#!/usr/bin/env python3

"""
The idea here is to run existing constraint test binaries and capture the 
output of the .scp files, along with some metadata, into structured reports.
Sounds easy, right? Follow me ...
"""

from __future__ import annotations

import argparse
import csv
import os
import re
import shutil
import stat
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple


CASE_LINE_RE = re.compile(r"with proofs:")
EXPECTING_RE = re.compile(r"\s+expecting\s+(\d+)\s+solutions\s*$")
VERIPB_RESULT_RE = re.compile(r"^s (VERIFIED SATISFIABLE|VERIFIED UNSATISFIABLE).*$")


@dataclass
class Snapshot:
    seq: int
    source_name: str
    path: Path
    captured_ns: int

@dataclass
class CaseRow:
    constraint_type: str
    configuration: str
    expected_solutions: Optional[int] = None
    proof_result: Optional[str] = None

@dataclass
class CaseEvent:
    seq: int
    seen_ns: int
    row: CaseRow


def is_executable_file(p: Path) -> bool:
    if not p.is_file():
        return False
    mode = p.stat().st_mode
    return bool(mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH))


def discover_test_binaries(build_dir: Path) -> List[Path]:
    bin_dir = build_dir / ""
    if not bin_dir.exists():
        return []
    candidates = sorted(p for p in bin_dir.iterdir() if is_executable_file(p) and p.name.endswith("_test"))
    return candidates

def parse_case_line(line: str) -> Optional[CaseRow]:
    # E.g. "plus (2,5) (1,6) (1,12)  with proofs: expecting 8 solutions"
    # Meh. Handle multi-word constraint names and configurations that may start
    # with (, [, a positive number, or a negative number. Getting messy.
    # Oh lordy.  I also need to account for e.g. "element 2d constant"
    if "with proofs:" not in line:
        return None

    s = line.strip()

    expected_solutions: Optional[int] = None
    m_exp = EXPECTING_RE.search(s)
    if m_exp:
        expected_solutions = int(m_exp.group(1))

    s = EXPECTING_RE.sub("", s)
    s = s.replace("with proofs:", "").strip()
    if not s:
        return None

    # Find the first delimiter that looks like the start of parameters:
    #   (tuple/list), [domain], integer, or negative integer
    # Have some delicious regex with extra lookahead to make it even less readable
    # m = re.search(r"\s(?=(?:\(|\[|-?\d))", s)
    m = re.search(r"\s(?=(?:\(|\[|-?(?!2d\b)\d))", s)
    if m is None:
        constraint_type = s.strip()
        configuration = ""
    else:
        split_at = m.start()
        constraint_type = s[:split_at].strip()
        configuration = s[split_at:].strip()

    return CaseRow(
        constraint_type=constraint_type,
        configuration=configuration,
        expected_solutions=expected_solutions,
    )


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def extract_s_expression_encoding(scp_file: Path) -> str:
    # capture lines that look like constraint records e.g.: "(c1 ...)", "(c2 ...)", etc.
    # This assumes that constraint names start with 'c' followed by digits, which is true for the current implementation.
    # fallback: flattened full file.  JUST GRAB IT ALL FOR NOW
    scp = scp_file.read_text(encoding="utf-8", errors="replace")
    # t = scp.strip()
    # if re.match(r"^\(c\d+\b", t):
    #     t = re.sub(r"\s+", " ", t)
    return normalize_ws(scp)


def monitor_scp_files(
    run_dir: Path,
    snapshots_dir: Path,
    proc: subprocess.Popen,
    process_start_ns: int,
) -> List[Snapshot]:
    snapshots: List[Snapshot] = []
    mtimes: Dict[Path, int] = {}
    seq = 0

    def scan_once() -> None:
        nonlocal seq
        for scp in sorted(run_dir.glob("*.scp")):
            try:
                st = scp.stat()
                mtime_ns = st.st_mtime_ns
            except FileNotFoundError:
                continue

            if mtime_ns < process_start_ns:
                continue

            prev = mtimes.get(scp)
            if prev is None or mtime_ns > prev:
                mtimes[scp] = mtime_ns
                seq += 1
                out_name = f"{seq:04d}_{scp.name}"
                out_path = snapshots_dir / out_name
                try:
                    shutil.copy2(scp, out_path)
                except FileNotFoundError:
                    continue
                snapshots.append(
                    Snapshot(
                        seq=seq,
                        source_name=scp.name,
                        path=out_path,
                        captured_ns=time.monotonic_ns(),
                    )
                )

    while proc.poll() is None:
        scan_once()
        time.sleep(0.05)

    for _ in range(3):
        scan_once()
        time.sleep(0.02)

    return snapshots


def capture_latest_scp(
    run_dir: Path, 
    snapshots_dir: Path, 
    seq: int
) -> Optional[Snapshot]:
    candidates: List[Tuple[int, Path]] = []

    for scp in sorted(run_dir.glob("*.scp")):
        try:
            mtime_ns = scp.stat().st_mtime_ns
        except FileNotFoundError:
            continue
        candidates.append((mtime_ns, scp))

    if not candidates:
        return None

    _, scp = max(candidates, key=lambda t: (t[0], t[1].name))
    out_name = f"{seq:04d}_{scp.name}"
    out_path = snapshots_dir / out_name
    shutil.copy2(scp, out_path)

    return Snapshot(
        seq=seq,
        source_name=scp.name,
        path=out_path,
        captured_ns=time.monotonic_ns(),
    )


def assign_snapshots_to_cases(
    cases: List[CaseEvent],
    snapshots: List[Snapshot],
) -> Tuple[List[Tuple[CaseEvent, Snapshot]], List[str]]:
    if not cases:
        return [], ["no proof case lines were captured"]
    if not snapshots:
        return [], ["no scp snapshots were captured"]

    cases = sorted(cases, key=lambda c: c.seen_ns)
    snapshots = sorted(snapshots, key=lambda s: s.captured_ns)

    buckets: List[List[Snapshot]] = [[] for _ in cases]
    case_ix = 0

    for snap in snapshots:
        while case_ix + 1 < len(cases) and cases[case_ix + 1].seen_ns <= snap.captured_ns:
            case_ix += 1
        buckets[case_ix].append(snap)

    pairs: List[Tuple[CaseEvent, Snapshot]] = []
    warnings: List[str] = []

    for case, bucket in zip(cases, buckets):
        if not bucket:
            warnings.append(
                f"case {case.seq}: no scp captured for "
                f"{case.row.constraint_type} {case.row.configuration}"
            )
            continue

        if len(bucket) > 1:
            warnings.append(
                f"case {case.seq}: captured {len(bucket)} scp files for "
                f"{case.row.constraint_type} {case.row.configuration}; using the last one"
            )

        pairs.append((case, bucket[-1]))

    return pairs, warnings


def run_one_test(
    test_bin: Path,
    out_root: Path,
    args: Optional[List[str]] = None,
    timeout_sec: int = 0
) -> Tuple[List[CaseEvent], List[Snapshot], int]:
    test_name = test_bin.name
    run_label="_".join(args) if args else None
    subdir = f"{test_name}_{run_label}" if run_label else test_name
    test_out = out_root / subdir
    run_dir = test_out / "run"
    snapshots_dir = test_out / "snapshots"

    if run_dir.exists():
        shutil.rmtree(run_dir)
    if snapshots_dir.exists():
        shutil.rmtree(snapshots_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    snapshots_dir.mkdir(parents=True, exist_ok=True)

    stdout_log = test_out / "stdout.log"
    stderr_log = test_out / "stderr.log"

    cmd = [str(test_bin)] + (args if args is not None else [])
    proc = subprocess.Popen(
        cmd,
        cwd=run_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=1,
    )

    stdout_lines: List[str] = []
    stderr_lines: List[str] = []
    case_events: List[CaseEvent] = []
    snapshots: List[Snapshot] = []
    lock = threading.Lock()

    def drain(stream, sink: List[str], log_path: Path, capture_cases: bool = False) -> None:
        with log_path.open("w", encoding="utf-8") as f:
            for raw_line in stream:
                line = raw_line.rstrip("\n")
                sink.append(line)
                f.write(raw_line)

                if capture_cases:
                    if CASE_LINE_RE.search(line):
                        parsed = parse_case_line(line)
                        if parsed is not None:
                            with lock:
                                if case_events:
                                    snap = capture_latest_scp(run_dir, snapshots_dir, len(snapshots) + 1)
                                    if snap is not None:
                                        snapshots.append(snap)

                                case_events.append(
                                    CaseEvent(
                                        seq=len(case_events) + 1,
                                        seen_ns=time.monotonic_ns(),
                                        row=parsed,
                                    )
                                )

                m_vpb = VERIPB_RESULT_RE.match(line)
                if m_vpb:
                    with lock:
                        if case_events:
                            case_events[-1].row.proof_result = m_vpb.group(1)

    t_out = threading.Thread(target=drain, args=(proc.stdout, stdout_lines, stdout_log), daemon=True)
    t_err = threading.Thread(target=drain, args=(proc.stderr, stderr_lines, stderr_log, True), daemon=True)
    t_out.start()
    t_err.start()

    try:
        if timeout_sec > 0:
            rc = proc.wait(timeout=timeout_sec)
        else:
            rc = proc.wait()
    except subprocess.TimeoutExpired:
        proc.kill()
        rc = 124

    t_out.join(timeout=1.0)
    t_err.join(timeout=1.0)

    with lock:
        if case_events and len(snapshots) < len(case_events):
            snap = capture_latest_scp(run_dir, snapshots_dir, len(snapshots) + 1)
            if snap is not None:
                snapshots.append(snap)

    return case_events, snapshots, rc


def write_reports(
    out_root: Path,
    rows_minimal: List[Tuple],
    rows_debug: List[Tuple],
) -> None:
    tsv_min = out_root / "scp_summary.tsv"
    csv_min = out_root / "scp_summary.csv"
    tsv_dbg = out_root / "scp_summary_debug.tsv"

    min_headers = [
        "Constraint type",
        "configuration/parameters",
        "s-expression encoding",
        "expected solutions",
        "proof result",
        "valid encoding",
    ]

    with tsv_min.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f, delimiter="\t")
        w.writerow(min_headers)
        for r in rows_minimal:
            w.writerow(r)

    with csv_min.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(min_headers)
        for r in rows_minimal:
            w.writerow(r)

    with tsv_dbg.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f, delimiter="\t")
        w.writerow(
            [
                "Constraint type",
                "configuration/parameters",
                "s-expression encoding",
                "expected solutions",
                "proof result",
                "valid encoding",
                "test_binary",
                "source_scp_name",
                "case_index",
                "snapshot_path",
            ]
        )
        for r in rows_debug:
            w.writerow(r)

            
def is_valid_encoding(enc) -> bool:
    # Use a stack to check for balanced brackets
    stack = []
    for char in enc:
        if char == '(':
            stack.append(char)
        elif char == ')':
            if not stack:
                return False
            stack.pop()
    return not stack


def main() -> int:

    build_dir = Path('./build').resolve()
    out_dir = Path('./build/scp_capture').resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    test_bins = discover_test_binaries(build_dir)
    # if args.name_filter:
    #     test_bins = [p for p in test_bins if args.name_filter in p.name]

    if not test_bins:
        print(f"No *_test binaries found under {build_dir}", file=sys.stderr)
        return 2

    rows_minimal: List[Tuple] = []
    rows_debug: List[Tuple] = []
    warnings: List[str] = []
    failures: List[str] = []

    for test_bin in test_bins:
        print(f"Running {test_bin.name} ...")

        if "linear_test" in test_bin.name:
            arg_sets = [["le"], ["eq"], ["ne"], ["ge"]]
        elif "comparison_test" in test_bin.name:
            arg_sets = [["lt"], ["lt_if"], ["lt_iff"],
                        ["le"], ["le_if"], ["le_iff"],
                        ["ge"], ["ge_if"], ["ge_iff"],
                        ["gt"], ["gt_if"], ["gt_iff"]]
        elif "element_test" in test_bin.name:
            arg_sets = [["var"], ["var2d"], ["const"], ["const2d"]]
        elif "smart_table_test" in test_bin.name:
            arg_sets = [["lex_gt"], ["lex_ge"], ["lex_lt"], ["lex_le"], 
                        ["lex_gt_fixed"], ["lex_ge_fixed"], ["lex_lt_fixed"], ["lex_le_fixed"], 
                        ["am1_eq"], ["am1_in_set"], ["al1_eq"],["al1_in_set"]]
        else:
            arg_sets = [[]]

        for args in arg_sets:
            label = f"{test_bin.name}" + (f" [{' '.join(args)}]" if args else "")
            if args:
                print(f"  Adding args for {test_bin.name}: {args}")

            case_events, snaps, rc = run_one_test(test_bin, out_dir, args, timeout_sec=0)

            if rc != 0:
                failures.append(f"{label} exited with {rc}")

            pairs, pair_warnings = assign_snapshots_to_cases(case_events, snaps)
            warnings.extend(f"{label}: {w}" for w in pair_warnings)

            for case_event, snap in pairs:
                c = case_event.row
                enc = extract_s_expression_encoding(snap.path)
                valid = is_valid_encoding(enc)
                rows_minimal.append((
                    c.constraint_type,
                    c.configuration,
                    enc,
                    c.expected_solutions,
                    c.proof_result,
                    valid,
                ))
                rows_debug.append((
                    c.constraint_type,
                    c.configuration,
                    enc,
                    c.expected_solutions,
                    c.proof_result,
                    valid,
                    label,
                    snap.source_name,
                    case_event.seq,
                    str(snap.path),
                ))

    write_reports(out_dir, rows_minimal, rows_debug)

    if warnings:
        (out_dir / "warnings.log").write_text("\n".join(warnings) + "\n", encoding="utf-8")
        print(f"Wrote warnings: {out_dir / 'warnings.log'}")

    if failures:
        (out_dir / "failures.log").write_text("\n".join(failures) + "\n", encoding="utf-8")
        print(f"Wrote failures: {out_dir / 'failures.log'}")
        return 1

    print(f"Wrote: {out_dir / 'scp_summary.tsv'}")
    print(f"Wrote: {out_dir / 'scp_summary.csv'}")
    print(f"Wrote: {out_dir / 'scp_summary_debug.tsv'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

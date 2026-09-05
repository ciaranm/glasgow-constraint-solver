#!/usr/bin/env python3
"""One sweep harness for the Cumulative and Disjunctive propagation rules.

Replaces a family of per-issue scripts that each hardcoded their own arm list
and answered one question. What made them proliferate is that measuring a
scheduling rule needs four things at once --- an arm to switch it on, an
instance family it actually fires on, a search-shape number and a proof number
--- and each script had two of the four.

Two modes:

  shape   solve and record search shape *and* the per-rule counters. One pass:
          the counters are inert (they change no inference and no proof byte),
          so unlike the STATS=0 / STATS=1 split this replaces, a counter run and
          a timing run are the same run.

  prove   solve with --prove, then run veripb, and record proof size and
          verification time.

Four instance sources --- a directory of MiniZinc .dzn RCPSP data, job shops,
multi-mode .mm files, and the generator --- because no single family exercises
the whole rule set. Every RCPSP collection in circulation has capacities of
three and up, so none of them posts a Disjunctive at all; none has a variable
duration, so none exercises the variable-argument accounting.

Arms are a table, one line each, so adding a rule is adding a line. Arms whose
flags this binary does not have are skipped and *said to be skipped*, which is
what makes it safe to point at an older build or at one built before half the
stack merged.

Examples:

    tools/scheduling_sweep.py --list-arms
    tools/scheduling_sweep.py --binary build/rcpsp --out shape.jsonl \\
        --dzn-dir ~/mzn-bench/rcpsp --collections data_bl,data_pack \\
        --arms ef,ttef,energetic,nfnl --timeout 60 --jobs 8
    tools/scheduling_sweep.py --binary build/rcpsp --out proofs.jsonl \\
        --mode prove --generated 'size=10,12;seed=1..10;capacity=3,4' \\
        --arms ef,ttef --proof-cap-mb 4000
    tools/scheduling_sweep.py ... --print-jobs > jobs.txt   # for a cluster

See dev_docs/rule-counters.md for what the counter columns mean, and
tools/README.md for the traps.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

# --- the arm table ---------------------------------------------------------
#
# name -> flags. An arm is a *configuration of the solver*, not a rule: several
# name a rule plus the strengthening that replaces its detection, because that
# is how the flags work and how a row has to be read.
#
# The disjunctive arms carry --unary/--machine themselves. Without them nothing
# posts a Disjunctive at all on a file-read instance, and the arm would measure
# an unchanged model very convincingly.

ARMS: dict[str, list[str]] = {
    # Cumulative. The baseline is time-tabling plus the overload check, both on
    # by default; "off" therefore means "no energetic rule", not "no rules".
    "off": [],
    "elastic": ["--cumulative-elastic-overload"],
    "kaoc": ["--cumulative-knapsack-overload"],
    "ef": ["--cumulative-edge-finding"],
    "ttef": ["--cumulative-time-table-edge-finding"],
    "energetic": ["--cumulative-energetic-edge-finding"],
    "nfnl": ["--cumulative-not-first-not-last"],
    "nfnlpub": ["--cumulative-not-first-not-last-published"],
    "ttef+nfnl": ["--cumulative-time-table-edge-finding", "--cumulative-not-first-not-last"],
    "ttef+nfnlpub": ["--cumulative-time-table-edge-finding", "--cumulative-not-first-not-last-published"],
    "energetic+nfnl": ["--cumulative-energetic-edge-finding", "--cumulative-not-first-not-last"],

    # Disjunctive. Every one of these needs a unary resource to exist.
    "dj-off": ["--unary", "disjunctive", "--machine", "disjunctive"],
    "dj-ef": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-edge-finding"],
    "dj-ef-lb": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-edge-finding",
                 "--disjunctive-edge-finding-lb-only"],
    "dj-ef-ub": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-edge-finding",
                 "--disjunctive-edge-finding-ub-only"],
    "dj-nfnl": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-not-first-not-last"],
    "dj-nfnlpub": ["--unary", "disjunctive", "--machine", "disjunctive",
                   "--disjunctive-not-first-not-last-published"],
    "dj-dps": ["--unary", "disjunctive", "--machine", "disjunctive",
               "--disjunctive-detectable-precedences-set"],
    "dj-overload": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-overload"],
    "dj-overload-ti": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-overload",
                       "--disjunctive-overload-certificate", "time-indexed"],
    "dj-overload-sn": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-overload",
                       "--disjunctive-overload-certificate", "sorting-network"],
    "dj-ef+nfnl": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-edge-finding",
                   "--disjunctive-not-first-not-last"],
    "dj-ef+dps": ["--unary", "disjunctive", "--machine", "disjunctive", "--disjunctive-edge-finding",
                  "--disjunctive-detectable-precedences-set"],
}

COUNTER_LINE = re.compile(r"^(cumulative|disjunctive)_([a-z_]+): "
                          r"calls=(\d+) firings=(\d+) already_true=(\d+) contradictions=(\d+)\s*$")
STAT_LINE = re.compile(r"^([a-z_ ]+): (.*)$")

# Whole-solve fields worth keeping from --stats, in the order rcpsp prints them.
WANTED_STATS = ["status", "makespan", "recursions", "propagations", "wall_time_s",
                "solutions", "critical path", "horizon"]


def binary_flags(binary: str) -> set[str]:
    """Every long option this binary's help mentions."""
    try:
        out = subprocess.run([binary, "--help"], capture_output=True, text=True, timeout=60).stdout
    except (OSError, subprocess.SubprocessError) as e:
        sys.exit(f"could not run {binary} --help: {e}")
    return set(re.findall(r"--[a-z0-9-]+", out))


def usable_arms(names: list[str], have: set[str]) -> tuple[list[str], dict[str, list[str]]]:
    """Split the requested arms into the ones this binary can run and the rest.

    Skipping is reported rather than silent: an arm quietly dropped looks
    exactly like an arm that made no difference.
    """
    ok, skipped = [], {}
    for name in names:
        missing = [f for f in ARMS[name] if f.startswith("--") and f not in have]
        if missing:
            skipped[name] = missing
        else:
            ok.append(name)
    return ok, skipped


def instance_jobs(args) -> list[tuple[str, str, list[str]]]:
    """(source, label, flags naming the instance)."""
    jobs: list[tuple[str, str, list[str]]] = []

    if args.dzn_dir:
        root = Path(args.dzn_dir).expanduser()
        colls = args.collections.split(",") if args.collections else [d.name for d in root.iterdir() if d.is_dir()]
        for coll in colls:
            for f in sorted((root / coll).glob("*.dzn")):
                jobs.append(("dzn", f"{coll}/{f.stem}", ["--dzn", str(f)]))

    for flag, source, pattern in (("--jss", "jss", "*.jss"), ("--mm", "mm", "*.mm")):
        d = getattr(args, f"{source}_dir")
        if not d:
            continue
        # An instance source is a flag too, and a binary built before the reader
        # landed would fail every run of it with the same unhelpful message.
        if flag not in args.have:
            print(f"skipping --{source}-dir: this binary has no {flag}", file=sys.stderr)
            continue
        for f in sorted(Path(d).expanduser().rglob(pattern)):
            jobs.append((source, f.stem, [flag, str(f)]))

    if args.generated:
        grid: dict[str, list[str]] = {}
        for part in args.generated.split(";"):
            if not part.strip():
                continue
            key, _, spec = part.partition("=")
            values: list[str] = []
            for piece in spec.split(","):
                if ".." in piece:
                    lo, _, hi = piece.partition("..")
                    values += [str(v) for v in range(int(lo), int(hi) + 1)]
                else:
                    values.append(piece)
            grid[key.strip()] = values
        keys = sorted(grid)

        def expand(at: int, chosen: list[tuple[str, str]]) -> None:
            if at == len(keys):
                label = " ".join(f"{k}={v}" for k, v in chosen)
                flags: list[str] = []
                for k, v in chosen:
                    flags += [f"--{k}", v]
                jobs.append(("generated", label, flags))
                return
            for v in grid[keys[at]]:
                expand(at + 1, chosen + [(keys[at], v)])

        expand(0, [])

    return jobs


def parse_output(text: str) -> tuple[dict, dict]:
    stats: dict[str, str] = {}
    rules: dict[str, dict[str, int]] = {}
    for line in text.splitlines():
        m = COUNTER_LINE.match(line)
        if m:
            which, rule, calls, firings, already, contra = m.groups()
            rules[f"{which}_{rule}"] = {"calls": int(calls), "firings": int(firings),
                                        "already_true": int(already), "contradictions": int(contra)}
            continue
        m = STAT_LINE.match(line)
        if m and m.group(1) in WANTED_STATS and m.group(1) not in stats:
            stats[m.group(1)] = m.group(2).strip()
    return stats, rules


def run_one(args, source: str, label: str, instance_flags: list[str], arm: str) -> dict:
    scratch = tempfile.mkdtemp(prefix="sweep-")
    row: dict = {"source": source, "instance": label, "arm": arm, "mode": args.mode,
                 "timeout_s": args.timeout, "parallel": 1 if args.serial else args.jobs}
    try:
        cmd = [os.path.abspath(args.binary), *instance_flags, *ARMS[arm], "--stats",
               "--timeout", str(args.timeout)]
        if args.mode == "prove":
            cmd += ["--prove", "--proof-files-basename", os.path.join(scratch, "p")]

        env = dict(os.environ, GCS_SCHEDULING_RULE_STATS="1")
        cap = args.proof_cap_mb * 1024 * 1024

        def limit() -> None:
            # A proof that runs away takes the disk with it: an uncapped rcpsp
            # --prove on a real Pack instance has written 128 GB in ten minutes.
            # The run dies with a write error and everything before the cap is
            # still readable, which is what makes this a cap and not a loss.
            if args.mode == "prove":
                resource.setrlimit(resource.RLIMIT_FSIZE, (cap, cap))
            os.setpgrp()

        started = time.monotonic()
        try:
            done = subprocess.run(cmd, capture_output=True, text=True, env=env,
                                  preexec_fn=limit, timeout=args.timeout * 6)
            row["solve_wall_s"] = round(time.monotonic() - started, 3)
            out = done.stdout + done.stderr
            row["exit"] = done.returncode
        except subprocess.TimeoutExpired:
            row["result"] = "harness-timeout"
            return row

        stats, rules = parse_output(out)
        row.update({k.replace(" ", "_"): v for k, v in stats.items()})
        if rules:
            row["rules"] = rules

        if args.mode == "prove":
            opb, pbp = Path(scratch, "p.opb"), Path(scratch, "p.pbp")

            # An incomplete proof is not a rejected one, and this is the whole
            # difference between a harness that reports a finding and one that
            # cries wolf. A run killed by the file-size cap leaves a truncated
            # .pbp behind, and a run that hit its own --timeout leaves one with
            # no conclusion: both are non-empty, both make veripb exit non-zero,
            # and neither says anything about the solver. Classify them from how
            # the run ended, and do not check them.
            if row.get("exit", 0) < 0:
                killed = -row["exit"]
                row["result"] = "proof-too-big" if killed == int(signal.SIGXFSZ) else f"killed-by-signal-{killed}"
                return row
            if stats.get("status") not in ("optimal", "infeasible", "unsatisfiable", "satisfiable-complete"):
                row["result"] = stats.get("status", "no-status")
                return row
            if not pbp.exists() or pbp.stat().st_size == 0:
                row["result"] = "no-proof"
                return row
            row["opb_bytes"] = opb.stat().st_size
            row["pbp_bytes"] = pbp.stat().st_size
            with pbp.open("rb") as fh:
                row["pbp_lines"] = sum(1 for _ in fh)
            started = time.monotonic()
            try:
                check = subprocess.run([args.veripb, str(opb), str(pbp)], capture_output=True,
                                       text=True, timeout=args.verify_timeout)
                row["verify_s"] = round(time.monotonic() - started, 3)
                # A checker that *died* did not reject anything, and this is the
                # same distinction the solver side makes a few lines up --- which
                # this half was missing. subprocess reports a signal death as a
                # negative return code, so an OOM kill, or someone else's
                # `pkill veripb` on a shared machine, used to land in the JSONL
                # as REJECTED: indistinguishable from an unsound proof, and the
                # most alarming thing this harness can say. Both happened.
                #
                # The tell is that a real rejection prints a multi-line
                # `Error: Checking error at ...`, where a killed one has said
                # nothing but its banner --- but that is a heuristic over the
                # captured text, and the return code is not. Record it either
                # way, so a row can be re-read later rather than re-run.
                row["verify_rc"] = check.returncode
                if check.returncode < 0:
                    row["result"] = f"verify-killed-{-check.returncode}"
                elif check.returncode == 0:
                    row["result"] = "verified"
                else:
                    row["result"] = "REJECTED"
                if check.returncode != 0:
                    row["verify_says"] = (check.stdout + check.stderr).strip()[-400:]
            except subprocess.TimeoutExpired:
                row["verify_s"] = round(time.monotonic() - started, 3)
                row["result"] = "verify-timeout"
        elif row.get("exit") != 0:
            row["result"] = "solver-error"
        else:
            # A solve that ran out of time ran cleanly; saying "ok" for it would
            # be true of the process and misleading about the row. Anything
            # summing these has to filter on one field, so make it this one.
            row["result"] = stats.get("status", "ok") if stats.get("status") != "optimal" else "ok"
        return row
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--binary", default="build/rcpsp", help="the rcpsp example to sweep")
    p.add_argument("--out", help="JSONL output; appended to, and re-runnable (see --resume)")
    p.add_argument("--arms", help="comma-separated arm names; default every arm the binary supports")
    p.add_argument("--list-arms", action="store_true", help="print the arm table and what this binary supports")
    p.add_argument("--dzn-dir", help="directory of RCPSP .dzn collections")
    p.add_argument("--collections", help="comma-separated subdirectories of --dzn-dir")
    p.add_argument("--jss-dir", help="directory of job-shop instances (searched recursively)")
    p.add_argument("--mm-dir", help="directory of multi-mode .mm instances (searched recursively)")
    p.add_argument("--generated", help="generator grid, e.g. 'size=10,12;seed=1..10;capacity=3,4'")
    p.add_argument("--mode", choices=["shape", "prove"], default="shape")
    p.add_argument("--timeout", type=float, default=60.0, help="solver timeout in seconds")
    p.add_argument("--verify-timeout", type=float, default=3600.0)
    p.add_argument("--proof-cap-mb", type=int, default=4000, help="per-run proof file size cap")
    p.add_argument("--veripb", default="veripb")
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--serial", action="store_true",
                   help="one run at a time. Closed counts under a timeout are load-dependent, "
                        "so a table that reports them wants this; ratios over instances every arm "
                        "closed do not.")
    p.add_argument("--resume", action="store_true", help="skip rows already in --out")
    p.add_argument("--print-jobs", action="store_true",
                   help="print one command line per run instead of running them, for a cluster scheduler")
    args = p.parse_args()

    have = args.have = binary_flags(args.binary)
    requested = args.arms.split(",") if args.arms else list(ARMS)
    unknown = [a for a in requested if a not in ARMS]
    if unknown:
        sys.exit(f"unknown arm(s): {', '.join(unknown)}\nknown: {', '.join(ARMS)}")
    arms, skipped = usable_arms(requested, have)

    if args.list_arms:
        for name, flags in ARMS.items():
            mark = "  " if name in arms else ("--" if name in skipped else "  ")
            note = f"   [skipped: {' '.join(skipped[name])} not in this binary]" if name in skipped else ""
            print(f"{mark} {name:18s} {' '.join(flags) or '(defaults only)'}{note}")
        return 0

    if not args.out:
        sys.exit("--out is required unless --list-arms is given")
    for name, missing in skipped.items():
        print(f"skipping arm {name}: this binary has no {', '.join(missing)}", file=sys.stderr)
    if not arms:
        sys.exit("no requested arm is supported by this binary")

    jobs = instance_jobs(args)
    if not jobs:
        sys.exit("no instances: give at least one of --dzn-dir, --jss-dir, --mm-dir, --generated")

    done: set[tuple] = set()
    if args.resume and os.path.exists(args.out):
        with open(args.out) as fh:
            for line in fh:
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                done.add((r.get("source"), r.get("instance"), r.get("arm"), r.get("mode")))

    work = [(s, label, flags, arm) for (s, label, flags) in jobs for arm in arms
            if (s, label, arm, args.mode) not in done]
    print(f"{len(work)} runs ({len(jobs)} instances x {len(arms)} arms, {len(done)} already done)",
          file=sys.stderr)

    if args.print_jobs:
        for s, label, flags, arm in work:
            cmd = [os.path.abspath(args.binary), *flags, *ARMS[arm], "--stats", "--timeout", str(args.timeout)]
            print(f"GCS_SCHEDULING_RULE_STATS=1 {' '.join(shlex.quote(c) for c in cmd)}")
        return 0

    written = 0
    with open(args.out, "a", buffering=1) as fh:
        def emit(row: dict) -> None:
            nonlocal written
            fh.write(json.dumps(row) + "\n")
            written += 1

        if args.serial:
            for s, label, flags, arm in work:
                emit(run_one(args, s, label, flags, arm))
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
                futures = [pool.submit(run_one, args, s, label, flags, arm) for s, label, flags, arm in work]
                try:
                    for fut in concurrent.futures.as_completed(futures):
                        emit(fut.result())
                except KeyboardInterrupt:
                    for fut in futures:
                        fut.cancel()
                    raise

    print(f"wrote {written} rows to {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal.default_int_handler)
    sys.exit(main())

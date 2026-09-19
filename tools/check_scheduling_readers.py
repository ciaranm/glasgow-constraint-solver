#!/usr/bin/env python3
"""Pre-flight: does this build get the published answers?

Reading an instance format is easy to get subtly wrong in a way that no crash
and no test reveals --- a duration read into the wrong mode, a precedence
weighted by the wrong figure --- and the failure looks like a slightly better
optimum, which is exactly what nobody double-checks. Both of the bugs that
existed in the multi-mode support when it was written showed up only as a
makespan *below* the published one.

So before a long sweep, check the build against numbers other people published:

    tools/check_scheduling_readers.py --binary build/rcpsp \\
        --instances scheduling-instances

Multi-mode is compared against PSPLIB's own optimal-makespan table, which the
fetch script downloads alongside the instances. Job shop is compared against two
optima famous enough to hardcode. Anything that disagrees is a finding about
this build, not about the instance.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# ft06 and la01 from the Lawrence and Fisher-Thompson sets. Both are settled and
# have been for forty years; if this build disagrees, this build is wrong.
JOBSHOP_OPTIMA = {"ft06": 55, "la01": 666}

# The mode/instance columns are 1-based and a makespan of 16384 is the table's
# way of saying "no feasible schedule". PSPLIB ships no file for those, so they
# never come up here, but read the sentinel rather than trusting that.
INFEASIBLE = 16384


def solve(binary: str, flags: list[str], timeout: float) -> tuple[str, int | None]:
    out = subprocess.run([binary, *flags, "--stats", "--timeout", str(timeout)],
                         capture_output=True, text=True, timeout=timeout * 6).stdout
    status = re.search(r"^status: (\S+)$", out, re.M)
    makespan = re.search(r"^makespan: (\d+)$", out, re.M)
    return (status.group(1) if status else "?",
            int(makespan.group(1)) if makespan else None)


def check_jobshop(binary: str, root: Path, timeout: float) -> tuple[int, int, int]:
    agree = disagree = unresolved = 0
    for name, want in JOBSHOP_OPTIMA.items():
        found = list(root.rglob(f"{name}.jss"))
        if not found:
            print(f"  {name}: no instance file, skipped")
            continue
        # Edge-finding is off by default and a job shop is where that shows:
        # ft06 is 55 recursions with it and had not closed after 29.6 million
        # without. A pre-flight wants the configuration that finishes.
        status, got = solve(binary, ["--jss", str(found[0]), "--unary", "disjunctive",
                                     "--disjunctive-edge-finding",
                                     "--branch", "dom-then-deg", "--value-order", "split"], timeout)
        if status != "optimal":
            print(f"  {name}: {status} within {timeout:g}s, wanted {want}")
            unresolved += 1
        elif got == want:
            print(f"  {name}: {got} as published")
            agree += 1
        else:
            print(f"  {name}: got {got}, PUBLISHED OPTIMUM IS {want}  <-- disagreement")
            disagree += 1
    return agree, disagree, unresolved


def published_optima(opt_file: Path, prefix: str) -> dict[str, int]:
    table: dict[str, int] = {}
    for line in opt_file.read_text(errors="replace").splitlines():
        f = line.split()
        if len(f) >= 3 and f[0].isdigit() and f[1].isdigit():
            try:
                table[f"{prefix}{f[0]}_{f[1]}.mm"] = int(f[2])
            except ValueError:
                pass
    return table


def check_multimode(binary: str, root: Path, timeout: float, limit: int) -> tuple[int, int, int]:
    agree = disagree = unresolved = 0
    for opt_file in sorted(root.glob("*.opt")):
        setname = opt_file.stem
        table = published_optima(opt_file, setname)
        files = sorted((root / setname).rglob("*.mm"))[:limit]
        if not files:
            continue
        print(f"  {setname}: checking {len(files)} of {len(list((root / setname).rglob('*.mm')))}")
        for path in files:
            want = table.get(path.name)
            if want is None or want == INFEASIBLE:
                continue
            status, got = solve(binary, ["--mm", str(path)], timeout)
            if status != "optimal":
                unresolved += 1
            elif got == want:
                agree += 1
            else:
                disagree += 1
                print(f"    {path.name}: got {got}, published {want}  <-- disagreement")
    return agree, disagree, unresolved


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--binary", default="build/rcpsp")
    p.add_argument("--instances", default="scheduling-instances",
                   help="the directory tools/fetch_scheduling_instances.bash filled")
    p.add_argument("--timeout", type=float, default=30.0)
    p.add_argument("--limit", type=int, default=40, help="multi-mode instances per set")
    args = p.parse_args()

    root = Path(args.instances).expanduser()
    binary = str(Path(args.binary).expanduser().resolve())
    help_text = subprocess.run([binary, "--help"], capture_output=True, text=True).stdout

    total_disagree = total_unresolved = 0

    if "--jss" not in help_text:
        print("job shop: this binary has no --jss, skipping")
    elif not (root / "jobshop").is_dir():
        print("job shop: no instances fetched, skipping")
    else:
        print("job shop, against published optima:")
        a, d, u = check_jobshop(binary, root / "jobshop", args.timeout)
        total_disagree += d
        total_unresolved += u

    if "--mm" not in help_text:
        print("multi-mode: this binary has no --mm, skipping")
    elif not (root / "multimode").is_dir():
        print("multi-mode: no instances fetched, skipping")
    else:
        print("multi-mode, against PSPLIB's optimal-makespan table:")
        a, d, u = check_multimode(binary, root / "multimode", args.timeout, args.limit)
        total_disagree += d
        total_unresolved += u
        print(f"  {a} agree, {d} disagree, {u} unresolved within {args.timeout:g}s")

    print()
    if total_disagree:
        print(f"{total_disagree} DISAGREEMENTS. Do not sweep with this build: a makespan that "
              f"differs from a published optimum is a bug in the reader or the model, and every "
              f"number the sweep produces would inherit it.")
        return 1
    print("no disagreements with any published optimum.")
    if total_unresolved:
        print(f"{total_unresolved} did not resolve in {args.timeout:g}s, which is a statement "
              f"about the timeout rather than about the build; raise --timeout to shrink it.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

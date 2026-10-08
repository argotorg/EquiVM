#!/usr/bin/env python3
"""The finish checklist of Misc/prompt.md as one command.

Builds the capstone module, searches the working directory for `sorry`/`admit` and project
`axiom`s, prints the axiom footprint of the capstone theorem, and flags anything outside the
accepted trusted base.

Example:
  scripts/finish_check.py --dir Benchmarks/Dss/Pot --module Benchmarks.Dss.Pot \
      --theorem Benchmarks.Dss.Pot.potContractCorrect
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

ACCEPTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound", "Lean.ofReduceBool", "Lean.trustCompiler"}
ACCEPTED_PATTERNS = [re.compile(r".*\.native_decide\.ax_\d+$"), re.compile(r".*\._auxLemma\.\d+$")]


def run(args: list[str], timeout: int | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=False, timeout=timeout)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dir", type=Path, required=True, help="working directory of the proof")
    parser.add_argument("--module", required=True, help="Lean module path of the directory")
    parser.add_argument("--theorem", required=True, help="fully qualified capstone theorem")
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--allow-axiom", action="append", default=[],
                        help="additional accepted axiom names (repeatable)")
    args = parser.parse_args(argv)
    failures = 0

    if not args.skip_build:
        print(f"== lake build {args.module}.Correct", flush=True)
        build = run(["lake", "build", f"{args.module}.Correct"])
        tail = (build.stdout + build.stderr).strip().splitlines()[-15:]
        print("\n".join(tail))
        if build.returncode != 0:
            print("FAIL build")
            return 1
        print("ok   build")

    print(f"== sorry/admit in {args.dir}")
    hits = []
    for path in sorted(args.dir.rglob("*.lean")):
        for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            code = line.split("--", 1)[0]
            if re.search(r"\b(sorry|admit)\b", code):
                hits.append(f"{path}:{n}: {line.strip()}")
    if hits:
        failures += 1
        print("FAIL " + "\n     ".join(hits[:40]))
    else:
        print("ok   no sorry/admit")

    print(f"== project axioms in {args.dir}")
    axioms = []
    for path in sorted(args.dir.rglob("*.lean")):
        for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if re.match(r"^\s*axiom\s", line):
                axioms.append(f"{path}:{n}: {line.strip()}")
    if axioms:
        failures += 1
        print("FAIL " + "\n     ".join(axioms))
    else:
        print("ok   no axiom declarations")

    print(f"== #print axioms {args.theorem}")
    probe = f"import {args.module}.Correct\n#print axioms {args.theorem}\n"
    result = run(["lake", "env", "lean", "--stdin"], timeout=1800) if False else \
        subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, text=True, input=probe,
                       capture_output=True, check=False)
    out = result.stdout + result.stderr
    print(out.strip())
    m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    if result.returncode != 0 or not m:
        if "does not depend on any axioms" in out:
            print("ok   no axioms")
        else:
            print("FAIL could not read the axiom footprint")
            failures += 1
    else:
        names = [a.strip() for a in m.group(1).split(",") if a.strip()]
        accepted = ACCEPTED_AXIOMS | set(args.allow_axiom)
        bad = [a for a in names if a not in accepted and not any(p.match(a) for p in ACCEPTED_PATTERNS)]
        if bad:
            failures += 1
            print("FAIL axioms outside the accepted set: " + ", ".join(bad))
        else:
            print(f"ok   {len(names)} axioms, all accepted")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())

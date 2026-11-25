#!/usr/bin/env python3
"""Run the repository differential CLI with only Midnight registered locally."""
from pathlib import Path
import json
import os
import subprocess
import sys

directory = Path(__file__).resolve().parent
repo = directory.parents[1]
runner = directory / ".difftest"
runner.mkdir(exist_ok=True)
(runner / "lakefile.toml").write_text(
    'name = "MidnightDiff"\nversion = "0.1.0"\n'
    'packagesDir = ' + json.dumps(str(repo / ".lake/packages")) + '\n'
    '[[require]]\nname = "EquiVM"\npath = ' + json.dumps(str(repo)) + '\n'
    '[[lean_exe]]\nname = "stele-difftest"\nroot = "Main"\n')
(runner / "lean-toolchain").write_text((repo / "lean-toolchain").read_text())
main = (repo / "Tests/DiffTest/Main.lean").read_text()
main = main.replace("import Tests.DiffTest.Targets", "import Benchmarks.Midnight.DiffTarget")
main = main.replace("open Stele.DiffTest Tests.DiffTest",
                    "open Stele.DiffTest\n\ndef allTargets : List Target :=\n"
                    "  [Benchmarks.Midnight.diffTarget]")
(runner / "Main.lean").write_text(main)
manifest = json.loads((repo / "lake-manifest.json").read_text())
manifest["name"] = "MidnightDiff"
manifest["packagesDir"] = str(repo / ".lake/packages")
manifest["packages"].append(dict(type="path", name="EquiVM", dir=str(repo),
    manifestFile="lake-manifest.json", configFile="lakefile.toml", inherited=False))
(runner / "lake-manifest.json").write_text(json.dumps(manifest))
for name in ("EthereumTests", "Ethereum"):
    link = runner / name
    if not link.exists():
        link.symlink_to(repo / ".lake/packages/evmlean" / name, target_is_directory=True)
env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
raise SystemExit(subprocess.call(["lake", "exe", "stele-difftest", *sys.argv[1:]],
                                cwd=runner, env=env))

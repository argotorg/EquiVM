#!/usr/bin/env python3
"""Rebuild the compiler-upgraded benchmark while preserving the authored spec and fixtures."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

DIRECTORY = Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[2]
MODULE = "Benchmarks.Morpho.MetaMorphoV1_1"
VERSION = "0.8.37+commit.f401782d"
LINUX_SHA256 = "5de843c2c93563cc66425c99a4fb13fdbf32b4c4ae07469480faaf126e14404a"


def run(script, *args):
    subprocess.run([sys.executable, str(script), *map(str, args)], cwd=ROOT, check=True)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solc", type=Path, required=True)
    args = parser.parse_args()
    solc = args.solc.resolve()
    version = subprocess.check_output([str(solc), "--version"], text=True)
    if f"Version: {VERSION}." not in version:
        raise SystemExit(f"Expected solc {VERSION}, got {version.strip()}")
    binary_hash = digest(solc.read_bytes())
    if binary_hash != LINUX_SHA256:
        raise SystemExit("Expected the pinned official Linux amd64 solc binary")

    provenance = DIRECTORY / "provenance"
    authority = json.loads((provenance / "verification.standard-input.json").read_text())
    settings = {k: v for k, v in authority["settings"].items()
                if k != "outputSelection" and not (k == "libraries" and not v)}
    source_root = DIRECTORY / "compiler-sources"
    for unit, source in authority["sources"].items():
        content = source["content"]
        if (DIRECTORY.parent / "metamorpho-v1.1" / unit).read_text() != content:
            raise SystemExit(f"Source differs from pinned deployment input: {unit}")
        if unit == "src/MetaMorphoV1_1.sol":
            if content.count("pragma solidity 0.8.26;") != 1:
                raise SystemExit("Expected exactly one upstream compiler pragma")
            content = content.replace("pragma solidity 0.8.26;", "pragma solidity 0.8.37;")
        path = source_root / unit
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    scaffold = ROOT / "scripts/scaffold.py"
    run(scaffold, "compile", "--dir", DIRECTORY, "--solc", solc,
        "--sources-root", "compiler-sources", "--main", "src/MetaMorphoV1_1.sol",
        "--contract", "MetaMorphoV1_1", "--settings-json", json.dumps(settings))
    run(scaffold, "lean", "--dir", DIRECTORY, "--module", MODULE, "--force")
    run(scaffold, "blocks", "--dir", DIRECTORY, "--module", MODULE, "--force")
    run(ROOT / "scripts/bytecode_report.py", DIRECTORY,
        "--output", DIRECTORY / "MetaMorphoV1_1.report.md")
    run(DIRECTORY / "generate_skeleton.py", "--force")

    build = json.loads((DIRECTORY / "MetaMorphoV1_1.build.json").read_text())
    historical = json.loads((provenance / "deployment-solc-0.8.26-comparison.json").read_text())
    runtime = bytes.fromhex((DIRECTORY / "runtime.hex").read_text().strip())
    patched = bytearray(runtime)
    immutables = {}
    for imm in build["immutables"]:
        value = historical["immutables"][imm["name"]]["value"]
        word = int(value, 16).to_bytes(32, "big")
        for offset in imm["offsets"]:
            patched[offset:offset + 32] = word
        immutables[imm["name"]] = {
            "type": imm["type"], "value": value, "offsets": imm["offsets"]}
    deployed = bytes.fromhex((provenance / "deployed-runtime.hex").read_text().strip().removeprefix("0x"))
    comparison = {
        "chainId": historical["chainId"], "factory": historical["factory"],
        "vault": historical["vault"], "compiler": VERSION,
        "scope": "Compiler-upgraded local benchmark; historical deployment remains on solc 0.8.26.",
        "bytes": len(runtime), "deployedBytes": len(deployed),
        "equal": patched == deployed, "metadataIncluded": True,
        "runtimeSha256": digest(patched), "deployedRuntimeSha256": digest(deployed),
        "historicalComparison": "deployment-solc-0.8.26-comparison.json",
        "immutables": immutables,
    }
    (provenance / "deployment-comparison.json").write_text(json.dumps(comparison, indent=2) + "\n")
    compiler = {
        "version": VERSION, "platform": "linux-amd64", "sha256": binary_hash,
        "url": f"https://binaries.soliditylang.org/linux-amd64/solc-linux-amd64-v{VERSION}",
        "reason": "Avoid LostStorageArrayWriteOnSlotOverflow, fixed in solc 0.8.32.",
        "bugReference": "https://www.soliditylang.org/blog/2025/12/18/lost-storage-array-write-on-slot-overflow-bug/",
        "settingsAuthority": "verification.standard-input.json (compiler version overridden)",
        "sourcePatch": {"src/MetaMorphoV1_1.sol":
                        "pragma solidity 0.8.26; -> pragma solidity 0.8.37;"},
    }
    (provenance / "benchmark-compiler.json").write_text(json.dumps(compiler, indent=2) + "\n")
    run(scaffold, "check", "--dir", DIRECTORY)


if __name__ == "__main__":
    main()

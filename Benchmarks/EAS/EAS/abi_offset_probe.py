#!/usr/bin/env python3
"""Compile the ABI-offset investigation probes with the two pinned compilers.

Writes scratch artifacts only to --output. The Lean runner compares execution
across versions, code generation pipelines, and calldata/memory access paths.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


SOURCE = """// SPDX-License-Identifier: MIT
pragma solidity >=0.8.18 <0.9.0;
contract OffsetProbe {
    struct R { bytes32 schema; uint256[] data; }
    function direct(R[] calldata r) external pure returns (uint256) { return r[0].data.length; }
    function copied(R[] calldata r) external pure returns (uint256) { R memory x = r[0]; return x.data.length; }
    function memoryArg(R[] memory r) external pure returns (uint256) { return r[0].data.length; }
}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solc-0.8.18", dest="solc18", type=Path, required=True)
    parser.add_argument("--solc-0.8.32", dest="solc32", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    provenance = Path(__file__).resolve().parent / "provenance"
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "OffsetProbe.sol").write_text(SOURCE)
    manifest = []
    for compiler, release in [
        (args.solc18, "mainnet-compiler-release.json"),
        (args.solc32, "compiler-release.json"),
    ]:
        compiler = compiler.resolve()
        pinned = json.loads((provenance / release).read_text())
        digest = hashlib.sha256(compiler.read_bytes()).hexdigest()
        if digest != pinned["sha256"].removeprefix("0x"):
            raise SystemExit(f"compiler checksum mismatch: {compiler}")
        for via_ir in (True, False):
            name = pinned["version"] + ("-ir" if via_ir else "-legacy")
            compile_input = {
                "language": "Solidity",
                "sources": {"OffsetProbe.sol": {"content": SOURCE}},
                "settings": {
                    "optimizer": {"enabled": True, "runs": 1_000_000},
                    "viaIR": via_ir,
                    "evmVersion": "paris",
                    "metadata": {"bytecodeHash": "none"},
                    "outputSelection": {
                        "*": {"*": ["evm.deployedBytecode.object", "evm.methodIdentifiers", "irOptimized"]}
                    },
                },
            }
            encoded = json.dumps(compile_input, indent=2)
            (args.output / f"{name}.input.json").write_text(encoded + "\n")
            result = subprocess.run(
                [str(compiler), "--standard-json"], input=encoded,
                text=True, capture_output=True, check=True,
            )
            output = json.loads(result.stdout)
            errors = [e for e in output.get("errors", []) if e["severity"] == "error"]
            if errors:
                raise SystemExit(json.dumps(errors, indent=2))
            artifact = output["contracts"]["OffsetProbe.sol"]["OffsetProbe"]
            runtime = bytes.fromhex(artifact["evm"]["deployedBytecode"]["object"])
            (args.output / f"{name}.bin").write_bytes(runtime)
            (args.output / f"{name}.yul").write_text(artifact["irOptimized"])
            manifest.append({
                "name": name,
                "compiler": pinned["longVersion"],
                "compilerSha256": digest,
                "settings": compile_input["settings"],
                "runtimeBytes": len(runtime),
                "runtimeSha256": hashlib.sha256(runtime).hexdigest(),
                "selectors": artifact["evm"]["methodIdentifiers"],
            })
            print(f"{name}: {len(runtime)} runtime bytes; compiler checksum verified")
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()

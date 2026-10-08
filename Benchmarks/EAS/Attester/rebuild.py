#!/usr/bin/env python3
"""Reproduce the pinned upstream Attester build. Use --write to refresh artifacts."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import textwrap

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[2]
sys.dont_write_bytecode = True
sys.path.insert(0, str(PROJECT / "scripts"))
from generate_rd_blocks import disassemble

SETTINGS = {
    "optimizer": {"enabled": True, "runs": 1000000},
    "evmVersion": "paris",
    "viaIR": False,
    "metadata": {"bytecodeHash": "none"},
}


def json_text(value):
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def byte_array(name, code):
    values = ", ".join(str(byte) for byte in code)
    return f"def {name} : ByteArray :=\n  ⟨#[\n" + textwrap.fill(
        values, width=96, initial_indent="    ", subsequent_indent="    "
    ) + "]⟩\n"


def jump_fact(name, code_name, code):
    # The compiler's metadata contains no JUMPDEST after the first undefined opcode.
    jumps = [ins.pc for ins in disassemble(code) if ins.opcode == 0x5B]
    values = ", ".join(f"⟨{pc}⟩" for pc in jumps)
    return (
        f"@[valid_jumps] theorem {name} :\n"
        f"    Ethereum.EVM.D_J {code_name} 0 = #[\n"
        + textwrap.fill(values, width=96, initial_indent="      ", subsequent_indent="      ")
        + "] := by\n  native_decide\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solc", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--output-json", type=Path, help="also retain complete compiler output")
    args = parser.parse_args()
    compiler = args.solc.resolve()
    version = subprocess.check_output([str(compiler), "--version"], text=True)
    if "0.8.26+commit.8a97fa7a" not in version:
        parser.error("expected Solidity 0.8.26+commit.8a97fa7a")
    sources = {}
    for path in sorted((ROOT / "contracts").rglob("*.sol")):
        key = path.relative_to(ROOT / "contracts").as_posix()
        if key == "Attester.sol":
            key = "contracts/Attester.sol"
        sources[key] = {"content": path.read_text()}
    settings = dict(SETTINGS, outputSelection={"*": {
        "*": ["abi", "storageLayout", "metadata", "evm.bytecode", "evm.deployedBytecode",
              "evm.methodIdentifiers", "evm.legacyAssembly"], "": ["ast"]}})
    result = subprocess.run([str(compiler), "--standard-json"],
        input=json.dumps({"language": "Solidity", "sources": sources, "settings": settings}),
        text=True, capture_output=True, check=True)
    output = json.loads(result.stdout)
    for diagnostic in output.get("errors", []):
        print(diagnostic["formattedMessage"], file=sys.stderr)
    if any(e["severity"] == "error" for e in output.get("errors", [])):
        return 1
    if args.output_json:
        args.output_json.write_text(json_text(output))
    contract = output["contracts"]["contracts/Attester.sol"]["Attester"]
    evm = contract["evm"]
    runtime = bytes.fromhex(evm["deployedBytecode"]["object"])
    creation = bytes.fromhex(evm["bytecode"]["object"])
    references = evm["deployedBytecode"]["immutableReferences"]
    assert len(references) == 1
    sites = next(iter(references.values()))
    assert all(s["length"] == 32 for s in sites)
    offsets = [s["start"] for s in sites]
    for offset in offsets:
        assert runtime[offset - 1] == 0x7F and runtime[offset:offset + 32] == bytes(32)
    artifacts = {
        "creation.hex": creation.hex() + "\n",
        "runtime.hex": runtime.hex() + "\n",
        "Attester.abi.json": json_text(contract["abi"]),
        "Attester.storage.json": json_text(contract["storageLayout"]),
        "Attester.sol.ast.json": json_text(output["sources"]["contracts/Attester.sol"]["ast"]),
        "Attester.compiler.json": json_text({
            "compiler": "0.8.26+commit.8a97fa7a", "settings": SETTINGS,
            "upstream": {"repository": "ethereum-attestation-service/eas-contracts-example",
                         "commit": "d2864b166a08f9b3f9314f8b302316d67f227462",
                         "branch": "master", "hardhat": "2.22.13", "eas-contracts": "1.7.1"},
            "methodIdentifiers": evm["methodIdentifiers"],
            "immutableReferences": references,
            "creation": {"bytes": len(creation), "sha256": hashlib.sha256(creation).hexdigest(),
                         "functionDebugData": evm["bytecode"]["functionDebugData"]},
            "runtime": {"bytes": len(runtime), "sha256": hashlib.sha256(runtime).hexdigest(),
                        "functionDebugData": evm["deployedBytecode"]["functionDebugData"]},
            "sourceSha256": {name: hashlib.sha256(s["content"].encode()).hexdigest()
                             for name, s in sources.items()},
        }),
    }
    artifacts["Bytecode.lean"] = '''import Benchmarks.EAS.Attester.Spec
import Ethereum.Semantics
import Reasoning.JumpDest

/-!
# EAS Attester: exact upstream-settings compiler artifacts

Generated by `rebuild.py` using solc 0.8.26+commit.8a97fa7a, optimizer enabled with
1,000,000 runs, Paris, legacy pipeline, and metadata.bytecodeHash = none.
Source: eas-contracts-example commit d2864b166a08f9b3f9314f8b302316d67f227462.
The runtime template's `_eas` sites are recorded in `Immutables.lean`.
-/

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.EAS.Attester

set_option maxRecDepth 2000000

''' + byte_array("attesterBytecode", runtime) + "\n" + jump_fact(
        "validJumps", "attesterBytecode", runtime) + "\n" + byte_array(
        "attesterCreationBytecode", creation) + "\n" + jump_fact(
        "validCreationJumps", "attesterCreationBytecode", creation) + "\nend Benchmarks.EAS.Attester\n"
    immutables = (ROOT / "Immutables.lean").read_text()
    artifacts["Immutables.lean"] = re.sub(
        r'\[\("_eas", \[[\d, ]+\]\)\]', f'[("_eas", {offsets})]', immutables)
    hash_inputs = {p.relative_to(ROOT).as_posix(): p.read_bytes()
                   for p in sorted((ROOT / "contracts").rglob("*.sol"))}
    hash_inputs.update({name: artifacts[name].encode() for name in artifacts
                       if name.endswith((".hex", ".json"))})
    artifacts["sources.sha256"] = "".join(
        f"{hashlib.sha256(data).hexdigest()}  {name}\n"
        for name, data in sorted(hash_inputs.items()))
    mismatches = []
    for name, text in artifacts.items():
        path = ROOT / name
        if args.write:
            path.write_text(text)
        elif not path.exists() or path.read_text() != text:
            mismatches.append(name)
    if mismatches:
        print("Artifact mismatches: " + ", ".join(mismatches), file=sys.stderr)
        return 1
    print(f"{'Wrote' if args.write else 'Verified'} {len(artifacts)} artifacts; "
          f"creation {len(creation)} bytes, runtime {len(runtime)} bytes; immutable sites {offsets}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

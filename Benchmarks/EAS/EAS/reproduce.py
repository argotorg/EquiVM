#!/usr/bin/env python3
"""Recompile EAS with Solidity 0.8.32 and regenerate the benchmark artifacts.

The user selected a newer compiler to avoid SOL-2025-1. runtime.hex is the
zero-immutable compiler template. runtime-reference.hex applies the original
mainnet constructor environment; it is deliberately different from mainnet code.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

DIRECTORY = Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[2]
SOURCES = DIRECTORY.parent / "eas-contracts"
MODULE = "Benchmarks.EAS.EAS"
sys.path.insert(0, str(ROOT / "scripts"))
import scaffold
from evm_tools import decode_source_map, keccak256


def read_json(name):
    return json.loads((DIRECTORY / name).read_text())


def run_script(name, *args):
    subprocess.run([sys.executable, str(ROOT / "scripts" / name), *map(str, args)],
                   cwd=ROOT, check=True)


def write_constructor_blocks(build, creation, runtime):
    """Summarize constructor instructions, keeping data in the full code term.

    The generic generator disassembles embedded runtime and trailing constants
    as well. In this artifact the final hash constant happens to decode as
    BLOCKHASH, exposing an unrelated gas-normalization generator failure.
    Solc's creation source map identifies the executable prefix independently.
    """
    rd = scaffold.rd
    instructions = rd.disassemble(creation)
    mapped = decode_source_map(build["sourceMap"]["creation"])
    separator = instructions[len(mapped)]
    assert separator.opcode == 0xFE
    runtime_start = separator.pc + 1
    assert creation[runtime_start:runtime_start + len(runtime)] == runtime
    code_term = f"{MODULE}.easCreationBytecode"
    units = rd.generate_unit_records(creation, "easCreation", code_term,
                                     False, False, 64, True, None, None, False)
    executable = []
    for unit in units:
        if unit.pcs:
            if unit.pcs[0] < runtime_start:
                assert unit.pcs[-1] < runtime_start
                executable.append(unit)
        else:
            boundary = re.search(r"boundary at pc (\d+):", unit.text)
            assert boundary is not None
            if int(boundary[1]) < runtime_start:
                executable.append(unit)
    paths = rd.write_outputs(DIRECTORY / "CreationBlocks.lean", "easCreation",
                             [f"{MODULE}.Bytecode"], executable, 20, True, code_term)
    print(f"wrote {len(paths)} creation summary shards for constructor PCs "
          f"0–{separator.pc - 1}; full {len(creation)}-byte artifact retained")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solc", help="recompile with this verified Solidity 0.8.32 binary")
    args = parser.parse_args()
    if args.solc:
        release = read_json("provenance/compiler-release.json")
        digest = hashlib.sha256(Path(args.solc).read_bytes()).hexdigest()
        assert digest == release["sha256"].removeprefix("0x"), "wrong solc binary"
        settings = read_json("provenance/benchmark-settings.json")
        run_script("scaffold.py", "compile", "--dir", DIRECTORY, "--solc", args.solc,
                   "--sources-root", SOURCES, "--main", "contracts/EAS.sol", "--contract", "EAS",
                   "--runs", 1000000, "--via-ir", "--evm-version", "paris",
                   "--metadata-hash", "none", "--all-sources",
                   "--settings-json", json.dumps(settings))

    deployment = read_json("provenance/upstream-deployment.json")
    verification = read_json("provenance/blockscout-verification.json")
    build = read_json("EAS.build.json")
    assert build["settings"]["viaIR"] is True
    assert build["compiler"]["version"].startswith("0.8.32+commit.ebbd65e5")
    template = bytes.fromhex((DIRECTORY / "runtime.hex").read_text().strip())
    deployed = bytes.fromhex(verification["deployed_bytecode"].removeprefix("0x"))
    creation = bytes.fromhex((DIRECTORY / "creation.hex").read_text().strip())
    if args.solc:
        request = {
            "language": "Solidity",
            "sources": {p.relative_to(SOURCES).as_posix(): {"content": p.read_text()}
                        for p in sorted(SOURCES.rglob("*.sol"))},
            "settings": {**build["settings"], "outputSelection": {
                "*": {"*": [*scaffold.OUTPUT_SELECTION, "irOptimized"], "": ["ast"]}}},
        }
        (DIRECTORY / "provenance/benchmark-input.json").write_text(json.dumps(request, indent=2) + "\n")
        result = subprocess.run([args.solc, "--standard-json"], input=json.dumps(request),
                                text=True, capture_output=True, check=True)
        output = json.loads(result.stdout)
        assert not [e for e in output.get("errors", []) if e.get("severity") == "error"]
        contract = output["contracts"]["contracts/EAS.sol"]["EAS"]
        assert bytes.fromhex(contract["evm"]["deployedBytecode"]["object"]) == template
        assert bytes.fromhex(contract["evm"]["bytecode"]["object"]) == creation
        (DIRECTORY / "EAS.optimized.yul").write_text(contract["irOptimized"] + "\n")
    registry = int(deployment["args"][0], 16)
    address = int(deployment["address"], 16)
    word = lambda n: n.to_bytes(32, "big")
    name_hash = keccak256(b"EAS")
    version_hash = keccak256(b"0.26")
    type_hash = keccak256(b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")
    values = {
        "_HASHED_NAME": name_hash,
        "_HASHED_VERSION": version_hash,
        "_TYPE_HASH": type_hash,
        "_CACHED_CHAIN_ID": word(1),
        "_CACHED_THIS": word(address),
        "_CACHED_DOMAIN_SEPARATOR": keccak256(type_hash + name_hash + version_hash + word(1) + word(address)),
        "_schemaRegistry": word(registry),
    }
    patched = bytearray(template)
    for immutable in build["immutables"]:
        value = values[immutable["name"]]
        for offset in immutable["offsets"]:
            assert template[offset:offset + 32] == bytes(32)
            patched[offset:offset + 32] = value
    assert bytes(patched) != deployed, "upgraded benchmark unexpectedly equals the old deployment"
    rpc = read_json("provenance/mainnet-rpc.json")
    assert deployed == bytes.fromhex(rpc["response"]["result"].removeprefix("0x"))
    (DIRECTORY / "runtime-template.hex").write_text(template.hex() + "\n")
    (DIRECTORY / "runtime-reference.hex").write_text(patched.hex() + "\n")
    comparison = {
        "target": "EAS v0.26 recompiled with Solidity 0.8.32",
        "referenceAddress": deployment["address"], "chainId": 1,
        "sourceCommit": "aefff5aea2b61b4d86f5af016bc51b6acf3685fc",
        "sourceChanges": "Exact-version pragma declarations only; see source-adjustments.json",
        "compiler": build["compiler"]["version"],
        "settings": build["settings"],
        "runtimeBytes": len(template),
        "runtimeSha256": hashlib.sha256(template).hexdigest(),
        "referenceRuntimeSha256": hashlib.sha256(patched).hexdigest(),
        "creationBytes": len(creation),
        "metadataTail": template[-12:].hex(),
        "runtimeByteExactWithMainnet": False,
        "compilerBugAvoided": "SOL-2025-1 (fixed in 0.8.32)",
        "immutablesDerivedFromConstructor": {k: "0x" + v.hex() for k, v in values.items()},
        "mainnetRuntimeBytes": len(deployed),
        "mainnetRuntimeSha256": hashlib.sha256(deployed).hexdigest(),
        "mainnetProvenance": "mainnet-comparison.json; original scaffold archived separately",
    }
    (DIRECTORY / "provenance/comparison.json").write_text(json.dumps(comparison, indent=2) + "\n")
    scaffold.write_hashes(DIRECTORY, "EAS", SOURCES)
    with (DIRECTORY / "sources.sha256").open("a") as hashes:
        for path in [DIRECTORY / "runtime-template.hex", DIRECTORY / "runtime-reference.hex",
                     DIRECTORY / "EAS.optimized.yul", *sorted((DIRECTORY / "provenance").iterdir())]:
            if not path.is_file():
                continue
            hashes.write(f"{scaffold.sha256_file(path)}  {scaffold.rel_to_root(path)}\n")
    for step in ("lean", "blocks", "check"):
        extra = ["--no-creation"] if step == "blocks" else []
        run_script("scaffold.py", step, "--dir", DIRECTORY, "--module", MODULE, "--force", *extra)
        if step == "blocks":
            write_constructor_blocks(build, creation, template)
            # The generator leaves excess shards when a new compiler emits fewer blocks.
            for stem in ("RuntimeBlocks", "CreationBlocks"):
                index = (DIRECTORY / f"{stem}.index").read_text().splitlines()
                current = {line.split("\t")[1].split(":")[0] for line in index if line.strip()}
                for path in DIRECTORY.glob(f"{stem}_*.lean"):
                    if path.name not in current:
                        path.unlink()
    print(f"ok   Solidity 0.8.32 runtime: {len(template)} bytes; mainnet differs as requested")


if __name__ == "__main__":
    main()

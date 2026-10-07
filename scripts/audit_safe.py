#!/usr/bin/env python3
"""Reproduce Safe artifacts and regenerate/check the proof-support inventory.

Usage: python3 scripts/audit_safe.py --solc /path/to/solc-0.8.35 [--write]
The compiler must be 0.8.35+commit.47b9dedd. This checks artifact provenance and
summary coverage; the separate Lean Audit target executes the semantic regressions.
Neither check proves the unfilled refinement obligations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

from bytecode_io import read_bytecode
from generate_rd_blocks import (
    disassemble, generate_unit_records, instruction_is_supported,
    strip_solidity_metadata, write_outputs,
)

ROOT = Path(__file__).resolve().parent.parent
SAFE = ROOT / "Benchmarks/Safe"
SOURCE = "Benchmarks/Safe/contracts/Safe.sol"
OPTIONS = ["--optimize", "--optimize-runs", "200", "--evm-version", "shanghai",
           "--metadata-hash", "none", "--base-path", "."]
FIELDS = "bin,bin-runtime,abi,storage-layout,srcmap-runtime,hashes,function-debug-runtime"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compare_or_write(path: Path, text: str, write: bool) -> None:
    if write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    elif not path.exists() or path.read_text(encoding="utf-8") != text:
        raise ValueError(f"stale generated artifact: {path.relative_to(ROOT)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solc", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    compiler = args.solc.resolve()
    version = subprocess.check_output([str(compiler), "--version"], text=True)
    if "0.8.35+commit.47b9dedd" not in version:
        raise ValueError(f"unexpected compiler version: {version}")
    run = subprocess.run([str(compiler), *OPTIONS, "--combined-json", FIELDS, SOURCE],
                         cwd=ROOT, text=True, capture_output=True, check=True)
    data = json.loads(run.stdout)
    artifact = data["contracts"][SOURCE + ":Safe"]
    runtime = read_bytecode(SAFE / "runtime.hex")
    creation = read_bytecode(SAFE / "creation.hex")
    assert bytes.fromhex(artifact["bin-runtime"]) == runtime, "runtime compilation mismatch"
    assert bytes.fromhex(artifact["bin"]) == creation, "creation compilation mismatch"
    assert read_bytecode(SAFE / "Bytecode.lean", "safeBytecode") == runtime
    assert read_bytecode(SAFE / "Bytecode.lean", "safeCreationBytecode") == creation
    assert artifact["abi"] == json.loads((SAFE / "Safe.abi.json").read_text())
    for row in (SAFE / "sources.sha256").read_text().splitlines():
        digest, name = row.split(None, 1)
        assert sha((ROOT / name).read_bytes()) == digest, f"source mismatch: {name}"
    spec = (SAFE / "Spec.lean").read_text()
    transitions = set(re.findall(r"^def (\w+Transition) : TransitionDecl", spec, re.MULTILINE))
    transitions -= {"receiveTransition", "fallbackTransition"}
    scaffold = (SAFE / "Runtime.lean").read_text()
    scaffold_transitions = set(re.findall(r"hdispatch : selectorDispatchMsg contract I.calldata =\s+"
                                        r"some (\w+Transition)", scaffold))
    assert len(transitions) == 31 and scaffold_transitions == transitions
    assert "theorem safeReceiveRefines" in scaffold and "theorem safeFallbackRefines" in scaffold

    source_by_id = {i: (path, (ROOT / path).read_bytes())
                    for i, path in enumerate(data["sourceList"])}
    source_map = {}
    previous = ["0", "0", "-1", "", ""]
    for ins, entry in zip(disassemble(runtime), artifact["srcmap-runtime"].split(";")):
        parts = entry.split(":")
        previous = [parts[i] if i < len(parts) and parts[i] else previous[i] for i in range(5)]
        start, length, file_id = map(int, previous[:3])
        if file_id in source_by_id:
            path, text = source_by_id[file_id]
            source_map[ins.pc] = {"file": path, "line": text[:start].count(b"\n") + 1,
                                 "text": text[start:start + length].decode("utf-8")}

    # A runtime selector arm is PUSH4 selector; EQ; PUSH2 entry; JUMPI.
    instructions = disassemble(strip_solidity_metadata(runtime))
    arms = {}
    for i in range(len(instructions) - 3):
        a, b, c, d = instructions[i:i + 4]
        if a.pc < 475 and (a.opcode, b.opcode, c.opcode, d.opcode) == (0x63, 0x14, 0x61, 0x57):
            arms[f"{a.argument:08x}"] = c.argument
    assert set(arms) == set(artifact["hashes"].values()), "ABI/dispatcher selector mismatch"

    units = generate_unit_records(runtime, "safeRuntime", "Benchmarks.Safe.safeBytecode")
    runtime_offset = len(creation) - len(runtime)
    assert runtime_offset == 33 and creation[runtime_offset:] == runtime
    # Generate against the full creation bytes; select only the executable constructor prelude.
    ctor_units = [u for u in generate_unit_records(
        creation, "safeCreation", "Benchmarks.Safe.safeCreationBytecode", creation_code=True)
        if u.pcs and max(u.pcs) < runtime_offset]
    unsupported = [ins for ins in instructions if not instruction_is_supported(ins)]
    covered = {pc for unit in units for pc in unit.pcs}
    assert covered | {ins.pc for ins in unsupported} == {ins.pc for ins in instructions}
    assert not covered & {ins.pc for ins in unsupported}
    ctor_covered = {pc for unit in ctor_units for pc in unit.pcs}
    assert ctor_covered == {ins.pc for ins in disassemble(creation[:runtime_offset])}

    with tempfile.TemporaryDirectory(prefix="safe-blocks-") as directory:
        destination = Path(directory)
        shards = write_outputs(destination / "Runtime.lean", "safeRuntime",
                               ["Benchmarks.Safe.Bytecode"], units, 20, code=runtime)
        ctor_files = write_outputs(destination / "Creation.lean", "safeCreation",
                                   ["Benchmarks.Safe.Bytecode"], ctor_units, None,
                                   creation_code=True, code_term="Benchmarks.Safe.safeCreationBytecode",
                                   code=creation)
        outputs = sorted(destination.iterdir())
        for path in outputs:
            compare_or_write(SAFE / "Blocks" / path.name, path.read_text(), args.write)
        existing = {p.name for p in (SAFE / "Blocks").iterdir() if p.suffix in {".lean", ".index"}}
        assert existing == {p.name for p in outputs}, "unexpected stale block shard(s)"
        imports = "".join("import Benchmarks.Safe.Blocks." + p.stem + "\n"
                          for p in ctor_files + shards)
        compare_or_write(SAFE / "Blocks.lean", imports, args.write)

    # ABI expectations originate from solc, and are checked against the actual Lean declarations.
    checks = ["import Benchmarks.Safe.Spec", "", "open Solm ABI Ethereum", "",
              "namespace Benchmarks.Safe", "", "-- Generated by scripts/audit_safe.py from solc's ABI.",
              "#guard transitions.length == 31", ""]
    for entry in artifact["abi"]:
        if entry["type"] != "function":
            continue
        signature = entry["name"] + "(" + ",".join(p["type"] for p in entry["inputs"]) + ")"
        returns = "[" + ", ".join(json.dumps(p["type"]) for p in entry["outputs"]) + "]"
        selector = ", ".join("0x" + artifact["hashes"][signature][i:i + 2] for i in range(0, 8, 2))
        checks += [f"#guard (transitions.find? (transitionSigStr · == {json.dumps(signature)})).map",
                   f"  (fun t ↦ t.returnType.map abiToSigStr) == some {returns}",
                   f"#guard (KEC {json.dumps(signature)}.toUTF8).extract 0 4 == ⟨#[{selector}]⟩", ""]
    checks += ["end Benchmarks.Safe", ""]
    compare_or_write(SAFE / "ArtifactChecks.lean", "\n".join(checks), args.write)

    friendly = {0x32: "ORIGIN", 0x3A: "GASPRICE", 0x3C: "EXTCODECOPY", 0xF4: "DELEGATECALL"}
    manifest = {
        "compiler": "0.8.35+commit.47b9dedd", "compiler_options": OPTIONS,
        "source": SOURCE,
        "artifacts": {name: {"file_sha256": sha((SAFE / name).read_bytes()),
                             "bytes_sha256": sha(code), "bytes": len(code)}
                      for name, code in [("runtime.hex", runtime), ("creation.hex", creation)]},
        "abi_file_sha256": sha((SAFE / "Safe.abi.json").read_bytes()),
        "sources_manifest_sha256": sha((SAFE / "sources.sha256").read_bytes()),
        "spec_sha256": sha((SAFE / "Spec.lean").read_bytes()),
        "syntax_spec_sha256": sha((SAFE / "SpecSyntax.lean").read_bytes()),
        "runtime_entrypoint_obligations": 33,
        "selectors": [{"signature": sig, "selector": sel, "entry_pc": arms[sel]}
                      for sig, sel in artifact["hashes"].items()],
        "storage_layout": artifact["storage-layout"],
        "function_entry_points": {k: v for k, v in artifact["function-debug-runtime"].items()
                                  if v.get("entryPoint") is not None},
        "runtime_instructions": len(instructions),
        "runtime_summarized_instructions": len(covered),
        "runtime_summary_theorems": sum(len(u.theorem_names) for u in units),
        "runtime_shards": len(shards),
        "creation_runtime_offset": runtime_offset,
        "creation_summarized_instructions": len(ctor_covered),
        "creation_summary_theorems": sum(len(u.theorem_names) for u in ctor_units),
        "boundaries": [{"pc": ins.pc, "opcode": friendly.get(ins.opcode, ins.name.upper()),
                        "source": source_map.get(ins.pc)} for ins in unsupported],
        "event_sites": [{"pc": ins.pc, "opcode": ins.name.upper(), "source": source_map.get(ins.pc)}
                        for ins in instructions if 0xA0 <= ins.opcode <= 0xA4],
        "scope": "Reproduction and instruction coverage only; refinement proofs remain unfilled.",
    }
    compare_or_write(SAFE / "AuditManifest.json", json.dumps(manifest, indent=2) + "\n", args.write)
    print(f"Safe artifacts reproduced; {len(arms)} ABI selectors; {len(covered)} summarized runtime "
          f"instructions and {len(unsupported)} explicit boundaries; {len(shards)} runtime shards.")


if __name__ == "__main__":
    main()

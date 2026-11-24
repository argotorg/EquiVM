#!/usr/bin/env python3
"""Reproduce Safe artifacts and regenerate/check the proof-support inventory.

Usage: python3 scripts/audit_safe.py --solc /path/to/solc-0.8.35 [--dir Benchmarks/Safe/Main] [--runs 200] [--via-ir] [--write]
`--dir` is the proof directory (default `Benchmarks/Safe/Main`); its path is the Lean module prefix.
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
    bytecode_imports, directory_listing, disassemble, generate_unit_records,
    instruction_is_supported, strip_solidity_metadata, write_outputs,
)

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DIR = "Benchmarks/Safe/Main"


def compiler_options(runs: int, via_ir: bool) -> list[str]:
    return (["--via-ir"] if via_ir else []) + [
        "--optimize", "--optimize-runs", str(runs), "--evm-version", "shanghai",
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
    parser.add_argument("--runs", type=int, default=200, help="solc --optimize-runs value of the proof's bytecode")
    parser.add_argument("--via-ir", action="store_true", help="the proof's bytecode was compiled with --via-ir")
    parser.add_argument("--dir", type=Path, default=Path(DEFAULT_DIR),
                        help="proof directory relative to the repository root (its path is the module prefix)")
    args = parser.parse_args()
    safe = (ROOT / args.dir).resolve()
    rel = safe.relative_to(ROOT)
    source = (rel / "contracts/Safe.sol").as_posix()
    if not (ROOT / source).is_file():
        raise SystemExit(f"no Safe source at {source}")
    module = ".".join(rel.parts)
    compiler = args.solc.resolve()
    options = compiler_options(args.runs, args.via_ir)
    version = subprocess.check_output([str(compiler), "--version"], text=True)
    if "0.8.35+commit.47b9dedd" not in version:
        raise ValueError(f"unexpected compiler version: {version}")
    run = subprocess.run([str(compiler), *options, "--combined-json", FIELDS, source],
                         cwd=ROOT, text=True, capture_output=True, check=True)
    data = json.loads(run.stdout)
    artifact = data["contracts"][source + ":Safe"]
    runtime = read_bytecode(safe / "runtime.hex")
    creation = read_bytecode(safe / "creation.hex")
    assert bytes.fromhex(artifact["bin-runtime"]) == runtime, "runtime compilation mismatch"
    assert bytes.fromhex(artifact["bin"]) == creation, "creation compilation mismatch"
    # The listings `Bytecode.lean` / `CreationBytecode.lean` (scripts/gen_listing.py) define the
    # bytecode constants from runtime.hex and creation.hex, pinned by their SHA-256 (checked here).
    assert read_bytecode(safe / "Bytecode.lean", "safeBytecode") == runtime
    assert read_bytecode(safe / "CreationBytecode.lean", "safeCreationBytecode") == creation
    assert artifact["abi"] == json.loads((safe / "Safe.abi.json").read_text())
    for row in (safe / "sources.sha256").read_text().splitlines():
        digest, name = row.split(None, 1)
        assert sha((ROOT / name).read_bytes()) == digest, f"source mismatch: {name}"
    spec = (safe / "Spec.lean").read_text()
    transitions = set(re.findall(r"^def (\w+Transition) : TransitionDecl", spec, re.MULTILINE))
    transitions -= {"receiveTransition", "fallbackTransition"}
    # Runtime.lean imports the 33 entrypoint modules; their statements carry the dispatch facts.
    entrypoints = re.findall(rf"^import {re.escape(module)}\.(\w+)$",
                             (safe / "Runtime.lean").read_text(), re.MULTILINE)
    scaffold = "".join((safe / f"{name}.lean").read_text() for name in entrypoints)
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

    # A runtime selector arm is PUSH4 selector; EQ; PUSH2 entry; JUMPI, with an ABI selector.
    instructions = disassemble(strip_solidity_metadata(runtime))
    selectors = set(artifact["hashes"].values())
    arms = {}
    for i in range(len(instructions) - 3):
        a, b, c, d = instructions[i:i + 4]
        if (a.opcode, b.opcode, c.opcode, d.opcode) == (0x63, 0x14, 0x61, 0x57):
            selector = f"{a.argument:08x}"
            if selector in selectors:
                assert selector not in arms, f"duplicate dispatcher arm for selector {selector}"
                arms[selector] = c.argument
    assert set(arms) == selectors, "ABI/dispatcher selector mismatch"

    # When the bytecode files are listings the summaries are runs over them.
    listing = directory_listing(safe, module, runtime)
    ctor_listing = directory_listing(safe, module, creation, creation=True)
    units = generate_unit_records(runtime, "safeRuntime", f"{module}.safeBytecode", listing=listing)
    runtime_offset = len(creation) - len(runtime)
    assert runtime_offset > 0 and creation[runtime_offset:] == runtime
    # Generate against the full creation bytes; select only the executable constructor prelude.
    ctor_units = [u for u in generate_unit_records(
        creation, "safeCreation", f"{module}.safeCreationBytecode", creation_code=True,
        listing=ctor_listing)
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
                               bytecode_imports(safe, module), units, 20, code=runtime,
                               max_rec_depth=10000 if args.via_ir else None,
                               namespace=f"{module}.RuntimeBlocks", listing=listing)
        ctor_files = write_outputs(destination / "Creation.lean", "safeCreation",
                                   bytecode_imports(safe, module, creation=True), ctor_units, None,
                                   creation_code=True, code_term=f"{module}.safeCreationBytecode",
                                   code=creation, namespace=f"{module}.CreationBlocks",
                                   listing=ctor_listing)
        outputs = sorted(destination.iterdir())
        for path in outputs:
            compare_or_write(safe / "Blocks" / path.name, path.read_text(), args.write)
        existing = {p.name for p in (safe / "Blocks").iterdir() if p.suffix in {".lean", ".index"}}
        assert existing == {p.name for p in outputs}, "unexpected stale block shard(s)"
        imports = "".join(f"import {module}.Blocks." + p.stem + "\n"
                          for p in ctor_files + shards)
        compare_or_write(safe / "Blocks.lean", imports, args.write)

    # ABI expectations originate from solc, and are checked against the actual Lean declarations.
    checks = [f"import {module}.Spec", "", "open Stele ABI Ethereum", "",
              f"namespace {module}", "", "-- Generated by scripts/audit_safe.py from solc's ABI.",
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
    checks += [f"end {module}", ""]
    compare_or_write(safe / "ArtifactChecks.lean", "\n".join(checks), args.write)

    friendly = {0x32: "ORIGIN", 0x3A: "GASPRICE", 0x3C: "EXTCODECOPY", 0xF4: "DELEGATECALL"}
    manifest = {
        "compiler": "0.8.35+commit.47b9dedd", "compiler_options": options,
        "source": source,
        "artifacts": {name: {"file_sha256": sha((safe / name).read_bytes()),
                             "bytes_sha256": sha(code), "bytes": len(code)}
                      for name, code in [("runtime.hex", runtime), ("creation.hex", creation)]},
        "abi_file_sha256": sha((safe / "Safe.abi.json").read_bytes()),
        "sources_manifest_sha256": sha((safe / "sources.sha256").read_bytes()),
        "spec_sha256": sha((safe / "Spec.lean").read_bytes()),
        "syntax_spec_sha256": sha((safe / "SpecSyntax.lean").read_bytes()),
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
    compare_or_write(safe / "AuditManifest.json", json.dumps(manifest, indent=2) + "\n", args.write)
    print(f"Safe artifacts reproduced; {len(arms)} ABI selectors; {len(covered)} summarized runtime "
          f"instructions and {len(unsupported)} explicit boundaries; {len(shards)} runtime shards.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Build a contract's proof scaffold from compiler artifacts.

Subcommands (``all`` runs them in order):

  compile   run solc (standard JSON), or Vyper 0.4.3 with --vyper, on the pinned sources:
            runtime.hex, creation.hex, <Name>.abi.json, <Name>.storage.json,
            sources.sha256 and <Name>.build.json (compiler settings, selectors, source maps,
            immutables). solc also writes <Name>.sol.ast.json, <Name>.metadata.json and the
            full source-unit AST; Vyper records its code layout and pc source-position map.
  lean      write Bytecode.lean and, with creation.hex, CreationBytecode.lean: the runtime and
            creation listings (scripts/gen_listing.py: a `listing_from_hex` command that decodes
            runtime.hex / creation.hex, pinned by its SHA-256, into a kernel-checked table of
            instructions when the file is built, defining <prefix>Bytecode /
            <prefix>CreationBytecode),
            Selectors.lean (selector table, selIs/selWord, keccak facts), and for contracts with
            immutables Immutables.lean and ImmutableCode.lean.  Existing files are kept unless
            --force.
  blocks    generate the proved block summaries RuntimeBlocks_NNN.lean / CreationBlocks_NNN.lean
            with scripts/generate_rd_blocks.py (immutable-aware when the contract has immutables),
            proved by runs over the listings when Bytecode.lean / CreationBytecode.lean are
            listings.
  check     verify that the listings (namespace, constant, hex file and its SHA-256, immutable
            layout), the selector table, immutable offsets and sources.sha256 agree with the
            artifacts.
  difftest  write DiffTarget.lean, the contract's entry for the differential suite
            (`lake exe stele-difftest --only <Name>`), and regenerate Tests/DiffTest/Generated.lean,
            the registry of every DiffTarget.lean in the repository.

Example:
  scripts/scaffold.py all --dir Benchmarks/Scaffolds/Foo --solc /tmp/solc-0.8.20 \
      --main contracts/Foo.sol --contract Foo --runs 200 --evm-version shanghai \
      --module Benchmarks.Scaffolds.Foo

  scripts/scaffold.py compile --dir Examples/VyperImmutable --vyper vyper \
      --main Immutable.vy --evm-version cancun
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import gen_listing
import generate_rd_blocks as rd
import bytecode_io
from bytecode_io import read_bytecode
from evm_tools import (abi_signatures, lean_name, overload_names, selector,
                       split_metadata, walk)

ROOT = Path(__file__).resolve().parent.parent

OUTPUT_SELECTION = [
    "abi", "metadata", "storageLayout",
    "evm.bytecode.object", "evm.bytecode.sourceMap", "evm.bytecode.generatedSources",
    "evm.deployedBytecode.object", "evm.deployedBytecode.sourceMap",
    "evm.deployedBytecode.immutableReferences", "evm.deployedBytecode.generatedSources",
    "evm.methodIdentifiers",
]


# --------------------------------------------------------------------------------------------
# Helpers

def lower_camel(name: str) -> str:
    """`CometRewards` → `cometRewards`, `WETH9` → `weth9`, `ERC20Token` → `erc20Token`."""
    name = re.sub(r"[^A-Za-z0-9_]", "_", name)
    m = re.match(r"[A-Z]+", name)
    if not m:
        return name
    run = m.group(0)
    rest = name[len(run):]
    if len(run) > 1 and rest[:1].islower():
        return run[:-1].lower() + run[-1] + rest
    return run.lower() + rest


def rel_to_root(path: Path, base: Path | None = None) -> str:
    """Path relative to the repository root, else to ``base``, else as given."""
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        if base is not None:
            try:
                return path.resolve().relative_to(base.resolve()).as_posix()
            except ValueError:
                pass
        return path.as_posix()


def default_module(directory: Path) -> str:
    rel = directory.resolve().relative_to(ROOT)
    return ".".join(rel.parts)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def find_build(directory: Path, contract: str | None) -> Path | None:
    if contract and (directory / f"{contract}.build.json").exists():
        return directory / f"{contract}.build.json"
    found = sorted(directory.glob("*.build.json"))
    return found[0] if found else None


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def contract_name(directory: Path, explicit: str | None) -> str:
    if explicit:
        return explicit
    build = find_build(directory, None)
    if build:
        return load_json(build)["contract"]
    abis = sorted(directory.glob("*.abi.json"))
    if len(abis) == 1:
        return abis[0].name[:-len(".abi.json")]
    raise SystemExit("cannot determine the contract name; pass --contract")


# --------------------------------------------------------------------------------------------
# compile

IMPORT_RE = re.compile(r'import\s+(?:[^;"\']*?\s+from\s+)?["\']([^"\']+)["\']\s*;')


def resolve_import(unit: str, target: str, remappings: list[str]) -> str:
    """Source unit name of `target` imported from `unit` (relative paths and remappings)."""
    for remap in remappings:
        if "=" in remap:
            prefix, replacement = remap.split("=", 1)
            if ":" in prefix:
                prefix = prefix.split(":", 1)[1]
            if target.startswith(prefix):
                target = replacement + target[len(prefix):]
                break
    if target.startswith("./") or target.startswith("../"):
        base = unit.rsplit("/", 1)[0] if "/" in unit else ""
        parts = (base.split("/") if base else [])
        for piece in target.split("/"):
            if piece == "..":
                if parts:
                    parts.pop()
            elif piece not in (".", ""):
                parts.append(piece)
        return "/".join(parts)
    return target


def collect_sources(root: Path, main: str | None, remappings: list[str], closure: bool) -> dict[str, str]:
    """Source units under `root` keyed by relative path; with `closure`, only the import closure of
    `main`."""
    all_sources: dict[str, str] = {}
    for path in sorted(root.rglob("*.sol")):
        all_sources[path.relative_to(root).as_posix()] = path.read_text(encoding="utf-8")
    if not all_sources:
        raise SystemExit(f"no .sol files under {root}")
    if not closure or main is None:
        return all_sources
    if main not in all_sources:
        raise SystemExit(f"main source {main} is not under {root}")
    wanted: dict[str, str] = {}
    queue = [main]
    while queue:
        unit = queue.pop()
        if unit in wanted:
            continue
        if unit not in all_sources:
            raise SystemExit(f"{unit} (imported) is not under {root}; add a remapping or the file")
        wanted[unit] = all_sources[unit]
        text = re.sub(r"//[^\n]*|/\*.*?\*/", "", all_sources[unit], flags=re.S)
        for match in IMPORT_RE.finditer(text):
            queue.append(resolve_import(unit, match.group(1), remappings))
    return dict(sorted(wanted.items()))


def solc_version(solc: str) -> str:
    out = subprocess.run([solc, "--version"], text=True, capture_output=True, check=True).stdout
    match = re.search(r"Version:\s*(\S+)", out)
    return match.group(1) if match else out.strip()


def vyper_scalar_immutable_type(ty: str) -> bool:
    if ty in ("address", "bool"):
        return True
    # A Vyper contract interface is represented by the address of its contract.
    # code_layout reports its source .vyi path rather than the word type.
    if ty.endswith(".vyi"):
        return True
    match = re.fullmatch(r"(?:uint|int)([0-9]+)", ty)
    if match:
        width = int(match.group(1))
        return 8 <= width <= 256 and width % 8 == 0
    match = re.fullmatch(r"bytes([0-9]+)", ty)
    return bool(match and 1 <= int(match.group(1)) <= 32)


def vyper_optimize_mode(source: str, no_optimize: bool) -> str:
    """Record the optimization selected by the CLI or the source pragma."""
    if no_optimize:
        return "none"
    match = re.search(r"(?m)^\s*#\s*pragma\s+optimize\s+(gas|codesize|none)\s*$", source)
    return match.group(1) if match else "gas"


def immutable_declarations(units: dict[str, dict]) -> dict[int, dict]:
    out: dict[int, dict] = {}
    for unit in units.values():
        for node in walk(unit):
            if node.get("nodeType") == "VariableDeclaration" and node.get("mutability") == "immutable":
                out[node["id"]] = {"id": node["id"], "name": node["name"],
                                   "type": node.get("typeDescriptions", {}).get("typeString", "")}
    return out


def immutable_write_order(creation: bytes, offsets_by_name: dict[str, list[int]]) -> list[str]:
    """Immutable names in the order the creation code patches their sites (``PUSH off ADD MSTORE``)."""
    instructions = rd.disassemble(creation)
    seen: list[str] = []
    site_name = {off: name for name, offs in offsets_by_name.items() for off in offs}
    for k, ins in enumerate(instructions):
        if ins.opcode == 0x52 and k >= 2 and instructions[k - 1].opcode == 0x01 \
                and 0x60 <= instructions[k - 2].opcode <= 0x7F:
            name = site_name.get(instructions[k - 2].argument)
            if name and name not in seen:
                seen.append(name)
    for name in offsets_by_name:
        if name not in seen:
            seen.append(name)
    return seen


def cmd_compile(args: argparse.Namespace) -> int:
    if args.vyper:
        return cmd_compile_vyper(args)
    directory: Path = args.dir
    directory.mkdir(parents=True, exist_ok=True)
    sources_root = directory / args.sources_root
    if not sources_root.exists():
        raise SystemExit(f"sources root {sources_root} does not exist")
    main = args.main
    if main is None:
        candidates = sorted(p.relative_to(sources_root).as_posix() for p in sources_root.rglob("*.sol"))
        if len(candidates) != 1:
            raise SystemExit("pass --main when the sources root holds more than one file")
        main = candidates[0]
    sources = collect_sources(sources_root, main, args.remapping or [], not args.all_sources)
    if main not in sources:
        raise SystemExit(f"main source {main} is not under {sources_root}")

    settings: dict = {
        "optimizer": {"enabled": not args.no_optimize, "runs": args.runs},
        "outputSelection": {"*": {"*": OUTPUT_SELECTION, "": ["ast"]}},
    }
    if args.via_ir:
        settings["viaIR"] = True
    if args.evm_version:
        settings["evmVersion"] = args.evm_version
    if args.metadata_hash:
        settings["metadata"] = {"bytecodeHash": args.metadata_hash}
    if args.remapping:
        settings["remappings"] = list(args.remapping)
    if args.settings_json:
        settings.update(json.loads(args.settings_json))
    settings["outputSelection"] = {"*": {"*": OUTPUT_SELECTION, "": ["ast"]}}
    request = {"language": "Solidity",
               "sources": {name: {"content": text} for name, text in sources.items()},
               "settings": settings}
    version = solc_version(args.solc)
    result = subprocess.run([args.solc, "--standard-json"], input=json.dumps(request),
                            text=True, capture_output=True, check=False)
    if result.returncode != 0:
        sys.stderr.write(result.stderr)
        return 1
    output = json.loads(result.stdout)
    errors = [e for e in output.get("errors", []) if e.get("severity") == "error"]
    if errors:
        for e in errors:
            sys.stderr.write(e.get("formattedMessage", e.get("message", "")) + "\n")
        return 1
    contracts = output.get("contracts", {}).get(main, {})
    name = args.contract
    if name is None:
        candidates = [c for c in contracts if contracts[c]["evm"]["deployedBytecode"]["object"]]
        if len(candidates) != 1:
            raise SystemExit(f"pass --contract; {main} defines {sorted(contracts)}")
        name = candidates[0]
    if name not in contracts:
        raise SystemExit(f"{main} does not define contract {name}; it defines {sorted(contracts)}")
    c = contracts[name]
    runtime_hex = c["evm"]["deployedBytecode"]["object"]
    creation_hex = c["evm"]["bytecode"]["object"]
    if not runtime_hex:
        raise SystemExit(f"{name} has no deployed bytecode (abstract or interface?)")
    if re.search(r"[^0-9a-fA-F]", creation_hex):
        sys.stderr.write("warning: creation bytecode has unlinked library placeholders\n")

    (directory / "runtime.hex").write_text(runtime_hex + "\n", encoding="utf-8")
    (directory / "creation.hex").write_text(creation_hex + "\n", encoding="utf-8")
    (directory / f"{name}.abi.json").write_text(json.dumps(c["abi"]) + "\n", encoding="utf-8")
    if c.get("storageLayout") is not None:
        (directory / f"{name}.storage.json").write_text(json.dumps(c["storageLayout"]) + "\n",
                                                        encoding="utf-8")
    if c.get("metadata"):
        (directory / f"{name}.metadata.json").write_text(c["metadata"] + "\n", encoding="utf-8")
    asts = {path: unit.get("ast") for path, unit in output.get("sources", {}).items()}
    ids = {path: unit.get("id") for path, unit in output.get("sources", {}).items()}
    if asts.get(main) is not None:
        (directory / f"{name}.sol.ast.json").write_text(json.dumps(asts[main]) + "\n",
                                                        encoding="utf-8")
    refs = c["evm"]["deployedBytecode"].get("immutableReferences") or {}
    decls = immutable_declarations({p: a for p, a in asts.items() if a})
    offsets_by_name = {decls[int(i)]["name"] if int(i) in decls else f"imm_{i}":
                       [site["start"] for site in sites] for i, sites in refs.items()}
    order = immutable_write_order(bytes.fromhex(creation_hex), offsets_by_name) if refs else []
    immutables = [{"id": next((d["id"] for d in decls.values() if d["name"] == n), None),
                   "name": n, "type": next((d["type"] for d in decls.values() if d["name"] == n), ""),
                   "offsets": offsets_by_name[n],
                   "lengths": sorted({s["length"] for i, ss in refs.items() for s in ss
                                      if (decls.get(int(i), {}).get("name") or f"imm_{i}") == n})}
                  for n in order]
    build = {
        "contract": name,
        "main": main,
        "sourcesRoot": args.sources_root,
        "compiler": {"version": version, "path": args.solc},
        "settings": {k: v for k, v in settings.items() if k != "outputSelection"},
        "sources": [{"id": ids[p], "path": p} for p in sorted(ids, key=lambda p: ids[p])],
        "methodIdentifiers": c["evm"].get("methodIdentifiers", {}),
        "immutableReferences": refs,
        "immutables": immutables,
        "sourceMap": {"runtime": c["evm"]["deployedBytecode"].get("sourceMap", ""),
                      "creation": c["evm"]["bytecode"].get("sourceMap", "")},
        "generatedSources": {"runtime": c["evm"]["deployedBytecode"].get("generatedSources", []),
                             "creation": c["evm"]["bytecode"].get("generatedSources", [])},
        "ast": asts,
    }
    (directory / f"{name}.build.json").write_text(json.dumps(build) + "\n", encoding="utf-8")
    write_hashes(directory, name, sources_root)
    runtime = bytes.fromhex(runtime_hex)
    body, meta = split_metadata(runtime)
    print(f"compiled {name} with solc {version}: runtime {len(runtime)} bytes "
          f"({len(meta)} metadata), creation {len(creation_hex) // 2} bytes, "
          f"{len(build['methodIdentifiers'])} selectors, {len(immutables)} immutables")
    return 0


def cmd_compile_vyper(args: argparse.Namespace) -> int:
    """Compile one Vyper module and preserve its code layout for suffix proofs."""
    directory: Path = args.dir
    directory.mkdir(parents=True, exist_ok=True)
    sources_root = directory / args.sources_root
    candidates = sorted(sources_root.rglob("*.vy"))
    main = args.main or (candidates[0].relative_to(sources_root).as_posix()
                         if len(candidates) == 1 else None)
    if main is None:
        raise SystemExit("pass --main when the sources root holds multiple .vy files")
    source = sources_root / main
    if not source.is_file() or source.suffix != ".vy":
        raise SystemExit(f"Vyper source {source} does not exist")
    optimize = vyper_optimize_mode(source.read_text(encoding="utf-8"), args.no_optimize)
    version = subprocess.run([args.vyper, "--version"], text=True, capture_output=True,
                             check=True).stdout.strip()
    if not version.startswith("0.4.3"):
        raise SystemExit(f"Vyper 0.4.3 required; got {version}")
    command = [args.vyper, "--no-bytecode-metadata", "-f", "combined_json"]
    if args.evm_version:
        command += ["--evm-version", args.evm_version]
    if args.no_optimize:
        command += ["--no-optimize"]
    command += ["--path", str(sources_root.resolve()), str(source.resolve())]
    result = subprocess.run(command, text=True, capture_output=True)
    if result.returncode:
        sys.stderr.write(result.stderr)
        return result.returncode
    output = json.loads(result.stdout)
    artifact = output.get(str(source.resolve()))
    if artifact is None:
        raise SystemExit(f"Vyper combined_json has no artifact for {source}")
    name = args.contract or source.stem
    # the annotated AST (types on every expression) drives vy2stele.py
    ast_command = [args.vyper, "-f", "annotated_ast"]
    if args.evm_version:
        ast_command += ["--evm-version", args.evm_version]
    ast_command += ["--path", str(sources_root.resolve()), str(source.resolve())]
    ast_result = subprocess.run(ast_command, text=True, capture_output=True)
    if ast_result.returncode:
        sys.stderr.write(ast_result.stderr)
        return ast_result.returncode
    annotated = json.loads(ast_result.stdout)
    for unit in [annotated.get("ast", {})] + list(annotated.get("imports", [])):
        for key in ("path", "resolved_path"):   # absolute on the compiling machine
            if unit.get(key):
                unit[key] = rel_to_root(Path(unit[key]), sources_root.resolve())
    (directory / f"{name}.vy.ast.json").write_text(json.dumps(annotated) + "\n", encoding="utf-8")
    layout = artifact.get("layout", {}).get("code_layout", {})
    immutables = []
    for key, info in sorted(layout.items(), key=lambda pair: pair[1]["offset"]):
        if not isinstance(info.get("offset"), int) or not isinstance(info.get("length"), int):
            raise SystemExit(f"invalid Vyper code_layout entry for {key}")
        if info["length"] != 32 or not vyper_scalar_immutable_type(info.get("type", "")):
            raise SystemExit(f"{key}: unsupported immutable type {info.get('type')} "
                             f"with length {info['length']}; scalar 32-byte slots are supported")
        immutables.append({"name": key, "type": info["type"], "offset": info["offset"],
                           "length": info["length"]})
    for left, right in zip(immutables, immutables[1:]):
        if left["offset"] + left["length"] > right["offset"]:
            raise SystemExit(f"overlapping Vyper immutable slots: {left['name']}, {right['name']}")
    suffix_size = max((i["offset"] + i["length"] for i in immutables), default=0)
    runtime_hex = artifact["bytecode_runtime"].removeprefix("0x")
    creation_hex = artifact["bytecode"].removeprefix("0x")
    (directory / "runtime.hex").write_text(runtime_hex + "\n", encoding="utf-8")
    (directory / "creation.hex").write_text(creation_hex + "\n", encoding="utf-8")
    (directory / f"{name}.abi.json").write_text(json.dumps(artifact["abi"]) + "\n", encoding="utf-8")
    (directory / f"{name}.storage.json").write_text(json.dumps(artifact["layout"]) + "\n", encoding="utf-8")
    build = {"contract": name, "main": main, "sourcesRoot": args.sources_root,
             "compiler": {"kind": "vyper", "version": version, "path": args.vyper},
             "settings": {"evmVersion": args.evm_version or "prague",
                          "optimize": optimize,
                          "bytecodeMetadata": False},
             "methodIdentifiers": artifact.get("method_identifiers", {}),
             "immutables": immutables, "immutableSuffixSize": suffix_size,
             "sourceMap": {"runtime": artifact.get("source_map_runtime", {}),
                           "creation": artifact.get("source_map", {})},
             "ast": annotated}
    (directory / f"{name}.build.json").write_text(json.dumps(build) + "\n", encoding="utf-8")
    write_hashes(directory, name, sources_root, ".vy")
    print(f"compiled {name} with Vyper {version}: runtime {len(runtime_hex)//2} bytes, "
          f"creation {len(creation_hex)//2} bytes, immutable suffix {suffix_size} bytes")
    return 0


def write_hashes(directory: Path, name: str, sources_root: Path, extension: str = ".sol") -> None:
    files = sorted(sources_root.rglob(f"*{extension}"))
    if extension == ".vy":
        files = sorted(files + list(sources_root.rglob("*.vyi")))
    for artifact in ("creation.hex", "runtime.hex", f"{name}.abi.json", f"{name}.sol.ast.json",
                     f"{name}.storage.json", f"{name}.metadata.json"):
        if (directory / artifact).exists():
            files.append(directory / artifact)
    lines = [f"{sha256_file(p)}  {rel_to_root(p, directory)}" for p in files]
    (directory / "sources.sha256").write_text("\n".join(lines) + "\n", encoding="utf-8")


# --------------------------------------------------------------------------------------------
# lean

def selector_table(directory: Path, name: str, build: dict | None) -> list[tuple[str, bytes]]:
    """(canonical signature, 4-byte selector) for every external function, in table order."""
    if build and build.get("methodIdentifiers"):
        # Vyper may omit leading zeroes when serializing a selector as hex.  It also lists
        # `__default__()`, whose selector the dispatcher never compares: the fallback runs when
        # no selector matches.
        pairs = [(sig, bytes.fromhex(sel.removeprefix("0x").zfill(8)))
                 for sig, sel in build["methodIdentifiers"].items()
                 if not (build.get("compiler", {}).get("kind") == "vyper" and sig.startswith("__default__("))]
        if any(len(value) != 4 for _, value in pairs):
            raise SystemExit("compiler emitted a method identifier wider than four bytes")
    else:
        abi_path = directory / f"{name}.abi.json"
        if not abi_path.exists():
            raise SystemExit("no build json and no ABI to derive selectors from")
        pairs = [(sig, selector(sig)) for sig in abi_signatures(load_json(abi_path))]
    spec_order = spec_syntax_order(directory)
    if spec_order:
        by_name: dict[str, list[tuple[str, bytes]]] = {}
        for sig, sel in pairs:
            by_name.setdefault(sig.split("(", 1)[0], []).append((sig, sel))
        ordered: list[tuple[str, bytes]] = []
        for fn in spec_order:
            ordered.extend(sorted(by_name.pop(fn, []), key=lambda p: p[1]))
        for rest in by_name.values():
            ordered.extend(sorted(rest, key=lambda p: p[1]))
        return ordered
    return sorted(pairs, key=lambda p: p[1])


def spec_syntax_order(directory: Path) -> list[str]:
    """External function names in `SpecSyntax.lean` order (the `contract.transitions` order)."""
    path = directory / "SpecSyntax.lean"
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8")
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    names: list[str] = []
    for match in re.finditer(r"\bfunction\s+«?([A-Za-z_][A-Za-z0-9_]*)»?\s*\(([^)]*)\)\s*([^{]*)\{", text):
        mods = match.group(3)
        if re.search(r"\b(internal|private)\b", mods):
            continue
        names.append(match.group(1))
    return names


def render_selectors_lean(namespace: str, prefix: str, name: str,
                          table: list[tuple[str, bytes]]) -> str:
    names = overload_names([sig for sig, _ in table])
    out = ["import Ethereum.Semantics", "", "/-!", f"# {name} selectors", "",
           "Generated by `scripts/scaffold.py lean`: the selector table in `contract.transitions` order,",
           "the selector predicates, and one kernel-checked keccak fact per ABI signature.  The bridge from",
           "each Stele transition's signature string to its entry (`transitionSigStr … = \"…\"`) is added by",
           "the proof skeleton once `Spec.lean` exists.", "-/", "",
           "open Ethereum Ethereum.EVM", "", f"namespace {namespace}", "",
           "/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/",
           f"abbrev {prefix}SelWord (I : ExecutionEnv) : UInt256 :=",
           "  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩", "",
           "/-- The 4-byte selector of `I`'s calldata equals `sel`. -/",
           "abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=",
           "  (sel == I.calldata.extract 0 4) = true", "",
           f"/-- Function selectors in `contract.transitions` order ({len(table)} entries). -/",
           f"def {prefix}SelBytes : ℕ → ByteArray"]
    for index, (sig, sel) in enumerate(table):
        pattern = f"| {index}" if index + 1 < len(table) else "| _"
        bytes_lit = ", ".join(f"0x{b:02x}" for b in sel)
        out.append(f"  {pattern} => ⟨#[{bytes_lit}]⟩  -- {sig}")
    if not table:
        out.append("  | _ => ⟨#[]⟩")
    out += ["", "set_option maxHeartbeats 0", "set_option maxRecDepth 1000000", ""]
    for index, (sig, sel) in enumerate(table):
        out += [f"/-- `keccak256(\"{sig}\")[0:4] = 0x{sel.hex()}`. -/",
                f"theorem {names[sig]}SelectorFact :",
                f"    (Ethereum.KEC (String.toByteArray \"{sig}\")).extract 0 4 = {prefix}SelBytes {index} := by",
                "  decide +kernel", ""]
    out += [f"end {namespace}", ""]
    return "\n".join(out)


def lean_field_type(solidity_type: str) -> str:
    return "EVM.Address" if solidity_type.startswith("address") or solidity_type.startswith("contract") \
        else "EVM.Word"


def render_immutables_lean(namespace: str, name: str, build: dict) -> str:
    imms = build["immutables"]
    out = ["import Stele.Syntax", "import EVM.Types", "",
           "/-!", f"# {name} immutable valuation and offset table", "",
           "Generated by `scripts/scaffold.py lean` from solc's `evm.deployedBytecode.immutableReferences`",
           f"(solc `{build['compiler']['version']}`).  `runtime.hex` is the runtime template with every",
           "immutable site zeroed; the constructor patches the sites in the order listed below, which is",
           "the order the creation code writes them.", "-/", "",
           "open Stele ABI", "", f"namespace {namespace}.Immutables", "",
           "/-- A valuation of the contract's immutables, as the runtime proofs consume them. -/",
           f"structure {name}Immutables where"]
    for imm in imms:
        out.append(f"  {imm['name']} : {lean_field_type(imm['type'])}")
    out += ["", "/-- solc `immutableReferences`: each immutable's Stele name and patch offsets, in the order the",
            "    constructor writes them. -/",
            "def immutableReferences : List (Ident × List Nat) :="]
    rows = [f"(\"{imm['name']}\", [{', '.join(str(o) for o in imm['offsets'])}])" for imm in imms]
    out.append("  [ " + ",\n    ".join(rows) + " ]")
    out += ["", f"end {namespace}.Immutables", ""]
    return "\n".join(out)


def render_immutable_code_lean(namespace: str, module: str) -> str:
    return "\n".join([
        f"import {module}.Immutables", "import Reasoning.Immutables", "",
        "/-!", "The patch sites of the deployed runtime template, keyed by Stele immutable name.  Generated",
        "summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them",
        "from a Stele immutables store.", "-/", "",
        "open Reasoning.Immutables", f"open {namespace}.Immutables", "", f"namespace {namespace}", "",
        "/-- Patch sites in the deployed runtime template. -/",
        "def immutableLayout : Layout :=",
        "  ⟨immutableReferences.flatMap (fun (name, sites) =>",
        "    sites.map (fun offset => (offset, 32, name)))⟩", "",
        f"end {namespace}", ""])


def render_vyper_immutables_lean(namespace: str, name: str, build: dict) -> str:
    rows = [f'{{ name := "{i["name"]}", offset := {i["offset"]}, length := {i["length"]} }}'
            for i in build["immutables"]]
    return "\n".join([
        "import Reasoning.VyperImmutables", "",
        f"/-! Vyper {build['compiler']['version']} `code_layout` for {name}. -/", "",
        f"namespace {namespace}", "",
        "/-- Offsets are relative to the appended immutable section. -/",
        "def immutableLayout : Reasoning.VyperImmutables.Layout :=",
        f"  {{ slots := [{', '.join(rows)}], size := {build['immutableSuffixSize']} }}", "",
        f"end {namespace}", ""])


def render_vyper_immutable_code_lean(namespace: str, module: str, prefix: str,
                                     build: dict) -> str:
    imms = build["immutables"]
    n = len(imms)
    values = " ".join(f"v{i}" for i in range(n))
    byte_values = " ".join(f"b{i}" for i in range(n))
    get_names = " ".join(f"hget{i}" for i in range(n))
    enc_names = " ".join(f"henc{i}" for i in range(n))
    patches = ", ".join(f"({imm['offset']}, b{i})" for i, imm in enumerate(imms))
    out = [
        f"import {module}.Bytecode", f"import {module}.Immutables", "",
        "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory", "",
        f"namespace {namespace}", "",
        "/-- Runtime bytes from the constructor's immutable valuation. -/",
        "def deployedRuntime (imms : Stele.Store) : ByteArray :=",
        f"  immutableLayout.deployed {prefix}Bytecode imms", "",
        "/-- The compiler's slot order, with each named Stele value encoded as Vyper bytes. -/",
        f"private theorem immutablePatches (imms : Stele.Store) ({values} : Stele.Value)",
        f"    ({byte_values} : ByteArray)",
    ]
    for i, imm in enumerate(imms):
        out += [f'    (hget{i} : imms.get? "{imm["name"]}" = some v{i})',
                f'    (henc{i} : Reasoning.VyperImmutables.scalarBytes? v{i} = some b{i})']
    out += [f"    : immutableLayout.patches? imms = some [{patches}] := by",
            f"  simp only [Std.HashMap.get?_eq_getElem?] at {get_names}",
            "  simp [immutableLayout, Reasoning.VyperImmutables.Layout.patches?,",
            f"    Reasoning.VyperImmutables.Slot.patch?, {get_names.replace(' ', ', ')}, "
            f"{enc_names.replace(' ', ', ')}]", ""]
    for i, imm in enumerate(imms):
        off = imm["offset"]
        before = ", ".join(f"({v['offset']}, b{j})" for j, v in enumerate(imms[:i]))
        after = ", ".join(f"({v['offset']}, b{i+1+j})" for j, v in enumerate(imms[i+1:]))
        assumptions = [f"    (hsize : b{i}.size = 32)",
                       "    (hsuffix : immutableLayout.suffix? imms = some suffix)"]
        evidence = " ".join(f"hget{j} henc{j}" for j in range(n))
        arguments = f"imms {values} {byte_values} {evidence}"
        common = [
            f"    (layout := immutableLayout) (imms := imms) (template := {prefix}Bytecode)",
            f"    (suffix := suffix) (value := b{i}) (pre := [{before}]) (post := [{after}])",
            f"  · simpa using immutablePatches {arguments}",
            "  · exact hsize", "  · decide",
        ]
        if after:
            cases = " | ".join("rfl" for _ in imms[i+1:])
            common += ["  · intro p hp", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp",
                       f"    rcases hp with {cases}", "    all_goals omega"]
        else:
            common += ["  · simp"]
        name = re.sub(r"[^A-Za-z0-9_]", "_", imm["name"])
        out += [f"/-- The runtime code read for Vyper immutable `{imm['name']}`. -/",
                f"theorem immutableRead_{name} (imms : Stele.Store) ({values} : Stele.Value)",
                f"    ({byte_values} suffix : ByteArray)"]
        for j, other in enumerate(imms):
            out += [f'    (hget{j} : imms.get? "{other["name"]}" = some v{j})',
                    f'    (henc{j} : Reasoning.VyperImmutables.scalarBytes? v{j} = some b{j})']
        out += [*assumptions,
                f"    : ({prefix}Bytecode ++ suffix).readWithPadding ({prefix}Bytecode.size + {off}) 32 = b{i} := by",
                "  apply Reasoning.VyperImmutables.Layout.runtime_read_slot", *common,
                "  · exact hsuffix", ""]
        out += [f"/-- Read `{imm['name']}` back from memory after copying the immutable section. -/",
                f"theorem immutableCopy_{name} (imms : Stele.Store) ({values} : Stele.Value)",
                f"    ({byte_values} suffix mem : ByteArray) (dest : Nat)"]
        for j, other in enumerate(imms):
            out += [f'    (hget{j} : imms.get? "{other["name"]}" = some v{j})',
                    f'    (henc{j} : Reasoning.VyperImmutables.scalarBytes? v{j} = some b{j})']
        out += [*assumptions,
                f"    : (({prefix}Bytecode ++ suffix).write {prefix}Bytecode.size mem dest "
                f"{build['immutableSuffixSize']}).readWithPadding (dest + {off}) 32 = b{i} := by",
                "  apply Reasoning.VyperImmutables.Layout.codecopy_read_slot",
                *common, "  · exact hsuffix", ""]
        def word_patch(other: dict) -> str:
            return f'({other["offset"]}, (immWords "{other["name"]}").toByteArray)'
        word_pre = "[" + ", ".join(map(word_patch, imms[:i])) + "]"
        word_post = "[" + ", ".join(map(word_patch, imms[i + 1:])) + "]"
        out += [f"/-- A 32-byte code copy and MLOAD of `{imm['name']}` returns its word. -/",
                f"theorem immutableLoad_{name} (immWords : String → Ethereum.UInt256)",
                "    (mem : ByteArray) (dest : Ethereum.UInt256) :",
                f"    Reasoning.Reach.memLoad dest (({prefix}Bytecode ++ immutableLayout.suffixWords immWords).write",
                f"      ({prefix}Bytecode.size + {off}) mem dest.toNat 32) = immWords \"{imm['name']}\" := by",
                "  have hslots :",
                "      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =",
                f"      {word_pre} ++ ({off}, (immWords \"{imm['name']}\").toByteArray) :: {word_post} := by",
                "    rfl",
                "  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)",
                "      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =",
                "      some suffix := by",
                "    simp only [immutableLayout, List.map_cons, List.map_nil]",
                "    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,",
                "      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]",
                f"  have hpost : ∀ (p : Nat × ByteArray), p ∈ {word_post} → "
                f"{off} + 32 ≤ p.1 ∨ p.1 + 32 ≤ {off} := by",
                "    intro p hp",
                "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp"
                if imms[i + 1:] else "    simp at hp",
                "    rcases hp with " + " | ".join("rfl" for _ in imms[i + 1:])
                if imms[i + 1:] else "",
                "    all_goals omega" if imms[i + 1:] else "",
                "  exact Reasoning.VyperImmutables.Layout.codecopy_load_scalar",
                "    (layout := immutableLayout) (template := " + f"{prefix}Bytecode) (mem := mem)",
                f"    (words := immWords) (name := \"{imm['name']}\") (offset := {off}) (dest := dest)",
                f"    (pre := {word_pre}) (post := {word_post}) hslots (by decide) hpost hpatch", ""]
        out += [f"/-- Copying `{imm['name']}` from code writes its named word bytes to memory. -/",
                f"theorem immutableCopyWord_{name} (immWords : String → Ethereum.UInt256)",
                "    (mem : ByteArray) (dest : Nat) :",
                f"    (({prefix}Bytecode ++ immutableLayout.suffixWords immWords).write",
                f"      ({prefix}Bytecode.size + {off}) mem dest 32) =",
                f"      (immWords \"{imm['name']}\").toByteArray.write 0 mem dest 32 := by",
                "  have hslots :",
                "      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =",
                f"      {word_pre} ++ ({off}, (immWords \"{imm['name']}\").toByteArray) :: {word_post} := by",
                "    rfl",
                "  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)",
                "      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =",
                "      some suffix := by",
                "    simp only [immutableLayout, List.map_cons, List.map_nil]",
                "    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,",
                "      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]",
                f"  have hpost : ∀ (p : Nat × ByteArray), p ∈ {word_post} → "
                f"{off} + 32 ≤ p.1 ∨ p.1 + 32 ≤ {off} := by",
                "    intro p hp",
                "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp"
                if imms[i + 1:] else "    simp at hp",
                "    rcases hp with " + " | ".join("rfl" for _ in imms[i + 1:])
                if imms[i + 1:] else "",
                "    all_goals omega" if imms[i + 1:] else "",
                "  exact Reasoning.VyperImmutables.Layout.codecopy_write_scalar",
                "    (layout := immutableLayout) (template := " + f"{prefix}Bytecode) (mem := mem)",
                f"    (words := immWords) (name := \"{imm['name']}\") (offset := {off}) (dest := dest)",
                f"    (pre := {word_pre}) (post := {word_post}) hslots (by decide) hpost hpatch", ""]
    out += ["/-- The scalar word valuation encodes the same suffix as the Stele store. -/",
            f"theorem immutableWordsBridge (imms : Stele.Store) ({values} : Stele.Value)",
            f"    ({byte_values} : ByteArray)"]
    for i, imm in enumerate(imms):
        out += [f'    (hget{i} : imms.get? "{imm["name"]}" = some v{i})',
                f'    (henc{i} : Reasoning.VyperImmutables.scalarBytes? v{i} = some b{i})']
    out += ["    " + " ".join(f"(hsize{i} : b{i}.size = 32)" for i in range(n)),
            "    : immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) =",
            "      (immutableLayout.suffix? imms).getD (ByteArray.zeroes immutableLayout.size) := by",
            f"  have hp := immutablePatches imms {values} {byte_values} "
            + " ".join(f"hget{i} henc{i}" for i in range(n)),
            f"  simp only [Std.HashMap.get?_eq_getElem?] at {get_names}"]
    for i, imm in enumerate(imms):
        out += [f"  have hw{i} : Ethereum.UInt256.toByteArray",
                f'      (Reasoning.VyperImmutables.wordsOf imms "{imm["name"]}") = b{i} := by',
                f"    simp [Reasoning.VyperImmutables.wordsOf, hget{i}, henc{i},",
                f"      Reasoning.Theory.toByteArray_uInt256OfByteArray_of_size32 hsize{i}]"]
    out += ["  simp only [Reasoning.VyperImmutables.Layout.suffixWords,",
            "    Reasoning.VyperImmutables.Layout.suffix?]",
            "  rw [hp]",
            f"  simp [immutableLayout, {', '.join(f'hw{i}' for i in range(n))}]", ""]
    out += ["/-- The scalar word runtime agrees with the constructor's Stele valuation. -/",
            f"theorem deployedRuntime_eq_words (imms : Stele.Store) ({values} : Stele.Value)",
            f"    ({byte_values} : ByteArray)"]
    for i, imm in enumerate(imms):
        out += [f'    (hget{i} : imms.get? "{imm["name"]}" = some v{i})',
                f'    (henc{i} : Reasoning.VyperImmutables.scalarBytes? v{i} = some b{i})']
    out += ["    " + " ".join(f"(hsize{i} : b{i}.size = 32)" for i in range(n)),
            f"    : deployedRuntime imms = {prefix}Bytecode ++",
            "        immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) := by",
            "  unfold deployedRuntime Reasoning.VyperImmutables.Layout.deployed",
            "  rw [immutableWordsBridge imms " + f"{values} {byte_values} "
            + " ".join(f"hget{i} henc{i}" for i in range(n))
            + " " + " ".join(f"hsize{i}" for i in range(n)) + "]", ""]
    out += ["/-- Constructor memory writes in slot order produce the patched runtime. -/",
            f"theorem returnedRuntime_eq_deployed (imms : Stele.Store) (returned : ByteArray)",
            f"    ({values} : Stele.Value) ({byte_values} : ByteArray)"]
    for i, imm in enumerate(imms):
        out += [f'    (hget{i} : imms.get? "{imm["name"]}" = some v{i})',
                f'    (henc{i} : Reasoning.VyperImmutables.scalarBytes? v{i} = some b{i})']
    out += ["    " + " ".join(f"(hsize{i} : b{i}.size = 32)" for i in range(n)),
            f"    (hreturned : returned = {prefix}Bytecode ++",
            "      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)",
            "        (immutableLayout.slots.map fun slot =>",
            "          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :",
            "    returned = deployedRuntime imms := by",
            "  exact Reasoning.VyperImmutables.Layout.returned_eq_deployed",
            f"    immutableLayout {prefix}Bytecode returned imms (by decide)",
            "    (immutableWordsBridge imms " + f"{values} {byte_values} "
            + " ".join(f"hget{i} henc{i}" for i in range(n))
            + " " + " ".join(f"hsize{i}" for i in range(n)) + ") hreturned", ""]
    out += ["/-- A full RETURN read of that buffer yields the patched runtime. -/",
            f"theorem returnedRuntime_read_eq_deployed (imms : Stele.Store) (returned : ByteArray)",
            f"    ({values} : Stele.Value) ({byte_values} : ByteArray)"]
    for i, imm in enumerate(imms):
        out += [f'    (hget{i} : imms.get? "{imm["name"]}" = some v{i})',
                f'    (henc{i} : Reasoning.VyperImmutables.scalarBytes? v{i} = some b{i})']
    out += ["    " + " ".join(f"(hsize{i} : b{i}.size = 32)" for i in range(n)),
            f"    (hreturned : returned = {prefix}Bytecode ++",
            "      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)",
            "        (immutableLayout.slots.map fun slot =>",
            "          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :",
            f"    returned.readWithPadding 0 ({prefix}Bytecode.size + immutableLayout.size) =",
            "      deployedRuntime imms := by",
            "  exact Reasoning.VyperImmutables.Layout.returned_read_eq_deployed",
            f"    immutableLayout {prefix}Bytecode returned imms (by decide)",
            "    (immutableWordsBridge imms " + f"{values} {byte_values} "
            + " ".join(f"hget{i} henc{i}" for i in range(n))
            + " " + " ".join(f"hsize{i}" for i in range(n))
            + ") hreturned (by native_decide) (by native_decide)", ""]
    out += [f"end {namespace}", ""]
    return "\n".join(out)


def render_difftarget_lean(namespace: str, module: str, prefix: str, name: str,
                           has_creation: bool, has_immutables: bool) -> str:
    """The contract's `Target` for the differential suite (`Stele/DiffTest/Harness.lean`)."""
    out = ["import Stele.DiffTest.Harness", f"import {module}.Spec", f"import {module}.Bytecode"]
    if has_creation:
        out.append(f"import {module}.CreationBytecode")
    if has_immutables:
        out.append(f"import {module}.ImmutableCode")
    out += ["", "/-!", f"# {name} differential-test target (generated by `scripts/scaffold.py difftest`)", "",
            "Registered in `Tests/DiffTest/Generated.lean`; run with `lake exe stele-difftest --only "
            f"{name}`.", "Adjust `callees` and `words` when the contract needs specific counterparties or amounts.",
            "-/", "", "open Stele Stele.DiffTest", "", f"namespace {namespace}", "",
            "def diffTarget : Target :=",
            f"  {{ name := \"{name}\", contract := contract, config := config, runtime := {prefix}Bytecode,"]
    initcode = f"some {prefix}CreationBytecode" if has_creation else "none"
    fields = [f"    initcode := {initcode}"]
    if has_immutables:
        fields += ["    -- runtime cases use the store a generated constructor run leaves; the zero valuation\n"
                   "    -- is the fallback\n"
                   "    immutables := initialImmutables contract",
                   f"    runtimeCodeOf := some (immutableLayout.deployed {prefix}Bytecode)",
                   "    deployedRuntime := true"]
    fields += ["    callees := standardCallees, words := [10 ^ 18] }"]
    out += [",\n".join(fields), "", f"end {namespace}", ""]
    return "\n".join(out)


def difftarget_files(root: Path) -> list[Path]:
    """Every `DiffTarget.lean` of the checkout, skipping hidden directories (`.lake`, git worktrees
    under `.claude/`, …)."""
    return sorted(p for p in root.rglob("DiffTarget.lean")
                  if not any(part.startswith(".") for part in p.relative_to(root).parts))


def render_difftest_registry(root: Path) -> str:
    """`Tests/DiffTest/Generated.lean`: every `DiffTarget.lean` in the repository."""
    entries: list[tuple[str, str]] = []
    for path in difftarget_files(root):
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        m = re.search(r"^namespace\s+(\S+)", path.read_text(encoding="utf-8"), re.M)
        if not m:
            raise SystemExit(f"{path}: no namespace line")
        entries.append((module, m.group(1)))
    out = ["import Stele.DiffTest.Harness"] + [f"import {module}" for module, _ in entries]
    out += ["", "/-!", "Generated by `scripts/scaffold.py difftest`: the targets of every `DiffTarget.lean` in the",
            "repository.  Do not edit; rerun the script after adding or removing a target.", "-/", "",
            "namespace Tests.DiffTest", "", "def generatedTargets : List Stele.DiffTest.Target :="]
    if entries:
        out.append("  [ " + ",\n    ".join(f"{ns}.diffTarget" for _, ns in entries) + " ]")
    else:
        out.append("  []")
    out += ["", "end Tests.DiffTest", ""]
    return "\n".join(out)


def write_file(path: Path, text: str, force: bool) -> bool:
    if path.exists() and not force:
        print(f"kept existing {rel_to_root(path)} (use --force to overwrite)")
        return False
    path.write_text(text, encoding="utf-8")
    print(f"wrote {rel_to_root(path)}")
    return True


def cmd_lean(args: argparse.Namespace) -> int:
    directory: Path = args.dir
    name = contract_name(directory, args.contract)
    build_path = find_build(directory, name)
    build = load_json(build_path) if build_path else None
    module = args.module or default_module(directory)
    namespace = args.namespace or module
    prefix = args.prefix or lower_camel(name)
    # The runtime and creation listings (gen_listing.py) define the bytecode constants.
    for creation in (False, True):
        if creation and not (directory / "creation.hex").exists():
            continue
        gen_listing.write_listing(directory, module, name, prefix, build, creation, args.force,
                                  namespace=namespace,
                                  constant_namespace=args.constant_namespace)
    table = selector_table(directory, name, build)
    write_file(directory / "Selectors.lean", render_selectors_lean(namespace, prefix, name, table),
               args.force)
    if build and build.get("immutables"):
        if build["compiler"].get("kind") == "vyper":
            write_file(directory / "Immutables.lean",
                       render_vyper_immutables_lean(namespace, name, build), args.force)
            write_file(directory / "ImmutableCode.lean",
                       render_vyper_immutable_code_lean(namespace, module, prefix, build), args.force)
        else:
            write_file(directory / "Immutables.lean", render_immutables_lean(namespace, name, build), args.force)
            write_file(directory / "ImmutableCode.lean", render_immutable_code_lean(namespace, module), args.force)
    return 0


def cmd_difftest(args: argparse.Namespace) -> int:
    directory: Path = args.dir
    name = contract_name(directory, args.contract)
    build_path = find_build(directory, name)
    build = load_json(build_path) if build_path else None
    module = args.module or default_module(directory)
    namespace = args.namespace or module
    prefix = args.prefix or lower_camel(name)
    has_creation = (directory / "creation.hex").exists()
    has_immutables = bool(build and build.get("immutables"))
    write_file(directory / "DiffTarget.lean",
               render_difftarget_lean(namespace, module, prefix, name, has_creation, has_immutables), args.force)
    if not args.no_register:
        root = Path(args.repo_root).resolve()
        registry = root / "Tests" / "DiffTest" / "Generated.lean"
        registry.write_text(render_difftest_registry(root), encoding="utf-8")
        print(f"wrote {registry} ({len(difftarget_files(root))} target(s))")
    return 0


# --------------------------------------------------------------------------------------------
# blocks

def immutable_sites(build: dict, runtime: bytes) -> dict[int, tuple[int, str]]:
    raw = [{"offset": off, "length": 32, "key": imm["name"]}
           for imm in build["immutables"] for off in imm["offsets"]]
    return rd.validate_immutable_sites(raw, runtime)


def cmd_blocks(args: argparse.Namespace) -> int:
    directory: Path = args.dir
    name = contract_name(directory, args.contract)
    build_path = find_build(directory, name)
    build = load_json(build_path) if build_path else None
    module = args.module or default_module(directory)
    namespace = args.namespace or module
    prefix = args.prefix or lower_camel(name)
    runtime = read_bytecode(directory / "runtime.hex")
    # The modules defining the bytecode constants: the listings, or an old-format Bytecode.lean.
    own_bytecode = rd.bytecode_imports(directory, module)
    sites = None
    runtime_suffix = bool(build and build["compiler"].get("kind") == "vyper"
                          and build.get("immutables"))
    imports = list(own_bytecode)
    if runtime_suffix:
        imports.append(f"{module}.Immutables")
        imports.append(f"{module}.ImmutableCode")
    layout_term = None
    if build and build.get("immutables") and not runtime_suffix:
        sites = immutable_sites(build, runtime)
        imports.append(f"{module}.ImmutableCode")
        layout_term = f"{namespace}.immutableLayout"
    vyper_slots = ({len(runtime) + slot["offset"]: slot["name"]
                    for slot in build["immutables"] if slot["length"] == 32}
                   if runtime_suffix else None)
    # When Bytecode.lean is a listing (`gen_listing.py`) the runtime summaries are proved by a
    # run over it; an old-format Bytecode.lean (chunked arrays) keeps the rule chains.
    listing = (rd.directory_listing(directory, module, runtime,
                                    tail="suffix" if runtime_suffix else None)
               if not args.no_listing else None)
    units = rd.generate_unit_records(runtime, prefix, f"{namespace}.{prefix}Bytecode", False, False,
                                     args.max_summary_instructions, False, sites, layout_term, runtime_suffix,
                                     vyper_slots,
                                     f"{namespace}.immutableLayout" if runtime_suffix else None,
                                     build["immutableSuffixSize"] if runtime_suffix else None,
                                     listing=listing)
    paths = rd.write_outputs(directory / "RuntimeBlocks.lean", prefix, imports, units, args.shard_size,
                             False, f"{namespace}.{prefix}Bytecode", None, sites, runtime, layout_term,
                             runtime_suffix, listing=listing)
    print(f"wrote {len(paths)} runtime summary shards ({len(units)} units) and RuntimeBlocks.index")
    creation_path = directory / "creation.hex"
    if creation_path.exists() and not args.no_creation:
        creation = read_bytecode(creation_path)
        listing = (rd.directory_listing(directory, module, creation, creation=True)
                   if not args.no_listing else None)
        units = rd.generate_unit_records(creation, f"{prefix}Creation", f"{namespace}.{prefix}CreationBytecode",
                                         False, False, args.max_summary_instructions, True, None, None, False,
                                         listing=listing)
        paths = rd.write_outputs(directory / "CreationBlocks.lean", f"{prefix}Creation",
                                 rd.bytecode_imports(directory, module, creation=True),
                                 units, args.shard_size, True, f"{namespace}.{prefix}CreationBytecode",
                                 listing=listing)
        print(f"wrote {len(paths)} creation summary shards ({len(units)} units) and CreationBlocks.index")
    return 0


# --------------------------------------------------------------------------------------------
# check

def lean_selector_table(text: str) -> list[tuple[str, bytes]]:
    out: list[tuple[str, bytes]] = []
    for match in re.finditer(r"\|\s*(?:\d+|_)\s*=>\s*⟨#\[([^\]]*)\]⟩\s*--\s*(\S+)", text):
        out.append((match.group(2), bytes(int(b, 16) for b in match.group(1).split(","))))
    return out


def check_listing(path: Path, constant: str, namespace: str, hex_name: str, build: dict | None,
                  ok: list[str], failures: list[str]) -> None:
    """A listing (`gen_listing.py`, a `listing_from_hex` command) against the artifacts: its
    namespace, the constant it defines, the hex file it reads (the artifact ``hex_name``) and
    that file's SHA-256 (the one written in the listing), its mode (creation code and a Vyper
    runtime with immutables are followed by data), and for solc immutables its layout's sites
    against the build JSON.  The table is not compared: the command decodes the hex file and
    the kernel checks the table against the bytes when the file is built."""
    name = path.name
    try:
        listing = bytecode_io.read_listing(path)
    except ValueError as error:
        failures.append(f"{name}: {error}")
        return
    if listing is None:
        failures.append(f"{name}: not a listing (regenerate it with gen_listing.py)")
        return
    (ok if listing.namespace == namespace else failures).append(
        f"{name}: namespace {listing.namespace}"
        + ("" if listing.namespace == namespace else f", expected {namespace}"))
    (ok if listing.bytecode == constant else failures).append(
        f"{name}: {'defines' if listing.bytecode == constant else 'defines ' + listing.bytecode + ', not'}"
        f" {constant}")
    (ok if listing.file == hex_name else failures).append(
        f"{name}: reads {listing.file}" + ("" if listing.file == hex_name else f", expected {hex_name}"))
    try:
        bytecode_io.check_listing_hash(listing)
        ok.append(f"{name}: SHA-256 of {listing.file} matches")
    except ValueError as error:
        failures.append(f"{name}: {error}")
        return
    creation = hex_name == "creation.hex"
    vyper = bool(build and build["compiler"].get("kind") == "vyper")
    tail = "tail" if creation else "suffix" if vyper and build.get("immutables") else None
    (ok if listing.followed_by == tail and listing.creation == creation else failures).append(
        f"{name}: " + (f"followed by `{listing.followed_by}`" if listing.followed_by else "stands alone")
        + ("" if listing.followed_by == tail else f", expected {tail or 'no tail'}")
        + ("" if listing.creation == creation else ", `creation` flag wrong"))
    if creation or vyper or not (build and build.get("immutables")):
        if listing.layout is not None and build is not None and not creation:
            ok.append(f"{name}: layout {listing.layout} (no solc immutables in the build JSON)")
        return
    if listing.layout is None:
        failures.append(f"{name}: no `layout` although the build JSON lists solc immutables")
        return
    expected = {off: imm["name"] for imm in build["immutables"] for off in imm["offsets"]}
    order = [imm["name"] for imm in build["immutables"]]
    if listing.names and list(listing.names) != order:
        failures.append(f"{name}: `names` {list(listing.names)} differ from the build JSON's order {order}")
    code = bytecode_io.parse_bytecode_text(listing.hex_path.read_text(encoding="utf-8"))
    try:
        found = rd.read_lean_layout(listing.layout, [m for m in listing.imports
                                                     if not m.startswith("Reasoning.")], code)
    except ValueError as error:
        ok.append(f"{name}: layout sites not compared (could not evaluate {listing.layout}; "
                  f"build its module first): {str(error).splitlines()[0]}")
        return
    sites = {off: key for off, (_, key) in found.items()}
    first = list(dict.fromkeys(key for _, (_, key) in found.items()))
    (ok if sites == expected else failures).append(
        f"{name}: {len(sites)} layout sites " + ("match" if sites == expected else "differ from")
        + " the build JSON")
    if not listing.names and first != order:
        failures.append(f"{name}: immutables number by first appearance {first}, the build JSON "
                        f"orders them {order}: write `names` (gen_listing.py does)")


def cmd_check(args: argparse.Namespace) -> int:
    directory: Path = args.dir
    name = contract_name(directory, args.contract)
    build_path = find_build(directory, name)
    build = load_json(build_path) if build_path else None
    prefix = args.prefix or lower_camel(name)
    failures: list[str] = []
    ok: list[str] = []

    namespace = args.namespace or args.module or default_module(directory)
    cns = namespace if args.constant_namespace is None else args.constant_namespace
    qual = f"{cns}." if cns else ""
    bytecode_lean = directory / "Bytecode.lean"
    if bytecode_lean.exists():
        check_listing(bytecode_lean, f"{qual}{prefix}Bytecode", f"{namespace}.Listing",
                      "runtime.hex", build, ok, failures)
    else:
        failures.append("Bytecode.lean is missing")
    if (directory / "creation.hex").exists():
        creation_lean = directory / "CreationBytecode.lean"
        if creation_lean.exists():
            check_listing(creation_lean, f"{qual}{prefix}CreationBytecode",
                          f"{namespace}.CreationListing", "creation.hex", build, ok, failures)
        else:
            failures.append("CreationBytecode.lean is missing although creation.hex exists")

    selectors_lean = directory / "Selectors.lean"
    if selectors_lean.exists():
        table = lean_selector_table(selectors_lean.read_text(encoding="utf-8"))
        expected = selector_table(directory, name, build)
        if table == expected:
            ok.append(f"Selectors.lean: {len(table)} entries match the ABI in SpecSyntax order")
        elif sorted(table, key=lambda p: p[1]) == sorted(expected, key=lambda p: p[1]):
            failures.append("Selectors.lean: same selectors but a different order than SpecSyntax.lean")
        else:
            failures.append("Selectors.lean: selector table differs from the ABI")
        for sig, sel in table:
            if selector(sig) != sel:
                failures.append(f"Selectors.lean: keccak(\"{sig}\")[0:4] is {selector(sig).hex()}, table has {sel.hex()}")
    else:
        failures.append("Selectors.lean is missing")

    if build and build.get("immutables") and build["compiler"].get("kind") == "vyper":
        imm_lean = directory / "Immutables.lean"
        if imm_lean.exists():
            body = imm_lean.read_text(encoding="utf-8")
            for imm in build["immutables"]:
                fragment = (f'name := "{imm["name"]}", offset := {imm["offset"]}, '
                            f'length := {imm["length"]}')
                (ok if fragment in body else failures).append(
                    f"{imm['name']} code_layout {'matches' if fragment in body else 'differs from'} Immutables.lean")
            if f"size := {build['immutableSuffixSize']}" not in body:
                failures.append("immutable suffix size differs from Immutables.lean")
        else:
            failures.append("Immutables.lean is missing although the contract has immutables")
    elif build and build.get("immutables"):
        imm_lean = directory / "Immutables.lean"
        if imm_lean.exists():
            text = imm_lean.read_text(encoding="utf-8")
            pairs = re.findall(r"\(\"([A-Za-z_][A-Za-z0-9_]*)\",\s*\[([0-9,\s]*)\]\)", text)
            found = {n: [int(x) for x in offs.split(",") if x.strip()] for n, offs in pairs}
            expected = {i["name"]: i["offsets"] for i in build["immutables"]}
            (ok if found == expected else failures).append(
                f"Immutables.lean offsets {'match' if found == expected else 'differ from'} immutableReferences")
        else:
            failures.append("Immutables.lean is missing although the contract has immutables")

    hashes = directory / "sources.sha256"
    if hashes.exists():
        bad = []
        for line in hashes.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            digest, path = line.split(None, 1)
            target = ROOT / path if (ROOT / path).exists() else directory / path
            if not target.exists() or sha256_file(target) != digest:
                bad.append(path)
        (ok if not bad else failures).append(
            "sources.sha256 verified" if not bad else f"sources.sha256 mismatch: {', '.join(bad)}")
    for line in ok:
        print(f"ok   {line}")
    for line in failures:
        print(f"FAIL {line}")
    return 1 if failures else 0


# --------------------------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    def common(p: argparse.ArgumentParser) -> None:
        p.add_argument("--dir", type=Path, required=True, help="contract directory")
        p.add_argument("--contract", help="contract name (default: from *.build.json or the ABI file)")

    def compile_args(p: argparse.ArgumentParser) -> None:
        p.add_argument("--solc", default="solc", help="solc binary (default: solc on PATH)")
        p.add_argument("--vyper", help="use this Vyper 0.4.3 binary instead of solc")
        p.add_argument("--main", help="main source unit, relative to the sources root")
        p.add_argument("--sources-root", default=None,
                       help="directory holding .sol or .vy sources (default: contracts/ if present, else .)")
        p.add_argument("--runs", type=int, default=200)
        p.add_argument("--no-optimize", action="store_true")
        p.add_argument("--via-ir", action="store_true")
        p.add_argument("--evm-version")
        p.add_argument("--metadata-hash", default="none", help="none | ipfs | bzzr1 | '' to leave default")
        p.add_argument("--remapping", action="append", help="solc remapping prefix=target (repeatable)")
        p.add_argument("--all-sources", action="store_true",
                       help="compile every .sol under the sources root, not just the import closure of --main")
        p.add_argument("--settings-json", help="extra standard-json settings, merged last")

    def lean_args(p: argparse.ArgumentParser) -> None:
        p.add_argument("--module", help="Lean module path of the directory (default: from its path)")
        p.add_argument("--namespace", help="Lean namespace (default: the module path)")
        p.add_argument("--prefix", help="declaration prefix (default: lowerCamel contract name)")
        p.add_argument("--constant-namespace",
                       help="namespace of the bytecode constants (default: the namespace; '' for "
                            "the root)")
        p.add_argument("--force", action="store_true", help="overwrite existing generated files")

    def difftest_args(p: argparse.ArgumentParser) -> None:
        p.add_argument("--no-register", action="store_true",
                       help="write DiffTarget.lean only; leave Tests/DiffTest/Generated.lean alone")
        p.add_argument("--repo-root", default=str(Path(__file__).resolve().parent.parent),
                       help="repository root holding Tests/DiffTest (default: this checkout)")

    def blocks_args(p: argparse.ArgumentParser) -> None:
        p.add_argument("--shard-size", type=int, default=20)
        p.add_argument("--max-summary-instructions", type=int, default=rd.MAX_SUMMARY_INSTRUCTIONS)
        p.add_argument("--no-creation", action="store_true")
        p.add_argument("--no-listing", action="store_true",
                       help="keep the rule-chain proofs even when Bytecode.lean / "
                            "CreationBytecode.lean are listings")

    p = sub.add_parser("compile", help="run solc and write the artifacts"); common(p); compile_args(p)
    p = sub.add_parser("lean", help="write the listings (Bytecode, CreationBytecode), Selectors, Immutables"); common(p); lean_args(p)
    p = sub.add_parser("blocks", help="generate block summaries"); common(p); lean_args(p); blocks_args(p)
    p = sub.add_parser("check", help="verify artifacts against the Lean files"); common(p); lean_args(p)
    p = sub.add_parser("difftest", help="write DiffTarget.lean and the suite registry"); common(p); lean_args(p); difftest_args(p)
    p = sub.add_parser("all", help="compile, lean, difftest, blocks, check"); common(p); compile_args(p); lean_args(p); difftest_args(p); blocks_args(p)
    args = parser.parse_args(argv)
    if hasattr(args, "sources_root") and args.sources_root is None:
        args.sources_root = "contracts" if (args.dir / "contracts").exists() else "."
    if args.command == "compile":
        return cmd_compile(args)
    if args.command == "lean":
        return cmd_lean(args)
    if args.command == "blocks":
        return cmd_blocks(args)
    if args.command == "check":
        return cmd_check(args)
    if args.command == "difftest":
        return cmd_difftest(args)
    for step in (cmd_compile, cmd_lean, cmd_difftest, cmd_blocks, cmd_check):
        code = step(args)
        if code:
            return code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

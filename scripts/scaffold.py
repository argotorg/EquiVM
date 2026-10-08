#!/usr/bin/env python3
"""Build a contract's proof scaffold from compiler artifacts.

Subcommands (``all`` runs them in order):

  compile   run solc (standard JSON) on the pinned sources and write the artifacts:
            runtime.hex, creation.hex, <Name>.abi.json, <Name>.storage.json,
            <Name>.sol.ast.json (main source unit), <Name>.metadata.json, sources.sha256, and
            <Name>.build.json (compiler version and settings, method identifiers, immutable
            references, source maps, generated sources, every source unit's AST).
  lean      write Bytecode.lean (chunked byte arrays plus the JUMPDEST theorems), Selectors.lean
            (selector table, selIs/selWord, keccak facts), and for contracts with immutables
            Immutables.lean and ImmutableCode.lean.  Existing files are kept unless --force.
  blocks    generate the proved block summaries RuntimeBlocks_NNN.lean / CreationBlocks_NNN.lean
            with scripts/generate_rd_blocks.py (immutable-aware when the contract has immutables).
  check     verify that the Lean byte arrays, jump tables, selector table, immutable offsets and
            sources.sha256 agree with the artifacts.

Example:
  scripts/scaffold.py all --dir Benchmarks/Scaffolds/Foo --solc /tmp/solc-0.8.20 \
      --main contracts/Foo.sol --contract Foo --runs 200 --evm-version shanghai \
      --module Benchmarks.Scaffolds.Foo
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import generate_rd_blocks as rd
from bytecode_io import read_bytecode
from evm_tools import (abi_signatures, jump_dests, lean_name, overload_names, selector,
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


def write_hashes(directory: Path, name: str, sources_root: Path) -> None:
    files = sorted(sources_root.rglob("*.sol"))
    for artifact in ("creation.hex", "runtime.hex", f"{name}.abi.json", f"{name}.sol.ast.json",
                     f"{name}.storage.json", f"{name}.metadata.json"):
        if (directory / artifact).exists():
            files.append(directory / artifact)
    lines = [f"{sha256_file(p)}  {rel_to_root(p, directory)}" for p in files]
    (directory / "sources.sha256").write_text("\n".join(lines) + "\n", encoding="utf-8")


# --------------------------------------------------------------------------------------------
# lean

def render_bytes(name: str, data: bytes, chunk_size: int, private: bool = True) -> tuple[list[str], str]:
    """Chunk definitions for ``data`` and the term concatenating them."""
    lines: list[str] = []
    chunks = [data[i:i + chunk_size] for i in range(0, len(data), chunk_size)] or [b""]
    for index, chunk in enumerate(chunks):
        lines.append(f"{'private ' if private else ''}def {name}Chunk{index} : ByteArray :=")
        lines.append("  ⟨#[")
        for row in range(0, len(chunk), 24):
            part = ", ".join(f"0x{b:02x}" for b in chunk[row:row + 24])
            lines.append(f"    {part},")
        if lines[-1].endswith(","):
            lines[-1] = lines[-1][:-1]
        lines.append("  ]⟩")
        lines.append("")
    term = " ++\n  ".join(f"{name}Chunk{i}" for i in range(len(chunks)))
    return lines, term


def render_jump_table(theorem: str, code_term: str, code: bytes, doc: str) -> list[str]:
    dests = jump_dests(code)
    lines = [f"/-- {doc} -/", f"@[valid_jumps] theorem {theorem} :",
             f"    Ethereum.EVM.D_J {code_term} 0", "      = #["]
    row: list[str] = []
    for d in dests:
        row.append(f"⟨{d}⟩")
        if len(row) == 12:
            lines.append("      " + ", ".join(row) + ",")
            row = []
    if row:
        lines.append("      " + ", ".join(row))
    elif lines[-1].endswith(","):
        lines[-1] = lines[-1][:-1]
    lines += ["      ] := by", "  native_decide", ""]
    return lines


def render_bytecode_lean(namespace: str, prefix: str, name: str, runtime: bytes, creation: bytes | None,
                         build: dict | None, chunk_size: int) -> str:
    body, meta = split_metadata(runtime)
    header = [f"/-!", f"# {name} bytecode", "",
              "Generated by `scripts/scaffold.py lean` from `runtime.hex` and `creation.hex`; do not edit."]
    if build:
        header.append(f"Compiler: solc `{build['compiler']['version']}`, main source `{build['main']}`, "
                      f"settings `{json.dumps(build['settings'], sort_keys=True)}`.")
    header.append(f"Runtime: {len(runtime)} bytes ({len(body)} executable, {len(meta)} metadata)"
                  + (f"; creation: {len(creation)} bytes." if creation is not None else "."))
    if build and build.get("immutables"):
        sites = "; ".join(f"`{i['name']}` at {i['offsets']}" for i in build["immutables"])
        header.append(f"`{prefix}Bytecode` is the runtime template with zeroed immutable sites: {sites} "
                      "(see `Immutables.lean`).")
    header.append("-/")
    out = ["import Ethereum.Semantics", "import Reasoning.JumpDest", "", *header, "",
           "open Ethereum Ethereum.EVM", "", f"namespace {namespace}", "",
           "set_option maxRecDepth 50000000", "set_option maxHeartbeats 0", ""]
    chunk_lines, term = render_bytes(f"{prefix}Runtime", runtime, chunk_size)
    out += chunk_lines
    out += [f"def {prefix}Bytecode : ByteArray :=", f"  {term}", ""]
    out += render_jump_table("validJumps", f"{prefix}Bytecode", runtime,
                             f"The `JUMPDEST` set of `{prefix}Bytecode`, computed from the deployed runtime bytecode.")
    if creation is not None:
        chunk_lines, term = render_bytes(f"{prefix}Creation", creation, chunk_size)
        out += chunk_lines
        out += [f"def {prefix}CreationBytecode : ByteArray :=", f"  {term}", ""]
        out += render_jump_table("creationValidJumps", f"{prefix}CreationBytecode", creation,
                                 f"The `JUMPDEST` set of `{prefix}CreationBytecode`, computed from the creation bytecode.")
    out += [f"end {namespace}", ""]
    return "\n".join(out)


def selector_table(directory: Path, name: str, build: dict | None) -> list[tuple[str, bytes]]:
    """(canonical signature, 4-byte selector) for every external function, in table order."""
    if build and build.get("methodIdentifiers"):
        pairs = [(sig, bytes.fromhex(sel)) for sig, sel in build["methodIdentifiers"].items()]
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
           "each Solm transition's signature string to its entry (`transitionSigStr … = \"…\"`) is added by",
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
    out = ["import Solm.Syntax", "import EVM.Types", "",
           "/-!", f"# {name} immutable valuation and offset table", "",
           "Generated by `scripts/scaffold.py lean` from solc's `evm.deployedBytecode.immutableReferences`",
           f"(solc `{build['compiler']['version']}`).  `runtime.hex` is the runtime template with every",
           "immutable site zeroed; the constructor patches the sites in the order listed below, which is",
           "the order the creation code writes them.", "-/", "",
           "open Solm ABI", "", f"namespace {namespace}.Immutables", "",
           "/-- A valuation of the contract's immutables, as the runtime proofs consume them. -/",
           f"structure {name}Immutables where"]
    for imm in imms:
        out.append(f"  {imm['name']} : {lean_field_type(imm['type'])}")
    out += ["", "/-- solc `immutableReferences`: each immutable's Solm name and patch offsets, in the order the",
            "    constructor writes them. -/",
            "def immutableReferences : List (Ident × List Nat) :="]
    rows = [f"(\"{imm['name']}\", [{', '.join(str(o) for o in imm['offsets'])}])" for imm in imms]
    out.append("  [ " + ",\n    ".join(rows) + " ]")
    out += ["", f"end {namespace}.Immutables", ""]
    return "\n".join(out)


def render_immutable_code_lean(namespace: str, module: str) -> str:
    return "\n".join([
        f"import {module}.Bytecode", f"import {module}.Immutables", "import Reasoning.Immutables", "",
        "/-!", "The patch sites of the deployed runtime template, keyed by Solm immutable name.  Generated",
        "summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them",
        "from a Solm immutables store.", "-/", "",
        "open Reasoning.Immutables", f"open {namespace}.Immutables", "", f"namespace {namespace}", "",
        "/-- Patch sites in the deployed runtime template. -/",
        "def immutableLayout : Layout :=",
        "  ⟨immutableReferences.flatMap (fun (name, sites) =>",
        "    sites.map (fun offset => (offset, 32, name)))⟩", "",
        f"end {namespace}", ""])


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
    runtime = read_bytecode(directory / "runtime.hex")
    creation = read_bytecode(directory / "creation.hex") if (directory / "creation.hex").exists() else None
    write_file(directory / "Bytecode.lean",
               render_bytecode_lean(namespace, prefix, name, runtime, creation, build, args.chunk_size),
               args.force)
    table = selector_table(directory, name, build)
    write_file(directory / "Selectors.lean", render_selectors_lean(namespace, prefix, name, table),
               args.force)
    if build and build.get("immutables"):
        write_file(directory / "Immutables.lean", render_immutables_lean(namespace, name, build), args.force)
        write_file(directory / "ImmutableCode.lean", render_immutable_code_lean(namespace, module), args.force)
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
    bytecode_import = f"{module}.Bytecode"
    sites = None
    imports = [bytecode_import]
    layout_term = None
    if build and build.get("immutables"):
        sites = immutable_sites(build, runtime)
        imports.append(f"{module}.ImmutableCode")
        layout_term = f"{namespace}.immutableLayout"
    units = rd.generate_unit_records(runtime, prefix, f"{namespace}.{prefix}Bytecode", False, False,
                                     args.max_summary_instructions, False, sites, layout_term, False)
    paths = rd.write_outputs(directory / "RuntimeBlocks.lean", prefix, imports, units, args.shard_size,
                             False, f"{namespace}.{prefix}Bytecode", None, sites, runtime, layout_term, False)
    print(f"wrote {len(paths)} runtime summary shards ({len(units)} units) and RuntimeBlocks.index")
    creation_path = directory / "creation.hex"
    if creation_path.exists() and not args.no_creation:
        creation = read_bytecode(creation_path)
        units = rd.generate_unit_records(creation, f"{prefix}Creation", f"{namespace}.{prefix}CreationBytecode",
                                         False, False, args.max_summary_instructions, True, None, None, False)
        paths = rd.write_outputs(directory / "CreationBlocks.lean", f"{prefix}Creation", [bytecode_import],
                                 units, args.shard_size, True, f"{namespace}.{prefix}CreationBytecode")
        print(f"wrote {len(paths)} creation summary shards ({len(units)} units) and CreationBlocks.index")
    return 0


# --------------------------------------------------------------------------------------------
# check

def lean_jump_table(text: str, theorem: str) -> list[int] | None:
    match = re.search(re.escape(theorem) + r"\s*:.*?#\[(.*?)\]\s*:=", text, re.S)
    if not match:
        return None
    return [int(x) for x in re.findall(r"⟨(\d+)⟩", match.group(1))]


def lean_selector_table(text: str) -> list[tuple[str, bytes]]:
    out: list[tuple[str, bytes]] = []
    for match in re.finditer(r"\|\s*(?:\d+|_)\s*=>\s*⟨#\[([^\]]*)\]⟩\s*--\s*(\S+)", text):
        out.append((match.group(2), bytes(int(b, 16) for b in match.group(1).split(","))))
    return out


def cmd_check(args: argparse.Namespace) -> int:
    directory: Path = args.dir
    name = contract_name(directory, args.contract)
    build_path = find_build(directory, name)
    build = load_json(build_path) if build_path else None
    prefix = args.prefix or lower_camel(name)
    failures: list[str] = []
    ok: list[str] = []

    runtime = read_bytecode(directory / "runtime.hex")
    creation = read_bytecode(directory / "creation.hex") if (directory / "creation.hex").exists() else None
    bytecode_lean = directory / "Bytecode.lean"
    if bytecode_lean.exists():
        text = bytecode_lean.read_text(encoding="utf-8")
        for term, data, theorem in ((f"{prefix}Bytecode", runtime, "validJumps"),
                                    (f"{prefix}CreationBytecode", creation, "creationValidJumps")):
            if data is None:
                continue
            try:
                lean_bytes = read_bytecode(bytecode_lean, term)
            except ValueError as error:
                failures.append(f"{term}: {error}")
                continue
            (ok if lean_bytes == data else failures).append(
                f"{term} {'matches' if lean_bytes == data else 'differs from'} the hex artifact")
            table = lean_jump_table(text, theorem)
            if table is None:
                failures.append(f"{theorem}: theorem not found in Bytecode.lean")
            else:
                expected = jump_dests(data)
                (ok if table == expected else failures).append(
                    f"{theorem}: {'matches' if table == expected else 'differs from'} the JUMPDEST scan")
    else:
        failures.append("Bytecode.lean is missing")

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

    if build and build.get("immutables"):
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
        p.add_argument("--main", help="main source unit, relative to the sources root")
        p.add_argument("--sources-root", default=None,
                       help="directory holding the .sol closure (default: contracts/ if present, else .)")
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
        p.add_argument("--chunk-size", type=int, default=512)
        p.add_argument("--force", action="store_true", help="overwrite existing generated files")

    def blocks_args(p: argparse.ArgumentParser) -> None:
        p.add_argument("--shard-size", type=int, default=20)
        p.add_argument("--max-summary-instructions", type=int, default=rd.MAX_SUMMARY_INSTRUCTIONS)
        p.add_argument("--no-creation", action="store_true")

    p = sub.add_parser("compile", help="run solc and write the artifacts"); common(p); compile_args(p)
    p = sub.add_parser("lean", help="write Bytecode/Selectors/Immutables modules"); common(p); lean_args(p)
    p = sub.add_parser("blocks", help="generate block summaries"); common(p); lean_args(p); blocks_args(p)
    p = sub.add_parser("check", help="verify artifacts against the Lean files"); common(p); lean_args(p)
    p = sub.add_parser("all", help="compile, lean, blocks, check"); common(p); compile_args(p); lean_args(p); blocks_args(p)
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
    for step in (cmd_compile, cmd_lean, cmd_blocks, cmd_check):
        code = step(args)
        if code:
            return code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

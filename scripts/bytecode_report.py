#!/usr/bin/env python3
"""Write the bytecode report for one contract directory.

The report is the ground truth a proving agent otherwise derives by hand: sizes, an opcode
census, the compiled dispatcher (guard, size check, pivots, selector arms, fallthroughs), the
JUMPDEST set, every runtime basic block, and, when ``<Name>.build.json`` (written by
``scaffold.py compile``) carries a source map, the source statement of each block, the per-function
pc ranges, and the internal routine entries and call sites.

Example:
  scripts/bytecode_report.py Examples/TinyImmutable --output Examples/TinyImmutable/REPORT.md
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

from bytecode_io import read_bytecode
from evm_tools import (AstFunction, Dispatcher, SourceMapEntry, ast_functions, census,
                       code_and_blocks, decode_source_map, dispatcher, function_pcs,
                       innermost_function, jump_dests, load_build, method_names, parse_src,
                       routine_boundaries, selector, split_metadata, abi_signatures)
from evm_tools import walk as walk_nodes
from generate_rd_blocks import Instruction


def find_build(directory: Path) -> Path | None:
    candidates = sorted(directory.glob("*.build.json"))
    return candidates[0] if candidates else None


def find_abi(directory: Path) -> Path | None:
    candidates = sorted(directory.glob("*.abi.json"))
    return candidates[0] if candidates else None


def fmt_ins(ins: Instruction) -> str:
    if ins.argument is not None and ins.width:
        return f"{ins.pc}: {ins.name.upper()} 0x{ins.argument:0{2 * ins.width}x}"
    return f"{ins.pc}: {ins.name.upper()}"


class SourceView:
    """Source text lookup for source-map entries (real files and solc generated sources)."""

    def __init__(self, directory: Path, build: dict | None, which: str) -> None:
        self.texts: dict[int, str] = {}
        self.names: dict[int, str] = {}
        if build is None:
            return
        root = directory / build.get("sourcesRoot", ".")
        for src in build.get("sources", []):
            path = root / src["path"]
            self.names[src["id"]] = src["path"]
            if path.exists():
                self.texts[src["id"]] = path.read_text(encoding="utf-8", errors="replace")
        for gen in build.get("generatedSources", {}).get(which, []):
            self.names[gen["id"]] = gen["name"]
            self.texts[gen["id"]] = gen.get("contents", "")

    def yul_function(self, entry: SourceMapEntry) -> str | None:
        """The generated-source Yul function enclosing `entry`, if the entry is in a generated source."""
        text = self.texts.get(entry.file)
        name = self.names.get(entry.file, "")
        if text is None or not name.endswith(".yul"):
            return None
        raw = text.encode("utf-8")
        best = None
        for m in re.finditer(rb"function\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(", raw):
            if m.start() <= entry.start:
                best = m.group(1).decode()
            else:
                break
        return f"{name}:{best}" if best else name

    def snippet(self, entry: SourceMapEntry, width: int = 72) -> str:
        text = self.texts.get(entry.file)
        if text is None or entry.start < 0:
            return ""
        # solc source maps count UTF-8 bytes.
        raw = text.encode("utf-8")[entry.start:entry.start + entry.length]
        line = " ".join(raw.decode("utf-8", errors="replace").split())
        return line if len(line) <= width else line[:width - 1] + "…"


def block_entry(entries: list[SourceMapEntry], index_of: dict[int, int],
                block: list[Instruction]) -> SourceMapEntry | None:
    """The most frequent source-map entry of a block (its statement), if mapped."""
    counter: Counter[tuple[int, int, int]] = Counter()
    first: dict[tuple[int, int, int], SourceMapEntry] = {}
    for ins in block:
        k = index_of.get(ins.pc)
        if k is None or k >= len(entries):
            continue
        e = entries[k]
        if e.start < 0:
            continue
        key = (e.start, e.length, e.file)
        counter[key] += 1
        first.setdefault(key, e)
    if not counter:
        return None
    return first[counter.most_common(1)[0][0]]


def render(directory: Path, name: str, build: dict | None, abi: list[dict] | None,
           full_creation: bool) -> str:
    out: list[str] = []
    runtime = read_bytecode(directory / "runtime.hex")
    creation_path = directory / "creation.hex"
    creation = read_bytecode(creation_path) if creation_path.exists() else None
    body, instructions, bblocks = code_and_blocks(runtime)
    _, metadata = split_metadata(runtime)
    index_of = {ins.pc: k for k, ins in enumerate(instructions)}

    out.append(f"# {name} bytecode report")
    out.append("")
    out.append("Derived from `runtime.hex`/`creation.hex` by `scripts/bytecode_report.py`; a development "
               "aid, not a proof artifact.")
    out.append("")
    out.append(f"- runtime: {len(runtime)} bytes ({len(body)} executable + {len(metadata)} metadata), "
               f"{len(instructions)} instructions, {len(bblocks)} basic blocks")
    if creation is not None:
        cbody, cinstrs, cblocks = code_and_blocks(creation)
        out.append(f"- creation: {len(creation)} bytes ({len(cbody)} executable), "
                   f"{len(cinstrs)} instructions, {len(cblocks)} basic blocks")
    if build is not None:
        comp = build.get("compiler", {})
        out.append(f"- compiler: solc {comp.get('version', '?')}; settings "
                   f"`{json.dumps(build.get('settings', {}), sort_keys=True)}`")
        imm = build.get("immutableReferences") or {}
        if imm:
            out.append(f"- immutables: " + ", ".join(
                f"`{i['name']}` (AST id {i['id']}) at offsets {i['offsets']}" for i in build.get("immutables", [])))
    out.append("")

    # Census
    out.append("## Opcode census (runtime)")
    out.append("")
    counts = census(instructions)
    if counts:
        out.append("| opcode | count |")
        out.append("|---|---|")
        for op, n in sorted(counts.items()):
            out.append(f"| {op} | {n} |")
    else:
        out.append("(no state-touching opcodes)")
    out.append("")

    # Names for selectors
    sel_names: dict[int, str] = {}
    if build is not None and build.get("methodIdentifiers"):
        sel_names = method_names(build["methodIdentifiers"])
    elif abi is not None:
        for sig in abi_signatures(abi):
            sel_names[int.from_bytes(selector(sig), "big")] = sig

    # Source maps
    entries: list[SourceMapEntry] = []
    functions: list[AstFunction] = []
    view = SourceView(directory, build, "runtime")
    srcmap_note = ""
    if build is not None and build.get("sourceMap", {}).get("runtime"):
        entries = decode_source_map(build["sourceMap"]["runtime"])
        # solc maps one entry per assembly instruction; the trailing INVALID data separator and
        # anything after it are unmapped.
        if len(entries) > len(instructions):
            srcmap_note = (f"source map has {len(entries)} entries but the executable runtime has "
                           f"{len(instructions)} instructions; annotations disabled")
            entries = []
        else:
            if len(entries) < len(instructions):
                srcmap_note = (f"source map covers {len(entries)} of {len(instructions)} runtime "
                               f"instructions (the tail from pc {instructions[len(entries)].pc} is unmapped)")
            units = [u for u in build.get("ast", {}).values() if isinstance(u, dict)]
            functions = ast_functions(units)
            # via-IR maps compiler helpers to the whole contract range: label them as helpers
            for unit in units:
                for c in (n for n in walk_nodes(unit) if n.get("nodeType") == "ContractDefinition"):
                    s, l, f = parse_src(c["src"])
                    functions.append(AstFunction(f"{c['name']} helper", "helper", c["name"], s, l, f))

    # Dispatcher
    disp: Dispatcher = dispatcher(instructions)
    out.append("## Dispatcher (runtime)")
    out.append("")
    out.append(f"- callvalue guard: {'global, before dispatch' if disp.callvalue_guard else 'none before dispatch (per-function or payable)'}")
    if disp.calldatasize_check:
        out.append(f"- short-calldata check: JUMPI at pc {disp.calldatasize_check[0]} → pc {disp.calldatasize_check[1]}")
    else:
        out.append("- short-calldata check: not recognised")
    if disp.pivots:
        out.append("")
        out.append("| pivot pc | PUSH4 | compare | taken → pc |")
        out.append("|---|---|---|---|")
        for p in disp.pivots:
            out.append(f"| {p.pc} | 0x{p.selector:08x} | {p.kind.upper()} | {p.target} |")
    out.append("")
    out.append("| compare pc | selector | signature | arm → pc | source function |")
    out.append("|---|---|---|---|---|")
    for a in disp.arms:
        label = ""
        if entries:
            k = index_of.get(a.target)
            fn = innermost_function(functions, entries[k]) if k is not None and k < len(entries) else None
            label = fn.label if fn else ""
        out.append(f"| {a.pc} | 0x{a.selector:08x} | {sel_names.get(a.selector, '?')} | {a.target} | {label} |")
    unmatched = [s for s in sel_names if s not in {a.selector for a in disp.arms}]
    if unmatched:
        out.append("")
        out.append("ABI functions without a selector arm (served by the fallback, or not dispatched): " +
                   ", ".join(f"`{sel_names[s]}`" for s in sorted(unmatched)))
    if disp.fallthroughs:
        out.append("")
        out.append("Chain fallthroughs (after the last compare of each chain): " +
                   "; ".join(f"pc {pc} → {desc}" for pc, desc in disp.fallthroughs))
    out.append("")

    # Jump dests
    dests = jump_dests(runtime)
    out.append(f"## Jump destinations (runtime, {len(dests)})")
    out.append("")
    out.append(", ".join(str(d) for d in dests))
    out.append("")

    # Functions and routines (need source map)
    if srcmap_note:
        out.append(f"> {srcmap_note}")
        out.append("")
    if entries:
        pcs = function_pcs(instructions, entries, functions)
        out.append("## Source functions → runtime pcs")
        out.append("")
        out.append("| function | kind | pcs | first JUMPDEST | blocks |")
        out.append("|---|---|---|---|---|")
        block_start = {b[0].pc: i for i, b in enumerate(bblocks)}
        for label, fpcs in sorted(pcs.items(), key=lambda kv: min(kv[1])):
            fn = next((f for f in functions if f.label == label), None)
            kind = fn.kind if fn else ""
            first_dest = next((p for p in fpcs if instructions[index_of[p]].opcode == 0x5B), None)
            blks = sorted({instructions[index_of[p]].pc for p in fpcs if p in block_start})
            rng = f"{min(fpcs)}–{max(fpcs)} ({len(fpcs)})"
            out.append(f"| {label} | {kind} | {rng} | {first_dest if first_dest is not None else ''} | "
                       f"{', '.join(str(b) for b in blks)} |")
        out.append("")
        routines = routine_boundaries(instructions, entries, functions)
        for callee in list(routines.entries):
            if routines.entries[callee] is None and callee in index_of:
                routines.entries[callee] = view.yul_function(entries[index_of[callee]])
        for call in routines.calls:
            if call.function is None and call.jump_pc in index_of:
                call.function = view.yul_function(entries[index_of[call.jump_pc]])
        out.append("## Internal routines (source-map jump tags)")
        out.append("")
        out.append(f"- `i`-tagged call jumps: {len(routines.calls)}; `o`-tagged return jumps: {len(routines.returns)}")
        if routines.entries:
            out.append("")
            out.append("| callee entry pc | function at entry | call sites (jump pc ← caller function) |")
            out.append("|---|---|---|")
            for callee, label in sorted(routines.entries.items()):
                sites = [c for c in routines.calls if c.callee == callee]
                desc = ", ".join(f"{c.jump_pc} ← {c.function or '?'}" for c in sites)
                out.append(f"| {callee} | {label or '?'} | {desc} |")
        unknown = [c for c in routines.calls if c.callee is None]
        if unknown:
            out.append("")
            out.append("Call jumps whose target is not a preceding PUSH (dynamic): " +
                       ", ".join(str(c.jump_pc) for c in unknown))
        out.append("")

    # Blocks
    out.append("## Runtime basic blocks")
    out.append("")
    out.append("```text")
    for block in bblocks:
        line = " | ".join(fmt_ins(ins) for ins in block)
        notes: list[str] = []
        kinds = [ins.name.upper() for ins in block
                 if ins.opcode in (0x54, 0x55, 0x20, 0xF1, 0xFA, 0xF4, 0xF0, 0xF5, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4,
                                   0x3B, 0xFF, 0xFE, 0x5C, 0x5D)]
        if kinds:
            notes.append(",".join(kinds))
        if entries:
            e = block_entry(entries, index_of, block)
            if e is not None:
                fn = innermost_function(functions, e)
                where = fn.label if fn else (view.yul_function(e) or view.names.get(e.file, f"src {e.file}"))
                snip = view.snippet(e)
                notes.append(f"{where}: {snip}" if snip else where)
        out.append(line + (f"    ;; {' ;; '.join(notes)}" if notes else ""))
    out.append("```")
    out.append("")

    # Creation
    if creation is not None:
        cbody, cinstrs, cblocks = code_and_blocks(creation)
        cdests = jump_dests(creation)
        out.append("## Creation bytecode")
        out.append("")
        out.append(f"- {len(cdests)} jump destinations: " + ", ".join(str(d) for d in cdests))
        copy_sites = [ins for ins in cinstrs if ins.opcode == 0x39]
        out.append(f"- CODECOPY sites: {', '.join(str(i.pc) for i in copy_sites) or 'none'}")
        if full_creation:
            cview = SourceView(directory, build, "creation")
            centries: list[SourceMapEntry] = []
            if build is not None and build.get("sourceMap", {}).get("creation"):
                centries = decode_source_map(build["sourceMap"]["creation"])
                if len(centries) > len(cinstrs):
                    centries = []
            cindex = {ins.pc: k for k, ins in enumerate(cinstrs)}
            out.append("")
            out.append("```text")
            for block in cblocks:
                line = " | ".join(fmt_ins(ins) for ins in block)
                note = ""
                if centries:
                    e = block_entry(centries, cindex, block)
                    if e is not None:
                        fn = innermost_function(functions, e)
                        where = fn.label if fn else cview.names.get(e.file, f"src {e.file}")
                        snip = cview.snippet(e)
                        note = f"    ;; {where}: {snip}" if snip else f"    ;; {where}"
                out.append(line + note)
            out.append("```")
        out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path, help="contract directory holding runtime.hex")
    parser.add_argument("--name", help="contract name (default: from *.build.json or the directory)")
    parser.add_argument("--output", "-o", type=Path, help="write the Markdown report here (default: stdout)")
    parser.add_argument("--full-creation", action="store_true",
                        help="also list every creation basic block")
    args = parser.parse_args(argv)
    directory: Path = args.directory
    if not (directory / "runtime.hex").exists():
        parser.error(f"{directory} has no runtime.hex")
    build_path = find_build(directory)
    build = load_build(build_path) if build_path else None
    abi = None
    abi_path = find_abi(directory)
    if abi_path:
        abi = json.loads(abi_path.read_text(encoding="utf-8"))
    name = args.name or (build or {}).get("contract") or directory.name
    text = render(directory, name, build, abi, args.full_creation)
    if args.output:
        args.output.write_text(text + "\n", encoding="utf-8")
        print(args.output)
    else:
        sys.stdout.write(text + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

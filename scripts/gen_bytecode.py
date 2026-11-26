#!/usr/bin/env python3
"""Write a contract's bytecode file (`<Dir>/Bytecode.lean`): its bytecode and its disassembly.

Usage:
    gen_bytecode.py --dir <Dir> [--module <Module>] [--contract <Name>] [--prefix <prefix>]
                   [--creation] [--layout <term> --layout-import <module>] [--force]
                   [--constant-namespace <ns>] [--blocks-namespace <ns>]
                   [--valid-jumps <name>] [--provenance <file>]

`scaffold.py lean` writes the same files.  Use this script to regenerate one file, or for a
contract whose immutable layout is defined by hand (`--layout`).  `--creation` reads
`creation.hex` and writes `<Dir>/CreationBytecode.lean`.

The file defines the bytecode as a `ByteArray` literal and, in the namespace `<Module>.Bytecode`
(`<Module>.CreationBytecode`), its sections and the theorems the block proofs use.  See
`Reasoning/Disassembly/Facts.lean` for its structure.

When the build JSON lists solc immutables, or `--layout` is given, the literal has zeros at the
immutable sites and the theorems are about the layout's runtime code.  Creation code and Vyper
runtimes with immutables get theorems about the code followed by arbitrary data.

The bytes are copied into the file, so it has to be regenerated when the hex file changes
(`scaffold.py check` reports a mismatch).  Standard library only.
"""

from __future__ import annotations

import argparse
import json
import sys
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bytecode_io import parse_bytecode_text  # noqa: E402

WIDTH = 96
BYTES_PER_LINE = 16
OPENS = "open Ethereum Ethereum.EVM EVM.Disassembly Reasoning.Disassembly Reasoning.Immutables"


def solc_immutable_names(build: dict | None) -> list[str]:
    """The names of the solc immutables of the build JSON, in its order (none for Vyper)."""
    if not build or build.get("compiler", {}).get("kind") == "vyper":
        return []
    names = []
    for imm in build.get("immutables") or []:
        if any(n != 32 for n in imm.get("lengths", [32])):
            sys.exit(f"immutable {imm['name']}: site length other than 32")
        names.append(imm["name"])
    return names


def first_appearance(build: dict) -> list[str]:
    """Immutable names in order of first appearance among the sites.  This is the default
    numbering in a bytecode file (`Reasoning.Disassembly.keyOrder`)."""
    sites = build.get("layoutSites") or [(off, imm["name"]) for imm in build["immutables"]
                                         for off in imm["offsets"]]
    out: list[str] = []
    for _, key in sites:
        if key not in out:
            out.append(key)
    return out


def build_sites(build: dict) -> list[int]:
    """The offset of every solc immutable site of the build JSON."""
    return [off for imm in build.get("immutables") or [] for off in imm["offsets"]]


def lean_string_list(names: list[str]) -> str:
    return "[" + ", ".join(json.dumps(n) for n in names) + "]"


def ends_in_short_push(code: bytes) -> bool:
    """Whether the last instruction is a push with missing immediate bytes."""
    pc = 0
    while pc < len(code):
        op = code[pc]
        pc += 1 + (op - 0x5F if 0x60 <= op <= 0x7F else 0)
    return pc > len(code)


def relative(name: str, namespace: str) -> str:
    """``name`` without the ``namespace`` prefix."""
    return name[len(namespace) + 1:] if name.startswith(namespace + ".") else name


def fit(head: str, tail: str, indent: str = "  ") -> list[str]:
    """``head tail`` on one line if it fits in 100 characters, otherwise on two."""
    if len(head) + 1 + len(tail) <= 100:
        return [f"{head} {tail}"]
    return [head, indent + tail]


def bytes_literal(code: bytes) -> list[str]:
    """The lines of the `⟨#[…]⟩` literal."""
    if not code:
        return ["⟨#[]⟩"]
    rows = [", ".join(f"0x{b:02x}" for b in code[k:k + BYTES_PER_LINE])
            for k in range(0, len(code), BYTES_PER_LINE)]
    return ["⟨#["] + [f"  {row}," for row in rows[:-1]] + [f"  {rows[-1]}]⟩"]


def render(namespace: str, name: str, qual: str, hex_file: str, code: bytes, creation: bool,
           tail: str | None, layout: str | None, layout_import: str | None,
           names: list[str] | None, blocks_namespace: str | None, valid_jumps: str | None,
           provenance: str | None) -> str:
    """The text of a bytecode file for ``code``.  ``names`` is the order of the immutables, or
    ``None`` for the default order."""
    ns = f"{namespace}.{'CreationBytecode' if creation else 'Bytecode'}"
    what = "creation" if creation else "runtime"
    para = (f"`{name}`'s {what} bytecode and its disassembly, see "
            f"`Reasoning/Disassembly/Facts.lean`. The bytes are those of `{hex_file}`"
            + (" with the immutable sites zeroed." if layout else "."))
    if tail == "tail":
        para += " The theorems hold for the code followed by any `tail`, i.e. the constructor arguments."
    elif tail is not None:
        para += f" The theorems hold for the code followed by any `{tail}`, i.e. its immutables."
    doc = textwrap.wrap("/-! " + para, WIDTH, break_long_words=False, break_on_hyphens=False)
    if provenance:
        doc += ["", *provenance.strip("\n").splitlines()]
    doc[-1] += " -/"
    out = []
    if layout:
        out.append(f"import {layout_import}")
    out += ["import Reasoning.Disassembly.Facts", "", *doc, ""]
    parts = ns.split(".")
    if len(set(parts)) < len(parts):  # e.g. `Benchmarks.EAS.EAS`
        out += ["set_option linter.dupNamespace false", ""]
    const_doc = (f"/-- The {what} bytecode." + (" Immutable sites are zero." if layout else "")
                 + " -/")
    literal = bytes_literal(code)
    out += ["set_option maxRecDepth 100000 in", const_doc,
            f"def {qual} : ByteArray := {literal[0]}", *literal[1:], "",
            f"namespace {ns}", "", OPENS, ""]
    # `bytecode_io.parse_bytecode_file` needs the full name of the layout, so only the constant
    # is shortened
    qual = relative(qual, namespace)
    sites = "[]"
    if layout:
        out += ["/-- The layout key of each immutable. -/",
                "def names : List String := "
                + (lean_string_list(names) if names else f"eval% keyOrder {layout}.sites"), ""]
        sites = f"(siteNumbers {layout}.sites names)"
    out += [
        "/-- The sections as a search tree, computed when this file is elaborated. -/",
        "noncomputable def tree : EVM.Disassembly.Tree :=",
        *fit("  eval% EVM.Disassembly.Tree.ofSections", f"(sectionsOf {qual} {sites})", "    "),
        "",
        f"def bytes : List UInt8 := {qual}.data.toList",
        "",
        "/-- The sections with their offsets. -/",
        "noncomputable def sections : List (Nat × List Instr) := tree.flat []",
        "",
        "/-- The sections are the disassembly of the bytes. -/",
        "theorem check : Checked bytes sections := by decide +kernel",
        "",
    ]
    if valid_jumps:
        out += [
            "/-- Membership in `D_J` as a lookup in `tree`, for the `jump_dest` tactic. -/",
            f"@[valid_jumps] theorem _root_.{valid_jumps} (t : UInt256) :",
            f"    (D_J {qual} 0).contains t =",
            "      ((tree.get? t.toNat).map startsJD).getD false :=",
            "  contains_eq_tree check t",
            "",
        ]
    zero = "(fun _ => ⟨0⟩)"
    if not layout:
        out += [
            "/-- The bytecode has no immutables to fill in. -/",
            *fit("theorem code_eq :", f"{qual} = filled bytes {zero} sections :=", "    "),
            "  eq_filled (by decide +kernel) _",
            "",
        ]
    if tail:
        last = ends_in_short_push(code)
        out += [
            "/-- Sections before this offset end inside the code. -/",
            *fit("def lim : Nat :=", f"eval% limOf (sectionsOf {qual} []) {qual}.size"),
            "",
            "theorem inside : tailCheck sections bytes.length lim = true := by decide +kernel",
            "",
            f"/-- A section found in the tree decodes in the code followed by any `{tail}`. -/",
            f"theorem decodes_code ({tail} : ByteArray) {{t : Nat}} {{s : List Instr}} (h : tree.get? t = some s)",
            "    (ht : t < lim := by decide) :",
            f"    Decodes ({qual} ++ {tail}) {zero} (UInt256.ofNat t) s :=",
            f"  decodes_appended_tree check code_eq inside {tail} h ht",
            "",
            "/-- The offset of a section that starts with a `JUMPDEST` is a valid jump destination of the",
            f"code followed by any `{tail}`. -/",
            f"theorem jumpdest_code ({tail} : ByteArray) {{t : Nat}} {{s : List Instr}} (h : tree.get? t = some s)",
            "    (hjd : startsJD s = true) (ht : t < 2 ^ 256 := by decide) :",
            f"    (D_J ({qual} ++ {tail}) 0).contains (UInt256.ofNat t) = true :=",
            f"  jumpdest_appended_tree check code_eq {tail} h hjd ht",
            "",
        ]
        if last:
            out += [
                "/-- The section at `lim` ends in a truncated push. The instructions before it decode in the",
                f"code followed by any `{tail}`. -/",
                f"theorem decodes_last ({tail} : ByteArray) :",
                f"    Decodes ({qual} ++ {tail}) {zero} (UInt256.ofNat lim)",
                *fit("      (((tree.get? lim).getD []).take",
                     f"(eval% lastCount (sectionsOf {qual} []) lim)) :=", "        "),
                f"  decodes_last_tree check code_eq inside (by decide +kernel) {tail}",
                "",
            ]
    else:
        code_term = f"({layout}.runtime {qual} immWords)" if layout else qual
        binder = "(immWords : String → UInt256) " if layout else ""
        sigma = "(immσ names immWords)" if layout else zero
        eq = "(code_eq immWords)" if layout else "code_eq"
        if layout:
            out += [
                "/-- The sites of the layout are the immutables of the sections. -/",
                *fit("theorem code_check :", f"codeCheck {layout}.sites sections names = true := by decide +kernel", "    "),
                "",
                "/-- The runtime code is the template with its immutables filled in. -/",
                f"theorem code_eq {binder}:",
                f"    {code_term} = filled bytes {sigma} sections :=",
                "  runtime_eq_filled check code_check immWords",
                "",
            ]
        out += [
            "/-- A section found in the tree decodes at its offset. -/",
            f"theorem decodes_code {binder}{{t : Nat}} {{s : List Instr}} (h : tree.get? t = some s) :",
            f"    Decodes {code_term} {sigma} (UInt256.ofNat t) s :=",
            f"  decodes_tree check {eq} h",
            "",
            "/-- The offset of a section that starts with a `JUMPDEST` is a valid jump destination. -/",
            f"theorem jumpdest_code {binder}{{t : Nat}} {{s : List Instr}} (h : tree.get? t = some s)",
            "    (hjd : startsJD s = true) (ht : t < 2 ^ 256 := by decide) :",
            f"    (D_J {code_term} 0).contains (UInt256.ofNat t) = true :=",
            f"  jumpdest_tree check {eq} h hjd ht",
            "",
        ]
    if layout:
        b = f"_root_.{blocks_namespace}"
        r = blocks_namespace
        out += [
            "/-- The size of the template. -/",
            *fit(f"theorem {b}.immutableTemplate_size :", f"{qual}.size = eval% {qual}.size := by", "    "),
            "  decide +kernel",
            "",
            *fit(f"theorem {b}.immutableLayout_sites :", f"{layout}.sites = eval% {layout}.sites := by decide", "    "),
            "",
            *fit(f"theorem {b}.immutableLayout_inBounds :", f"{layout}.inBounds {qual} = true := by", "    "),
            f"  simp only [Layout.inBounds, {r}.immutableTemplate_size, {r}.immutableLayout_sites]",
            "  decide",
            "",
            *fit(f"theorem {b}.immutableTemplate_size64 :", f"{qual}.size < 2 ^ 64 := by", "    "),
            f"  rw [{r}.immutableTemplate_size]; decide",
            "",
            f"theorem {b}.immutableRuntime_size (immWords : String → Ethereum.UInt256) :",
            f"    ({layout}.runtime {qual} immWords).size = {qual}.size :=",
            f"  Layout.runtime_size_of_bounds {r}.immutableLayout_inBounds",
            "",
        ]
    out += [f"end {ns}", ""]
    return "\n".join(out)


def bytecode_file_path(directory: Path, creation: bool = False) -> Path:
    """`Bytecode.lean` or `CreationBytecode.lean` in ``directory``."""
    return directory / ("CreationBytecode.lean" if creation else "Bytecode.lean")


def zero_sites(code: bytes, sites: list[int]) -> bytes:
    """``code`` with the 32 bytes at every immutable site set to zero."""
    out = bytearray(code)
    for off in sites:
        if not (1 <= off and off + 32 <= len(out)):
            sys.exit(f"immutable site {off}: outside the code")
        out[off:off + 32] = bytes(32)
    return bytes(out)


def render_bytecode_file(directory: Path, module: str, name: str, prefix: str,
                         build: dict | None, creation: bool = False,
                         blocks_namespace: str | None = None, layout: str | None = None,
                         layout_import: str | None = None, namespace: str | None = None,
                         constant_namespace: str | None = None, valid_jumps: str | None = None,
                         provenance: str | None = None) -> str:
    """The text of the directory's runtime (or creation) bytecode file, from `runtime.hex`
    (`creation.hex`).

    The constant is `<namespace>.<prefix>Bytecode` and the theorems are in `<namespace>.Bytecode`,
    where `namespace` defaults to the module path.  `constant_namespace` moves the constant to
    another namespace (`""` for the root).  `valid_jumps` is the name of the `@[valid_jumps]`
    theorem to generate, and `provenance` is text to add to the module doc."""
    source = "creation.hex" if creation else "runtime.hex"
    code = parse_bytecode_text((directory / source).read_text(encoding="utf-8"))
    namespace = namespace or module
    vyper_suffix = bool(build and build["compiler"].get("kind") == "vyper" and build.get("immutables"))
    # A Vyper runtime is followed by its immutables and creation code by the constructor
    # arguments.  Neither has immutable pushes.
    tail = "tail" if creation else "suffix" if vyper_suffix else None
    names = [] if tail else solc_immutable_names(build)
    explicit: list[str] | None = None
    if tail or not (names or layout):
        layout = None
    else:
        layout_import = layout_import or f"{module}.ImmutableCode"
        if names:
            code = zero_sites(code, build_sites(build))  # type: ignore[arg-type]
            if first_appearance(build) != names:  # type: ignore[arg-type]
                explicit = names
        else:
            # no build JSON: read the sites of the hand-written layout from Lean
            import generate_rd_blocks
            code = zero_sites(code, list(generate_rd_blocks.read_lean_layout(
                layout, [layout_import], code)))
        layout = layout or f"{namespace}.immutableLayout"
    code_term = f"{prefix}{'Creation' if creation else ''}Bytecode"
    cns = namespace if constant_namespace is None else constant_namespace
    qual = f"{cns}.{code_term}" if cns else code_term
    return render(namespace, name, qual, source, code, creation, tail, layout,
                  layout_import, explicit, blocks_namespace or f"{prefix}Blocks", valid_jumps,
                  provenance)

def write_bytecode_file(directory: Path, module: str, name: str, prefix: str,
                        build: dict | None, creation: bool = False, force: bool = False,
                        **options: str | None) -> bool:
    """Write the bytecode file, unless it exists and ``force`` is not set.  Returns whether it was
    written.  ``options`` are passed to `render_bytecode_file`."""
    out = bytecode_file_path(directory, creation)
    if out.exists() and not force:
        print(f"kept existing {out} (use --force to overwrite)")
        return False
    out.write_text(render_bytecode_file(directory, module, name, prefix, build, creation,
                                        **options), encoding="utf-8")
    print(f"wrote {out}")
    return True


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dir", type=Path, required=True)
    ap.add_argument("--module")
    ap.add_argument("--contract")
    ap.add_argument("--prefix")
    ap.add_argument("--blocks-namespace",
                    help="namespace of the generated block summaries (default: <prefix>Blocks)")
    ap.add_argument("--creation", action="store_true",
                    help="list creation.hex into CreationBytecode.lean; the summaries are over "
                         "`<prefix>CreationBytecode ++ tail` for any constructor-argument tail")
    ap.add_argument("--layout",
                    help="Lean term of the summaries' immutable layout "
                         "(default: <Module>.immutableLayout); given without a build JSON, the "
                         "runtime has immutables at the layout's sites")
    ap.add_argument("--layout-import",
                    help="Lean module defining --layout (default: <Module>.ImmutableCode)")
    ap.add_argument("--constant-namespace",
                    help="namespace of the bytecode constant (default: <Module>; '' for the root)")
    ap.add_argument("--valid-jumps", metavar="NAME",
                    help="also state membership in the code's JUMPDEST set as the @[valid_jumps] "
                         "theorem NAME (full name), for the `jump_dest` tactic")
    ap.add_argument("--provenance", type=Path,
                    help="file whose text is added to the module doc (how the bytes were produced)")
    ap.add_argument("--force", action="store_true")
    a = ap.parse_args()
    import scaffold
    name = scaffold.contract_name(a.dir, a.contract)
    build_path = scaffold.find_build(a.dir, name)
    build = json.loads(build_path.read_text()) if build_path else None
    module = a.module or scaffold.default_module(a.dir)
    prefix = a.prefix or scaffold.lower_camel(name)
    if not write_bytecode_file(a.dir, module, name, prefix, build, a.creation, a.force,
                               blocks_namespace=a.blocks_namespace, layout=a.layout,
                               layout_import=a.layout_import,
                               constant_namespace=a.constant_namespace,
                               valid_jumps=a.valid_jumps,
                               provenance=a.provenance.read_text() if a.provenance else None):
        sys.exit(1)


if __name__ == "__main__":
    main()

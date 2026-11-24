#!/usr/bin/env python3
"""Write a contract's listing (`<Dir>/Bytecode.lean`): its runtime bytecode as a checked table.

Usage:
    gen_listing.py --dir <Dir> [--module <Module>] [--contract <Name>] [--prefix <prefix>]
                   [--creation] [--layout <term> --layout-import <module>] [--force]
                   [--constant-namespace <ns>] [--blocks-namespace <ns>]
                   [--valid-jumps <name>] [--provenance <file>]

`scaffold.py lean` writes the same files through `write_listing`; this command line is for
regenerating a listing alone, or for a contract whose immutable layout is a Lean term of its
own (`--layout`).  With `--creation` it lists `creation.hex` into `<Dir>/CreationBytecode.lean`.

The file is one `listing_from_hex` command (`Reasoning/Listing/FromHex.lean`), in the namespace
`<Module>.Listing` (`<Module>.CreationListing`), whatever the file is called:

    namespace <Module>.Listing
    listing_from_hex "runtime.hex" sha256 "<SHA-256 of the file>"
      bytecode <Module>.<prefix>Bytecode
      [creation] [followed_by tail|suffix]
      [layout <Layout term> [names [...]] blocks <prefix>Blocks]
      [valid_jumps <name>]
    end <Module>.Listing

When the file is elaborated, the command reads the hex file, checks its SHA-256 against the one
written here, decodes it, and adds the listing: `bytes` (the code; for solc immutables the
template, zeros at the immutable sites), `table` (its sections, cut at every `JUMPDEST`,
immutable pushes as `.immutable i`), the bytecode constant `⟨bytes.toArray⟩`, the kernel's
check `Checked bytes table` (`Reasoning/Listing/Basic.lean`), the proof that the code the block
summaries are stated over is the listing's filled code (`Reasoning/Listing/Code.lean`),
`decodes_code` and `jumpdest_code` (which `generate_rd_blocks.py --listing` uses) and, with
`--valid-jumps <name>`, the `@[valid_jumps]` theorem `<name>` stating membership in the code's
`JUMPDEST` set as a lookup in the listing's tree (`Reasoning/Listing/JumpTable.lean`), for hand
proofs that discharge jump targets with the `jump_dest` tactic (`Reasoning/JumpDest.lean`).

Solc immutables: when the build JSON (`<Dir>/<Name>.build.json`, written by `scaffold.py
compile`) lists immutables, or `--layout` is given, the listing names the summaries' layout
(`<Module>.immutableLayout` from `<Module>.ImmutableCode` unless `--layout`/`--layout-import`
name another); the command takes the sites from that layout, numbers the immutables by first
appearance among the sites (`names [...]` is written when the build JSON's order differs), and
states the layout facts their users cite (`immutableLayout_inBounds`, …) in the block summaries'
namespace (`--blocks-namespace`, default `<prefix>Blocks`).  A Vyper runtime with immutables
(`template ++ suffix`) and creation code (`creationBytecode ++ tail`) are listed as fixed code
followed by arbitrary data (`followed_by`).

Nothing here is trusted: the kernel checks the listing when the file is built.  Lake does not
track the hex file; the hash in the source pins it (`check_listing_hashes.py` checks every
listing's hash without building).  Output is deterministic.  Standard library only.
"""

from __future__ import annotations

import argparse
import json
import sys
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bytecode_io import parse_bytecode_text, sha256_hex  # noqa: E402

WIDTH = 96


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
    """Immutable names by first appearance among the sites (in build JSON order, as
    `scaffold.py lean` writes the layout), the numbering `listing_from_hex` uses by default."""
    sites = build.get("layoutSites") or [(off, imm["name"]) for imm in build["immutables"]
                                         for off in imm["offsets"]]
    out: list[str] = []
    for _, key in sites:
        if key not in out:
            out.append(key)
    return out


def lean_string_list(names: list[str]) -> str:
    return "[" + ", ".join(json.dumps(n) for n in names) + "]"


def render(namespace: str, name: str, qual: str, hex_file: str, sha: str, creation: bool,
           tail: str | None, layout: str | None, layout_import: str | None,
           names: list[str] | None, blocks_namespace: str | None, valid_jumps: str | None,
           provenance: str | None) -> str:
    """The text of a listing file: imports, module doc, and the `listing_from_hex` command.
    ``names``: the immutables' order, written only when given (``None``: first appearance)."""
    ns = f"{namespace}.{'CreationListing' if creation else 'Listing'}"
    what = "creation" if creation else "runtime"
    if tail == "tail":
        clause = ": the code followed by any `tail` (the constructor arguments)"
    elif tail is not None:
        clause = f": the template followed by any `{tail}` (its immutables' data section)"
    elif layout:
        clause = (f": the template (`{hex_file}` with the sites of `{layout.rsplit('.', 1)[-1]}` "
                  "zeroed) with the immutables written in")
    else:
        clause = ""
    para = (f"`{name}`'s {what} bytecode as a table of sections, the check tying the table to "
            "the bytes, and what the check gives (`Reasoning/Listing/Sound.lean`) for the code "
            f"the block summaries are stated over{clause}.  The listing is computed from "
            f"`{hex_file}` when this file is elaborated (`Reasoning/Listing/FromHex.lean`); "
            f"`#print_listing {ns}.table` shows it.")
    doc = textwrap.wrap("/-! " + para, WIDTH, break_long_words=False, break_on_hyphens=False)
    if provenance:
        doc += ["", *provenance.strip("\n").splitlines()]
    doc[-1] += " -/"
    out = []
    if layout:
        out.append(f"import {layout_import}")
    out += ["import Reasoning.Listing.FromHex", "", *doc, "", f"namespace {ns}", "",
            f'listing_from_hex "{hex_file}" sha256 "{sha}"']
    line = f"  bytecode {qual}"
    if creation:
        line += " creation"
    if tail:
        line += f" followed_by {tail}"
    out.append(line)
    if layout:
        named = f" names {lean_string_list(names)}" if names else ""
        out.append(f"  layout {layout}{named} blocks {blocks_namespace}")
    if valid_jumps:
        out.append(f"  valid_jumps {valid_jumps}")
    out += ["", f"end {ns}", ""]
    return "\n".join(out)


def listing_path(directory: Path, creation: bool = False) -> Path:
    """Where a directory's listing lives: `Bytecode.lean`, or `CreationBytecode.lean`."""
    return directory / ("CreationBytecode.lean" if creation else "Bytecode.lean")


def render_listing(directory: Path, module: str, name: str, prefix: str, build: dict | None,
                   creation: bool = False, blocks_namespace: str | None = None,
                   layout: str | None = None, layout_import: str | None = None,
                   namespace: str | None = None, constant_namespace: str | None = None,
                   valid_jumps: str | None = None, provenance: str | None = None) -> str:
    """The text of the directory's runtime (or creation) listing over `runtime.hex`
    (`creation.hex`), whose SHA-256 it writes down.  The constant is
    `<namespace>.<prefix>Bytecode` and the listing's namespace `<namespace>.Listing`
    (`namespace` defaults to the module path); `constant_namespace` puts the constant in
    another namespace (`""`: the root).  `valid_jumps` names a theorem stating membership in the
    code's `JUMPDEST` set as a tree lookup, tagged `@[valid_jumps]`; `provenance` is prose for
    the module doc."""
    source = "creation.hex" if creation else "runtime.hex"
    hex_path = directory / source
    parse_bytecode_text(hex_path.read_text(encoding="utf-8"))  # a readable hex file
    namespace = namespace or module
    vyper_suffix = bool(build and build["compiler"].get("kind") == "vyper" and build.get("immutables"))
    # A Vyper runtime is `template ++ suffix` (its immutables' data section); creation code is
    # followed by the constructor arguments.  Neither has immutable pushes.
    tail = "tail" if creation else "suffix" if vyper_suffix else None
    names = [] if tail else solc_immutable_names(build)
    explicit: list[str] | None = None
    if tail or not (names or layout):
        layout = None
    else:
        layout = layout or f"{namespace}.immutableLayout"
        layout_import = layout_import or f"{module}.ImmutableCode"
        if names and first_appearance(build) != names:  # type: ignore[arg-type]
            explicit = names
    code_term = f"{prefix}{'Creation' if creation else ''}Bytecode"
    cns = namespace if constant_namespace is None else constant_namespace
    qual = f"{cns}.{code_term}" if cns else code_term
    return render(namespace, name, qual, source, sha256_hex(hex_path), creation, tail, layout,
                  layout_import, explicit, blocks_namespace or f"{prefix}Blocks", valid_jumps,
                  provenance)


def write_listing(directory: Path, module: str, name: str, prefix: str, build: dict | None,
                  creation: bool = False, force: bool = False, **options: str | None) -> bool:
    """Write the listing unless the file exists and ``force`` is not set; ``True`` if written.
    ``options``: ``blocks_namespace``, ``layout``, ``layout_import``, ``namespace``,
    ``constant_namespace``, ``valid_jumps``, ``provenance`` (see `render_listing`)."""
    out = listing_path(directory, creation)
    if out.exists() and not force:
        print(f"kept existing {out} (use --force to overwrite)")
        return False
    out.write_text(render_listing(directory, module, name, prefix, build, creation, **options),
                   encoding="utf-8")
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
    if not write_listing(a.dir, module, name, prefix, build, a.creation, a.force,
                         blocks_namespace=a.blocks_namespace, layout=a.layout,
                         layout_import=a.layout_import, constant_namespace=a.constant_namespace,
                         valid_jumps=a.valid_jumps,
                         provenance=a.provenance.read_text() if a.provenance else None):
        sys.exit(1)


if __name__ == "__main__":
    main()

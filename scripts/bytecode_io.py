#!/usr/bin/env python3
"""Shared bytecode input: hex / JSON artifacts, and listings (`gen_listing.py`)."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


def recursively_find_bytecode(value: object) -> str | None:
    if isinstance(value, dict):
        for key in ("object", "bytecode", "deployedBytecode"):
            if key in value:
                found = recursively_find_bytecode(value[key])
                if found:
                    return found
        for child in value.values():
            found = recursively_find_bytecode(child)
            if found:
                return found
    elif isinstance(value, list):
        for child in value:
            found = recursively_find_bytecode(child)
            if found:
                return found
    elif isinstance(value, str) and re.fullmatch(r"(?:0x)?[0-9a-fA-F]+", value):
        return value
    return None


def parse_bytecode_text(text: str) -> bytes:
    """Hex (with or without `0x`, whitespace, commas), a JSON artifact holding hex, or one Lean
    `⟨#[…]⟩` byte-array literal."""
    stripped = text.strip()
    lean_array = re.search(r"⟨#\[(.*?)\]\s*⟩", stripped, flags=re.DOTALL)
    if lean_array:
        array_body = re.sub(r"--[^\n]*", "", lean_array.group(1))
        array_body = re.sub(r"/-(?:.|\n)*?-/", "", array_body)
        tokens = re.findall(r"0x[0-9a-fA-F]+|\b[0-9]+\b", array_body)
        values = [int(token, 0) for token in tokens]
        if not values or any(value > 255 for value in values):
            raise ValueError("Lean ByteArray literal must contain bytes in the range 0..255")
        return bytes(values)
    if stripped.startswith(("{", "[")):
        candidate = recursively_find_bytecode(json.loads(stripped))
        if candidate is None:
            raise ValueError("JSON contains no hex bytecode object")
        stripped = candidate
    stripped = re.sub(r"0x", "", stripped, flags=re.IGNORECASE)
    stripped = re.sub(r"[\s,_]", "", stripped)
    if not re.fullmatch(r"[0-9a-fA-F]*", stripped) or len(stripped) % 2:
        raise ValueError("bytecode must contain an even number of hexadecimal digits")
    return bytes.fromhex(stripped)


# --------------------------------------------------------------------------------------------
# Listings: `Bytecode.lean` / `CreationBytecode.lean`, one `listing_from_hex` command
# (`Reasoning/Listing/FromHex.lean`, written by `gen_listing.py`):
#
#     namespace <M>.Listing
#     listing_from_hex "runtime.hex" sha256 "<64 hex digits>"
#       bytecode <full constant name> [creation] [followed_by tail|suffix]
#       [layout <Layout constant> [names ["A", …]] blocks <namespace>] [valid_jumps <name>]
#     end <M>.Listing

LISTING_COMMAND = re.compile(
    r'^listing_from_hex\s+"([^"]*)"\s+sha256\s+"([^"]*)"(.*?)(?=^end\s|\Z)', re.M | re.S)
LISTING_NAMESPACE = re.compile(r"^namespace (\S+\.(?:Creation)?Listing)\s*$", re.M)
IMPORT = re.compile(r"^import\s+(\S+)", re.M)


@dataclass(frozen=True)
class ListingCommand:
    """The `listing_from_hex` command of a listing file, and the file's namespace and imports."""
    namespace: str
    file: str
    sha256: str
    bytecode: str
    creation: bool = False
    followed_by: str | None = None
    layout: str | None = None
    names: tuple[str, ...] = ()
    blocks: str | None = None
    valid_jumps: str | None = None
    imports: tuple[str, ...] = ()
    path: Path | None = field(default=None, compare=False)

    @property
    def hex_path(self) -> Path:
        """The hex file, relative to the listing file's directory (as the command reads it)."""
        if self.path is None:
            raise ValueError("a listing parsed from text has no directory")
        return self.path.parent / self.file


def parse_listing(text: str, path: Path | None = None) -> ListingCommand | None:
    """The listing command of ``text`` (with its enclosing namespace), or ``None`` when the text
    holds no `listing_from_hex` command.  A malformed command raises ``ValueError``."""
    command = LISTING_COMMAND.search(text)
    if command is None:
        return None
    where = f"{path}: " if path else ""
    namespaces = [m for m in LISTING_NAMESPACE.finditer(text) if m.start() < command.start()]
    if not namespaces:
        raise ValueError(f"{where}listing_from_hex outside a `<M>.Listing` namespace")
    rest = re.sub(r"--[^\n]*", "", command.group(3))
    tokens = re.findall(r'\[[^\]]*\]|"[^"]*"|[^\s\[\]"]+', rest)
    options: dict[str, object] = {}
    flags = {"creation"}
    with_arg = {"bytecode", "followed_by", "layout", "names", "blocks", "valid_jumps"}
    k = 0
    while k < len(tokens):
        key = tokens[k]
        if key in flags:
            options[key] = True
            k += 1
        elif key in with_arg and k + 1 < len(tokens):
            options[key] = tokens[k + 1]
            k += 2
        else:
            raise ValueError(f"{where}listing_from_hex: unexpected `{key}`")
    if "bytecode" not in options:
        raise ValueError(f"{where}listing_from_hex without `bytecode`")
    if ("layout" in options) != ("blocks" in options):
        raise ValueError(f"{where}listing_from_hex: `layout` and `blocks` go together")
    if "names" in options and "layout" not in options:
        raise ValueError(f"{where}listing_from_hex: `names` without `layout`")
    names: tuple[str, ...] = ()
    if "names" in options:
        names = tuple(json.loads(options["names"]))  # a list of string literals
    return ListingCommand(
        namespace=namespaces[-1].group(1), file=command.group(1),
        sha256=command.group(2).strip().lower(), bytecode=str(options["bytecode"]),
        creation=bool(options.get("creation")),
        followed_by=options.get("followed_by"), layout=options.get("layout"),  # type: ignore[arg-type]
        names=names, blocks=options.get("blocks"),  # type: ignore[arg-type]
        valid_jumps=options.get("valid_jumps"),  # type: ignore[arg-type]
        imports=tuple(IMPORT.findall(text)), path=path)


def read_listing(path: Path) -> ListingCommand | None:
    """The listing command of the file ``path``; ``None`` if it does not exist or holds none."""
    if not path.is_file():
        return None
    return parse_listing(path.read_text(encoding="utf-8"), path)


def listing_namespace(text: str) -> str | None:
    """The listing's namespace (`<Module>.Listing` / `<Module>.CreationListing`) when ``text``
    is a listing file, else ``None``."""
    found = parse_listing(text)
    return found.namespace if found else None


def is_listing_file(path: Path) -> bool:
    """``path`` exists and is a listing (a `listing_from_hex` command)."""
    return read_listing(path) is not None


def listing_constants(text: str) -> list[str]:
    """The full names of the ByteArray constants the listing defines (its `bytecode`)."""
    found = parse_listing(text)
    return [found.bytecode] if found else []


def sha256_hex(path: Path) -> str:
    """SHA-256 of the raw file bytes, as `listing_from_hex` computes it."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_listing_hash(listing: ListingCommand) -> None:
    """The hex file exists and its SHA-256 is the one written in the listing, else ValueError."""
    hex_path = listing.hex_path
    if not hex_path.is_file():
        raise ValueError(f"{listing.path}: names {listing.file}, which does not exist")
    actual = sha256_hex(hex_path)
    if actual != listing.sha256:
        raise ValueError(f"{listing.path}: the SHA-256 of {hex_path} is {actual}, not the "
                         f"{listing.sha256} written in the listing")


def listing_sites(listing: ListingCommand, code: bytes) -> dict[int, str]:
    """First data byte -> layout key of each immutable site of a listing with `layout`: the
    solc build JSON's `immutables` next to the listing when it has them, else the Lean layout
    itself, evaluated (`generate_rd_blocks.read_lean_layout`; its module must be built)."""
    if listing.layout is None:
        return {}
    directory = listing.hex_path.parent
    for build_path in sorted(directory.glob("*.build.json")):
        build = json.loads(build_path.read_text(encoding="utf-8"))
        if build.get("compiler", {}).get("kind") == "vyper" or not build.get("immutables"):
            continue
        return {off: imm["name"] for imm in build["immutables"] for off in imm["offsets"]}
    import generate_rd_blocks
    imports = [m for m in listing.imports if not m.startswith("Reasoning.")]
    found = generate_rd_blocks.read_lean_layout(listing.layout, imports, code)
    return {off: key for off, (_, key) in found.items()}


def listing_bytes(listing: ListingCommand, sites: dict[int, str] | None = None) -> bytes:
    """The bytes of a listing, as the command computes them: its hex file (SHA-256 checked)
    with the 32 bytes of every immutable site zeroed.  ``sites`` defaults to
    `listing_sites`."""
    check_listing_hash(listing)
    code = bytearray(parse_bytecode_text(listing.hex_path.read_text(encoding="utf-8")))
    if sites is None:
        sites = listing_sites(listing, bytes(code))
    for off in sites:
        if not (1 <= off and off + 32 <= len(code)):
            raise ValueError(f"{listing.path}: immutable site {off} outside the code")
        code[off:off + 32] = bytes(32)
    return bytes(code)


def read_bytecode(path: Path, code_term: str | None = None) -> bytes:
    raw = sys.stdin.buffer.read() if str(path) == "-" else path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        return raw
    if code_term is not None and path.suffix == ".lean":
        # a listing: the bytes its constant is defined from
        listing = parse_listing(text, path)
        if listing is None:
            raise ValueError(f"{path} is not a listing (scripts/gen_listing.py)")
        local = code_term.rsplit(".", 1)[-1]
        if listing.bytecode.rsplit(".", 1)[-1] != local:
            raise ValueError(f"the listing {path} does not define {code_term}")
        return listing_bytes(listing)
    try:
        return parse_bytecode_text(text)
    except (ValueError, json.JSONDecodeError):
        return raw

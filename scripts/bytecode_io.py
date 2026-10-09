#!/usr/bin/env python3
"""Shared bytecode input and Lean ByteArray-definition parsing."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


LEAN_DECLARATION = re.compile(
    r"^(?:private\s+)?def\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*ByteArray\s*:=",
    re.MULTILINE,
)


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


def parse_lean_byte_arrays(text: str) -> dict[str, bytes]:
    """Evaluate literal and simple ``++`` ByteArray definitions in Lean source."""
    declarations = list(LEAN_DECLARATION.finditer(text))
    values: dict[str, bytes] = {}
    pending: list[tuple[str, str]] = []
    for index, match in enumerate(declarations):
        end = declarations[index + 1].start() if index + 1 < len(declarations) else len(text)
        name = match.group(1)
        body = text[match.end():end]
        literal = re.match(r"\s*(⟨#\[.*?\]\s*⟩)", body, re.DOTALL)
        if literal:
            values[name] = parse_bytecode_text(literal.group(1))
        else:
            pending.append((name, body))

    while pending:
        deferred: list[tuple[str, str]] = []
        made_progress = False
        for name, body in pending:
            expression = body.split("\n\n", 1)[0]
            expression = re.sub(r"--[^\n]*", "", expression)
            expression = re.sub(r"/-(?:.|\n)*?-/", "", expression)
            identifiers = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", expression)
            if identifiers and all(identifier in values for identifier in identifiers):
                values[name] = b"".join(values[identifier] for identifier in identifiers)
                made_progress = True
            else:
                deferred.append((name, body))
        if not made_progress:
            break
        pending = deferred
    return values


def parse_bytecode_text(text: str, code_term: str | None = None) -> bytes:
    stripped = text.strip()
    if code_term is not None and LEAN_DECLARATION.search(stripped):
        values = parse_lean_byte_arrays(stripped)
        local_name = code_term.rsplit(".", 1)[-1]
        if local_name not in values:
            raise ValueError(f"could not reconstruct ByteArray definition {code_term}")
        return values[local_name]

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


def read_bytecode(path: Path, code_term: str | None = None) -> bytes:
    raw = sys.stdin.buffer.read() if str(path) == "-" else path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        return raw
    try:
        return parse_bytecode_text(text, code_term)
    except (ValueError, json.JSONDecodeError):
        if code_term is not None and LEAN_DECLARATION.search(text):
            raise
        return raw

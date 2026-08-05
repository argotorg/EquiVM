#!/usr/bin/env python3
"""Transcribe Solidity runtime bytecode hex to a Lean `ByteArray` definition.

Usage:

    python3 Examples/Precompiles/Blake2f/scripts/transcribe_runtime.py \
      /tmp/blake2f-build/Blake2fDeployed.bin-runtime

The script prints chunked Lean code suitable for pasting into
`Examples/Precompiles/Blake2f/Bytecode.lean`.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def read_hex(path: Path) -> str:
    text = path.read_text().strip()
    if text.startswith("0x"):
        text = text[2:]
    text = "".join(text.split())
    if len(text) % 2 != 0:
        raise SystemExit(f"{path}: hex input has odd length")
    bad = [c for c in text if c not in "0123456789abcdefABCDEF"]
    if bad:
        raise SystemExit(f"{path}: non-hex character {bad[0]!r}")
    return text.lower()


def chunks(xs: list[str], size: int) -> list[list[str]]:
    return [xs[i : i + size] for i in range(0, len(xs), size)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("runtime_hex", type=Path)
    parser.add_argument("--namespace", default="Blake2f")
    parser.add_argument("--name", default="runtimeBytecode")
    parser.add_argument("--chunk-size", type=int, default=256)
    args = parser.parse_args()

    hex_text = read_hex(args.runtime_hex)
    byte_literals = [f"0x{hex_text[i:i + 2]}" for i in range(0, len(hex_text), 2)]
    chunked = chunks(byte_literals, args.chunk_size)

    print("import Ethereum.Semantics")
    print()
    print(f"namespace {args.namespace}")
    print()
    for idx, chunk in enumerate(chunked):
        print(f"private def {args.name}Chunk{idx} : ByteArray :=")
        print("  ⟨#[")
        for line in chunks(chunk, 16):
            print("    " + ", ".join(line) + ",")
        print("  ]⟩")
        print()
    if chunked:
        joined = " ++\n  ".join(f"{args.name}Chunk{idx}" for idx in range(len(chunked)))
    else:
        joined = "ByteArray.empty"
    print(f"def {args.name} : ByteArray :=")
    print(f"  {joined}")
    print()
    print(f"end {args.namespace}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Check that every listing's hex file is the one its source pins.

A listing (`Bytecode.lean` / `CreationBytecode.lean`, `scripts/gen_listing.py`) is a
`listing_from_hex "<file>" sha256 "<hash>" …` command (`Reasoning/Listing/FromHex.lean`) that
reads the hex file when the module is elaborated.  Lake does not track that file, so an edited
hex file with up-to-date `.olean`s goes unnoticed until a clean build.  This script reads every
listing among the repository's tracked `.lean` files (or the files given) and checks, without
Lean, that the file it names exists and that its SHA-256 is the one written in the source.

Usage: check_listing_hashes.py [--root <checkout>] [file.lean ...]
Exit status 1 when a listing is malformed, names a missing file, or the hash differs.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bytecode_io import check_listing_hash, parse_listing  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
# The command's own definition shows it in its documentation.
SKIP = {"Reasoning/Listing/FromHex.lean"}


def listing_files(root: Path) -> list[Path]:
    """Tracked `.lean` files (untracked ones too, unless ignored) with a line starting with
    `listing_from_hex "`."""
    out = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard",
                          "*.lean"], cwd=root, capture_output=True, text=True, check=True).stdout
    found = []
    for name in out.splitlines():
        path = root / name
        if name in SKIP or not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        if "\nlisting_from_hex \"" in text or text.startswith("listing_from_hex \""):
            found.append(path)
    return sorted(found)


def check(paths: list[Path]) -> list[str]:
    """One message per failing listing."""
    failures = []
    for path in paths:
        try:
            listing = parse_listing(path.read_text(encoding="utf-8"), path)
            if listing is None:
                raise ValueError(f"{path}: no listing_from_hex command")
            check_listing_hash(listing)
        except (OSError, ValueError) as error:
            failures.append(str(error))
    return failures


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("files", nargs="*", type=Path)
    a = ap.parse_args(argv)
    paths = [p.resolve() for p in a.files] if a.files else listing_files(a.root.resolve())
    failures = check(paths)
    for line in failures:
        print(f"FAIL {line}")
    print(f"{len(paths) - len(failures)}/{len(paths)} listings: hex file present, SHA-256 as pinned")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())

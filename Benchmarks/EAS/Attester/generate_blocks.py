#!/usr/bin/env python3
"""Regenerate immutable-aware runtime and constructor-prefix RD summaries."""

from pathlib import Path
import argparse
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT.parents[2] / "scripts"))
import generate_rd_blocks as blocks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare without rewriting artifacts")
    args = parser.parse_args()
    temporary = tempfile.TemporaryDirectory(prefix="eas-blocks-")
    output = Path(temporary.name) if args.check else ROOT / "Blocks"
    output.mkdir(exist_ok=True)
    imports = ["Benchmarks.EAS.Attester.Bytecode",
               "Benchmarks.EAS.Attester.Immutables"]
    layout = "Benchmarks.EAS.Attester.Immutables.immutableLayout"
    runtime = bytes.fromhex((ROOT / "runtime.hex").read_text())
    creation = bytes.fromhex((ROOT / "creation.hex").read_text())
    if not creation.endswith(runtime):
        raise ValueError("creation artifact must end with the runtime template")
    runtime_offset = len(creation) - len(runtime)
    sites = blocks.read_lean_layout(layout, imports, runtime)
    paths = []
    for kind, code in [("Runtime", runtime), ("Creation", creation)]:
        is_creation = kind == "Creation"
        term = "Benchmarks.EAS.Attester.attester" + ("Creation" if is_creation else "") + "Bytecode"
        name = "attester" + kind
        units = blocks.generate_unit_records(
            code, name, term, creation_code=is_creation,
            immutable_sites=None if is_creation else sites,
            layout_term=None if is_creation else layout)
        if is_creation:
            # The remainder is data copied by CODECOPY, not constructor instructions.
            units = [u for u in units if u.pcs and max(u.pcs) < runtime_offset]
        analyzed = code[:runtime_offset] if is_creation else blocks.strip_solidity_metadata(code)
        covered = {pc for unit in units for pc in unit.pcs}
        missing = [i for i in blocks.disassemble(analyzed) if i.pc not in covered]
        if any(i.opcode != 0xf1 or is_creation for i in missing):
            raise ValueError(f"unexpected summary coverage gaps: {missing}")
        written = blocks.write_outputs(
            output / f"{kind}.lean", name, imports, units, 20,
            creation_code=is_creation, code_term=term,
            immutable_sites=None if is_creation else sites, code=code,
            layout_term=None if is_creation else layout)
        # Only remove obsolete files owned by this generator.
        if not args.check:
            for previous in output.glob(f"{kind}_*.lean"):
                if re.fullmatch(rf"{kind}_\d+\.lean", previous.name) and previous not in written:
                    previous.unlink()
        paths.extend(written)
        summaries = sum(bool(u.pcs) for u in units)
        print(f"{kind}: {summaries} summaries, {len(written)} modules, {len(missing)} CALL boundaries")
    aggregator = "".join(
        f"import Benchmarks.EAS.Attester.Blocks.{p.stem}\n" for p in paths)
    if args.check:
        expected_names = {p.name for p in paths}
        actual_names = {p.name for p in (ROOT / "Blocks").glob("*.lean")}
        if expected_names != actual_names:
            raise ValueError("generated shard filenames differ")
        for p in paths + [output / "Runtime.index", output / "Creation.index"]:
            if p.read_bytes() != (ROOT / "Blocks" / p.name).read_bytes():
                raise ValueError(f"generated artifact differs: {p.name}")
        if aggregator != (ROOT / "Blocks.lean").read_text():
            raise ValueError("generated artifact differs: Blocks.lean")
        print("All generated summaries and indexes reproduce exactly")
    else:
        (ROOT / "Blocks.lean").write_text(aggregator)
    print(f"Constructor executable prefix: [0, {runtime_offset})")
    temporary.cleanup()


if __name__ == "__main__":
    main()

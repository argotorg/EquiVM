#!/usr/bin/env python3
"""Generate RD summaries for executable regions; retain complete artifact bytes.

The runtime's callback constant and metadata, and the constructor's embedded
runtime, are data. CREATE2 and external calls remain explicit proof boundaries.
"""
from pathlib import Path
import argparse
import re
import sys

directory = Path(__file__).resolve().parent
sys.path.insert(0, str(directory.parents[1] / "scripts"))
import generate_rd_blocks as rd

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--creation-only", action="store_true")
args = parser.parse_args()
module = "Benchmarks.Midnight"
runtime = bytes.fromhex((directory / "runtime.hex").read_text())
creation = bytes.fromhex((directory / "creation.hex").read_text())
assert len(runtime) == 24557 and runtime[24512] == 0xfe
assert runtime[24513:24545].hex() == "7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2"
assert len(creation) == 24640 and creation[83:] == runtime
assert creation[67:83].hex() == "615fed90816100538239f35b5f80fdfe"

regions = [("RuntimeBlocks", "midnight", runtime, 24513, False),
           ("CreationBlocks", "midnightCreation", creation, 83, True)]
for stem, prefix, code, limit, is_creation in regions:
    if args.creation_only and not is_creation:
        continue
    code_term = f"{module}.{prefix}Bytecode"
    all_units = rd.generate_unit_records(code, prefix, code_term, creation_code=is_creation)

    def pcs(unit):
        if unit.pcs:
            return unit.pcs
        return (int(re.search(r"boundary at pc (\d+):", unit.text)[1]),)

    units = [unit for unit in all_units if pcs(unit)[0] < limit]
    assert all(max(pcs(unit)) < limit for unit in units)
    assert {pc for unit in units for pc in pcs(unit)} == {
        ins.pc for ins in rd.disassemble(code) if ins.pc < limit}
    paths = rd.write_outputs(directory / (stem + ".lean"), prefix,
        [module + ".Bytecode"], units, 20, is_creation, code_term,
        code=code if not is_creation else None)
    for old in directory.glob(stem + "_*.lean"):
        if old not in paths:
            assert "Automatically generated RD summary" in old.read_text()
            old.unlink()
    print(f"{stem}: {len(units)} units in {len(paths)} shards, executable pcs 0..{limit - 1}")

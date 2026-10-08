#!/usr/bin/env python3
"""Regenerate this benchmark's skeleton without changing the shared generators.

The eleven immutable insertions need a larger elaboration budget than the shared
generator's default. The explicitly hand-written Blue ABI is kept as an input.
Only resource settings of the generated automation are adjusted; theorem statements
and all semantic proof stubs stay unchanged.
"""

from pathlib import Path
import sys

DIRECTORY = Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import proof_skeleton as skeleton

render_common = skeleton.render_common
render_spec = skeleton.render_spec


def common(contract):
    return render_common(contract).replace(
        "set_option maxRecDepth 2000000\n",
        "set_option maxRecDepth 2000000\nset_option maxHeartbeats 2000000\n"
        "attribute [local irreducible] Std.HashMap.insert\n",
        1,
    ).replace("grind [immStore]", f"grind (gen := {3 * len(contract.immutables)}) [immStore]")


def spec(contract):
    result = render_spec(contract)
    start = result.index("/-! ## External-call ABI")
    end = result.index("/-! ## Config", start)
    return result[:start] + (DIRECTORY / "external-abi.lean.inc").read_text() + result[end:]


skeleton.render_common = common
skeleton.render_spec = spec

if __name__ == "__main__":
    raise SystemExit(skeleton.main([
        "--dir", str(DIRECTORY),
        "--module", "Benchmarks.Morpho.MetaMorphoV1_1",
        *sys.argv[1:],
    ]))

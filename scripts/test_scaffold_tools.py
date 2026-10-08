#!/usr/bin/env python3
"""Checks for the scaffold helpers: jump tables, source maps, dispatcher recovery, selectors."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evm_tools as et  # noqa: E402
import scaffold  # noqa: E402
from generate_rd_blocks import disassemble  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent

def tiny_runtime() -> bytes:
    from bytecode_io import read_bytecode
    return read_bytecode(ROOT / "Examples/TinyImmutable/runtime.hex")


class JumpDestTests(unittest.TestCase):
    def test_push_data_is_skipped(self) -> None:
        # PUSH2 0x5b5b JUMPDEST: only the real JUMPDEST at pc 3 counts.
        self.assertEqual(et.jump_dests(bytes.fromhex("615b5b5b")), [3])

    def test_matches_checked_in_table(self) -> None:
        text = (ROOT / "Benchmarks/Dss/Pot/Bytecode.lean").read_text(encoding="utf-8")
        from bytecode_io import read_bytecode
        code = read_bytecode(ROOT / "Benchmarks/Dss/Pot/runtime.hex")
        self.assertEqual(scaffold.lean_jump_table(text, "validJumps"), et.jump_dests(code))


class SourceMapTests(unittest.TestCase):
    def test_fields_inherit(self) -> None:
        entries = et.decode_source_map("57:444:0:-:0;;;86:30;;;;:::i;:::-;4:2:1")
        self.assertEqual(len(entries), 10)
        self.assertEqual((entries[1].start, entries[1].length, entries[1].file), (57, 444, 0))
        self.assertEqual((entries[3].start, entries[3].length), (86, 30))
        self.assertEqual(entries[7].jump, "i")
        self.assertEqual(entries[8].jump, "-")
        self.assertEqual((entries[9].start, entries[9].length, entries[9].file), (4, 2, 1))


class DispatcherTests(unittest.TestCase):
    def test_tiny_dispatcher(self) -> None:
        body, instructions, _ = et.code_and_blocks(tiny_runtime(), keep_metadata=True)
        disp = et.dispatcher(instructions)
        self.assertTrue(disp.callvalue_guard)
        self.assertEqual(disp.calldatasize_check, (24, 63))
        self.assertEqual([(a.selector, a.target) for a in disp.arms],
                         [(0x8DA5CB5B, 67), (0xED1BD76C, 148), (0xF51E181A, 181)])
        self.assertEqual(disp.pivots, [])

    def test_census(self) -> None:
        _, instructions, _ = et.code_and_blocks(tiny_runtime(), keep_metadata=True)
        counts = et.census(instructions)
        self.assertEqual(counts.get("REVERT"), 4)  # callvalue, short calldata, no match, require
        self.assertEqual(counts.get("RETURN"), 1)
        self.assertNotIn("SLOAD", counts)


class SelectorTests(unittest.TestCase):
    def test_keccak_and_abi_signatures(self) -> None:
        self.assertEqual(et.selector("transfer(address,uint256)").hex(), "a9059cbb")
        abi = [{"type": "function", "name": "f", "inputs": [
            {"type": "tuple[]", "components": [{"type": "uint8"}, {"type": "address"}]},
            {"type": "uint256[2]"}]}]
        self.assertEqual(et.abi_signatures(abi), ["f((uint8,address)[],uint256[2])"])

    def test_overload_names(self) -> None:
        names = et.overload_names(["file(bytes32,uint256)", "file(bytes32,address)", "Pie()"])
        self.assertEqual(names["file(bytes32,uint256)"], "file_bytes32_uint256")
        self.assertEqual(names["file(bytes32,address)"], "file_bytes32_address")
        self.assertEqual(names["Pie()"], "pie")

    def test_table_follows_spec_syntax_order(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            (d / "SpecSyntax.lean").write_text(
                "def c := solidity% contract X {\n"
                "  function b() external returns (uint256) { return 1; }\n"
                "  function helper(uint256 x) internal returns (uint256) { return x; }\n"
                "  function a(address «to») external { }\n}\n", encoding="utf-8")
            build = {"methodIdentifiers": {"a(address)": "0a0a0a0a", "b()": "0b0b0b0b"}}
            table = scaffold.selector_table(d, "X", build)
            self.assertEqual([sig for sig, _ in table], ["b()", "a(address)"])
            self.assertEqual(scaffold.spec_syntax_order(d), ["b", "a"])

    def test_lean_selector_table_roundtrip(self) -> None:
        table = [("b()", bytes.fromhex("0b0b0b0b")), ("a(address)", bytes.fromhex("0a0a0a0a"))]
        text = scaffold.render_selectors_lean("N", "x", "X", table)
        self.assertEqual(scaffold.lean_selector_table(text), table)
        self.assertIn("theorem aSelectorFact", text)


class DiffTargetTests(unittest.TestCase):
    def test_render_plain_and_immutable(self) -> None:
        plain = scaffold.render_difftarget_lean("Foo.Bar", "Foo.Bar", "bar", "Bar", True, False)
        self.assertIn("import Foo.Bar.Spec", plain)
        self.assertIn("namespace Foo.Bar", plain)
        self.assertIn("runtime := barBytecode", plain)
        self.assertIn("initcode := some barCreationBytecode", plain)
        self.assertNotIn("immutableLayout", plain)
        imm = scaffold.render_difftarget_lean("Foo.Bar", "Foo.Bar", "bar", "Bar", False, True)
        self.assertIn("import Foo.Bar.ImmutableCode", imm)
        self.assertIn("initcode := none", imm)
        self.assertIn("runtimeCodeOf := some (immutableLayout.deployed barBytecode)", imm)
        self.assertIn("deployedRuntime := true", imm)

    def test_registry_scans_targets(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Tests" / "DiffTest").mkdir(parents=True)
            for module in ("A.One", "B.Two.Three"):
                d = root / Path(*module.split("."))
                d.mkdir(parents=True)
                (d / "DiffTarget.lean").write_text(f"namespace {module}.Ns\ndef diffTarget := 0\n")
            (root / ".lake" / "X").mkdir(parents=True)
            (root / ".lake" / "X" / "DiffTarget.lean").write_text("namespace Skip\n")
            text = scaffold.render_difftest_registry(root)
            self.assertIn("import A.One.DiffTarget", text)
            self.assertIn("import B.Two.Three.DiffTarget", text)
            self.assertIn("B.Two.Three.Ns.diffTarget", text)
            self.assertNotIn("Skip", text)
            self.assertEqual(scaffold.render_difftest_registry(root / "Tests").count("import"), 1)


class ImmutableOrderTests(unittest.TestCase):
    def test_write_order_from_creation_code(self) -> None:
        # ... PUSH1 0xba ADD MSTORE ... PUSH1 0x48 ADD MSTORE: scale (0xba) is written before owner.
        creation = bytes.fromhex("60ba015260480152")
        order = scaffold.immutable_write_order(creation, {"owner": [0x48, 0xF5], "scale": [0xBA, 0x169]})
        self.assertEqual(order, ["scale", "owner"])


if __name__ == "__main__":
    unittest.main()

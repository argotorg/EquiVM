#!/usr/bin/env python3
"""Checks for the scaffold helpers: jump tables, source maps, dispatcher recovery, selectors."""

from __future__ import annotations

import sys
import tempfile
import unittest
import shutil
import argparse
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evm_tools as et  # noqa: E402
import scaffold  # noqa: E402
import bytecode_report  # noqa: E402
import check_all_benchmark_blocks as benchmark_blocks  # noqa: E402
import generate_rd_blocks as rd  # noqa: E402
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


class VyperImmutableTests(unittest.TestCase):
    def test_optimization_pragma_is_recorded(self) -> None:
        source = "# pragma version 0.4.3\n# pragma optimize codesize\n"
        self.assertEqual(scaffold.vyper_optimize_mode(source, False), "codesize")
        self.assertEqual(scaffold.vyper_optimize_mode(source, True), "none")
        self.assertEqual(scaffold.vyper_optimize_mode("# pragma version 0.4.3", False), "gas")

    def test_vyper_report_uses_pc_positions(self) -> None:
        directory = ROOT / "Examples/VyperImmutable"
        build = json.loads((directory / "Immutable.build.json").read_text())
        abi = json.loads((directory / "Immutable.abi.json").read_text())
        report = bytecode_report.render(directory, "Immutable", build, abi, True)
        self.assertIn("compiler: vyper", report)
        self.assertIn("Vyper source positions annotate blocks", report)
        self.assertIn("Selectors not recovered as direct arms", report)
        self.assertIn("line 26:", report)

    @staticmethod
    def scalar_units(runtime: bytes, prefix: str, code: str, slots: list[dict],
                     max_summary_instructions: int = 1000) -> list[rd.GeneratedUnit]:
        return rd.generate_unit_records(
            runtime, prefix, code, max_summary_instructions=max_summary_instructions,
            runtime_suffix=True,
            vyper_scalar_slots={len(runtime) + slot["offset"]: slot["name"]
                                for slot in slots if slot["length"] == 32},
            vyper_layout_term=code.rsplit(".", 1)[0] + ".immutableLayout")

    def test_short_vyper_selector_is_padded_to_four_bytes(self) -> None:
        pairs = scaffold.selector_table(ROOT / "Examples/VyperImmutable", "Immutable",
                                        {"methodIdentifiers": {"get_rate_mul()": "0x95a0fc6"}})
        self.assertEqual(pairs, [("get_rate_mul()", bytes.fromhex("095a0fc6"))])

    def test_contract_interface_is_an_address_word(self) -> None:
        self.assertTrue(scaffold.vyper_scalar_immutable_type("curve_std/interfaces/IERC20.vyi"))
        self.assertFalse(scaffold.vyper_scalar_immutable_type("DynArray[uint256, 3]"))

    def test_block_check_uses_suffix_mode(self) -> None:
        self.assertTrue(benchmark_blocks.benchmark_uses_vyper_suffix(
            ROOT / "Examples/VyperImmutable/Bytecode.lean"))
        self.assertFalse(benchmark_blocks.benchmark_uses_vyper_suffix(
            ROOT / "Examples/TinyImmutable/Bytecode.lean"))

    def test_full_suffix_return_gets_byte_valued_summary(self) -> None:
        from bytecode_io import read_bytecode
        runtime = read_bytecode(ROOT / "Examples/VyperImmutable/runtime.hex")
        units = rd.generate_unit_records(runtime, "immutable",
                                         "Examples.VyperImmutable.immutableBytecode",
                                         runtime_suffix=True,
                                         vyper_layout_term="Examples.VyperImmutable.immutableLayout",
                                         vyper_suffix_size=96)
        valued = next(unit for unit in units if unit.theorem_names == ("immutable_block_41",))
        self.assertNotIn("private theorem", valued.text)
        self.assertIn("codecopy_read_suffix", valued.text)
        self.assertIn("theorem immutable_block_41 {immWords : String → UInt256}", valued.text)
        self.assertIn("σ (Examples.VyperImmutable.immutableLayout.suffixWords immWords)",
                      valued.text)
        unmatched = rd.generate_unit_records(runtime, "immutable",
            "Examples.VyperImmutable.immutableBytecode", runtime_suffix=True,
            vyper_layout_term="Examples.VyperImmutable.immutableLayout", vyper_suffix_size=32)
        self.assertIn("{suffix : ByteArray}", next(unit for unit in unmatched
                      if unit.theorem_names == ("immutable_block_41",)).text)

    def test_scalar_return_uses_named_immutable_word(self) -> None:
        from bytecode_io import read_bytecode
        runtime = read_bytecode(ROOT / "Examples/VyperImmutable/runtime.hex")
        slots = [{"name": "OWNER", "offset": 0, "length": 32},
                 {"name": "LIMIT", "offset": 32, "length": 32},
                 {"name": "TAG", "offset": 64, "length": 32}]
        units = self.scalar_units(runtime, "immutable",
                                  "Examples.VyperImmutable.immutableBytecode", slots)
        valued = next(unit for unit in units if unit.theorem_names == ("immutable_block_71",))
        self.assertIn('σ (immWords "OWNER").toByteArray := by', valued.text)
        self.assertIn("immutableCopyWord_OWNER", valued.text)
        self.assertNotIn("private theorem", valued.text)

    def test_mload_after_suffix_copy_uses_word_in_expression(self) -> None:
        from bytecode_io import read_bytecode
        runtime = read_bytecode(ROOT / "Examples/VyperImmutable/runtime.hex")
        slots = [{"name": "OWNER", "offset": 0, "length": 32},
                 {"name": "LIMIT", "offset": 32, "length": 32},
                 {"name": "TAG", "offset": 64, "length": 32}]
        units = self.scalar_units(runtime, "immutable",
                                  "Examples.VyperImmutable.immutableBytecode", slots)
        valued = next(unit for unit in units if unit.theorem_names == ("immutable_block_106",))
        self.assertIn('(immWords "LIMIT")', valued.text)
        self.assertIn("immutableLoad_LIMIT", valued.text)
        self.assertIn("UInt256.eq", valued.text)
        self.assertNotIn("readWithPadding", valued.text.split(" := by", 1)[0])
        unmatched = self.scalar_units(runtime, "immutable",
                                      "Examples.VyperImmutable.immutableBytecode", slots[:1])
        self.assertIn("{suffix : ByteArray}", next(unit for unit in unmatched
                      if unit.theorem_names == ("immutable_block_106",)).text)

    def test_mload_word_survives_a_block_boundary(self) -> None:
        from bytecode_io import read_bytecode
        runtime = read_bytecode(ROOT / "Examples/VyperImmutable/runtime.hex")
        slots = [{"name": "OWNER", "offset": 0, "length": 32},
                 {"name": "LIMIT", "offset": 32, "length": 32},
                 {"name": "TAG", "offset": 64, "length": 32}]
        units = self.scalar_units(runtime, "immutable",
                                  "Examples.VyperImmutable.immutableBytecode", slots, 8)
        valued = next(unit for unit in units if unit.theorem_names ==
                      ("immutable_block_106", "immutable_block_106_packed"))
        self.assertIn('RD fork (Examples.VyperImmutable.immutableBytecode ++', valued.text)
        self.assertIn('(immWords "LIMIT")', valued.text)
        self.assertIn("theorem immutable_block_106_packed", valued.text)

    def test_multiple_scalar_loads_in_one_block(self) -> None:
        # Two suffix words are copied to different memory offsets before a
        # shared calculation. The second copy has the first copy as its base.
        runtime = bytes.fromhex("602060155f395f5160206035602039602051015b00")
        slots = [{"name": "A", "offset": 0, "length": 32},
                 {"name": "B", "offset": 32, "length": 32}]
        valued = self.scalar_units(runtime, "probe", "Probe.bytecode", slots)[0]
        self.assertIn("have hload0", valued.text)
        self.assertIn("have hload1", valued.text)
        self.assertIn('(immWords "A")', valued.text)
        self.assertIn('(immWords "B")', valued.text)
        self.assertIn("theorem probe_block_0_packed", valued.text)

    def test_scalar_load_used_only_in_branch_condition(self) -> None:
        runtime = bytes.fromhex("6020600d5f395f51600b575b00")
        slots = [{"name": "A", "offset": 0, "length": 32}]
        valued = self.scalar_units(runtime, "probe", "Probe.bytecode", slots)[0]
        self.assertIn('(hcond : (immWords "A") ≠ (UInt256.ofNat 0))', valued.text)
        self.assertIn("have hload0", valued.text)
        self.assertIn("theorem probe_block_0_taken_packed", valued.text)

    def test_scalar_copy_without_load_names_memory_bytes(self) -> None:
        runtime = bytes.fromhex("602060085f395b00")
        slots = [{"name": "A", "offset": 0, "length": 32}]
        valued = self.scalar_units(runtime, "probe", "Probe.bytecode", slots)[0]
        self.assertIn('(immWords "A").toByteArray.write 0 mem', valued.text)
        self.assertIn("immutableCopyWord_A", valued.text)
        self.assertNotIn("have hload", valued.text)
        self.assertNotIn("private theorem", valued.text)

    def test_zero_destination_suffix_copy_is_recognized(self) -> None:
        runtime = bytes.fromhex("6020600a5f3960205ff3")
        valued = rd.generate_unit_records(runtime, "probe", "Probe.bytecode",
            runtime_suffix=True, vyper_layout_term="Probe.immutableLayout",
            vyper_suffix_size=32)[0]
        self.assertIn("theorem probe_block_0 {immWords", valued.text)
        self.assertIn(".write (UInt256.ofNat 10).toNat mem (⟨0⟩ : UInt256).toNat", valued.text)

    def test_compiler_layout_and_suffix_blocks(self) -> None:
        vyper = shutil.which("vyper")
        if vyper is None:
            self.skipTest("Vyper compiler is unavailable")
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            contracts = directory / "contracts"
            contracts.mkdir()
            shutil.copyfile(ROOT / "Examples/VyperImmutable/contracts/Immutable.vy",
                            contracts / "Immutable.vy")
            args = argparse.Namespace(dir=directory, vyper=vyper, main="Immutable.vy",
                                      sources_root="contracts", contract="Immutable",
                                      evm_version="cancun", no_optimize=False)
            self.assertEqual(scaffold.cmd_compile_vyper(args), 0)
            build = json.loads((directory / "Immutable.build.json").read_text())
            self.assertEqual(build["immutableSuffixSize"], 96)
            self.assertEqual([(i["name"], i["offset"], i["length"])
                              for i in build["immutables"]],
                             [("OWNER", 0, 32), ("LIMIT", 32, 32), ("TAG", 64, 32)])
            self.assertIn("slots :=", scaffold.render_vyper_immutables_lean(
                "Probe", "Immutable", build))
            code_lean = scaffold.render_vyper_immutable_code_lean(
                "Probe", "Probe", "immutable", build)
            self.assertIn("theorem returnedRuntime_eq_deployed", code_lean)
            self.assertIn("theorem returnedRuntime_read_eq_deployed", code_lean)
            self.assertEqual(scaffold.selector_table(directory, "Immutable", build)[0][1].hex(),
                             "57de26a4")

    def test_compound_immutable_is_rejected_before_scalar_word_generation(self) -> None:
        vyper = shutil.which("vyper")
        if vyper is None:
            self.skipTest("Vyper compiler is unavailable")
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            contracts = directory / "contracts"
            contracts.mkdir()
            (contracts / "Compound.vy").write_text(
                "# pragma version ^0.4.3\n"
                "ITEMS: immutable(uint256[2])\n"
                "@deploy\n"
                "def __init__():\n"
                "    ITEMS = [1, 2]\n"
                "@external\n"
                "@view\n"
                "def first() -> uint256:\n"
                "    return ITEMS[0]\n", encoding="utf-8")
            args = argparse.Namespace(dir=directory, vyper=vyper, main="Compound.vy",
                                      sources_root="contracts", contract="Compound",
                                      evm_version="cancun", no_optimize=False)
            with self.assertRaisesRegex(SystemExit, "unsupported immutable type"):
                scaffold.cmd_compile_vyper(args)


if __name__ == "__main__":
    unittest.main()

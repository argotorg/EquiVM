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

def needs_converted(test, directory: str) -> None:
    """Skip the test until ``directory`` has a generated `Bytecode.lean`."""
    from bytecode_io import is_bytecode_file
    root = Path(__file__).resolve().parent.parent
    if not is_bytecode_file(root / directory / "Bytecode.lean"):
        test.skipTest(f"{directory} is not converted yet")


def tiny_runtime() -> bytes:
    from bytecode_io import read_bytecode
    return read_bytecode(ROOT / "Examples/TinyImmutable/runtime.hex")


class JumpDestTests(unittest.TestCase):
    def test_push_data_is_skipped(self) -> None:
        # PUSH2 0x5b5b JUMPDEST: only the real JUMPDEST at pc 3 counts.
        self.assertEqual(et.jump_dests(bytes.fromhex("615b5b5b")), [3])

    def test_matches_checked_in_bytecode_file(self) -> None:
        needs_converted(self, "Benchmarks/Dss/Pot")
        # the Python scan and the bytecode file cut the same sections
        from bytecode_io import bytecode_file_bytes, read_bytecode, read_bytecode_file
        pot = ROOT / "Benchmarks/Dss/Pot"
        file = read_bytecode_file(pot / "Bytecode.lean")
        code = read_bytecode(pot / "runtime.hex")
        self.assertEqual(bytecode_file_bytes(file), code)
        starts = sorted({sec for sec, index in rd.section_positions(code).values()
                         if index == 0 and code[sec] == 0x5B})
        self.assertEqual(starts, et.jump_dests(code))
        self.assertEqual(file.valid_jumps, "Benchmarks.Dss.Pot.validJumps")
        self.assertNotIn("native_decide", (pot / "Bytecode.lean").read_text(encoding="utf-8"))


class BytecodeFileTests(unittest.TestCase):
    """`scaffold.py lean` writes the bytecode files and `check` compares them with the hex."""

    DIR = ROOT / "Tests/Pipeline/VyperRegistry"
    MODULE = "Tests.Pipeline.VyperRegistry"

    def test_lean_writes_the_bytecode_files(self) -> None:
        needs_converted(self, "Tests/Pipeline/VyperRegistry")
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            for name in ("runtime.hex", "creation.hex", "Registry.build.json", "Registry.abi.json",
                         "Selectors.lean"):
                if (self.DIR / name).exists():
                    shutil.copy(self.DIR / name, d / name)
            self.assertEqual(scaffold.main(["lean", "--dir", tmp, "--module", self.MODULE]), 0)
            for name in ("Bytecode.lean", "CreationBytecode.lean"):
                text = (d / name).read_text(encoding="utf-8")
                self.assertEqual(text, (self.DIR / name).read_text(encoding="utf-8"))
                self.assertNotIn("native_decide", text)
                self.assertNotIn("validJumps", text)
            # existing files are kept without --force
            (d / "Bytecode.lean").write_text("-- edited\n")
            self.assertEqual(scaffold.main(["lean", "--dir", tmp, "--module", self.MODULE]), 0)
            self.assertEqual((d / "Bytecode.lean").read_text(), "-- edited\n")
            self.assertEqual(scaffold.main(["lean", "--dir", tmp, "--module", self.MODULE,
                                            "--force"]), 0)
            self.assertIn("namespace Tests.Pipeline.VyperRegistry.Bytecode",
                          (d / "Bytecode.lean").read_text())

    def test_valid_jumps_and_constant_namespace(self) -> None:
        import gen_bytecode
        from bytecode_io import parse_bytecode_file
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            code = bytes.fromhex("6005565b005b00")  # PUSH1 5 JUMP JUMPDEST STOP JUMPDEST STOP
            (d / "runtime.hex").write_text(code.hex())
            text = gen_bytecode.render_bytecode_file(d, "Examples.Foo", "Foo", "foo", None,
                                                     constant_namespace="",
                                                     valid_jumps="fooValidJumps",
                                                     provenance="Compiled by hand.")
            self.assertIn("Compiled by hand.", text)
            self.assertNotIn("native_decide", text)
            self.assertIn("eval% EVM.Disassembly.Tree.ofSections (sectionsOf fooBytecode [])", text)
            file = parse_bytecode_file(text, d / "Bytecode.lean")
            self.assertEqual((file.namespace, file.hex_name, file.code, file.bytecode,
                              file.valid_jumps, file.followed_by, file.layout,
                              file.imports),
                             ("Examples.Foo.Bytecode", "runtime.hex", code,
                              "fooBytecode", "fooValidJumps", None, None,
                              ("Reasoning.Disassembly.Facts",)))
            # creation code is followed by its constructor arguments
            (d / "creation.hex").write_text(code.hex())
            ctor = parse_bytecode_file(gen_bytecode.render_bytecode_file(
                d, "Examples.Foo", "Foo", "foo", None, creation=True), d / "x.lean")
            self.assertEqual((ctor.namespace, ctor.hex_name, ctor.code, ctor.bytecode,
                              ctor.creation, ctor.followed_by),
                             ("Examples.Foo.CreationBytecode", "creation.hex", code,
                              "Examples.Foo.fooCreationBytecode", True, "tail"))

    def test_byte_lines(self) -> None:
        # the bytes are written `BYTES_PER_LINE` per line; the parser reads them back
        import gen_bytecode
        from bytecode_io import parse_bytecode_file
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            code = bytes(range(256)) * 3
            (d / "runtime.hex").write_text("0x" + code.hex().upper() + "\n")
            text = gen_bytecode.render_bytecode_file(d, "M", "Foo", "foo", None)
            body = text[text.index("⟨#[") + 3:text.index("]⟩")]
            self.assertEqual([len(line.strip().rstrip(",").split(", ")) for line in body.splitlines()[1:]],
                             [gen_bytecode.BYTES_PER_LINE] * 48)
            self.assertTrue(all(len(line) <= 100 for line in text.splitlines()))
            self.assertEqual(parse_bytecode_file(text).code, code)
            (d / "runtime.hex").write_text("")
            self.assertEqual(parse_bytecode_file(gen_bytecode.render_bytecode_file(
                d, "M", "Foo", "foo", None)).code, b"")

    def test_parse_bytes_literal(self) -> None:
        # the literal's body: `0x..` bytes separated by commas and whitespace
        from bytecode_io import parse_bytes_literal
        self.assertEqual(parse_bytes_literal("\n  0x60, 0x80,\n  0x0a"), bytes.fromhex("60800a"))
        self.assertEqual(parse_bytes_literal(""), b"")
        with self.assertRaisesRegex(ValueError, "not a byte literal"):
            parse_bytes_literal("0x60, 96")
        with self.assertRaisesRegex(ValueError, "not a byte literal"):
            parse_bytes_literal("0x600")

    def test_immutables_name_the_layout(self) -> None:
        # solc immutables: `names` is only written if the build JSON's order is not the default
        import gen_bytecode
        from bytecode_io import parse_bytecode_file
        build = {"compiler": {}, "immutables": [{"name": "a", "offsets": [10, 50]},
                                                {"name": "b", "offsets": [30]}]}
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            (d / "runtime.hex").write_text("7f" + "ff" * 32 + "00" * 99)
            file = parse_bytecode_file(
                gen_bytecode.render_bytecode_file(d, "M", "Foo", "foo", build), d / "x")
            self.assertEqual((file.layout, file.names, file.blocks, file.imports),
                             ("M.immutableLayout", (), "fooBlocks",
                              ("M.ImmutableCode", "Reasoning.Disassembly.Facts")))
            # the literal is the template: the sites' 32 bytes zeroed
            self.assertEqual(file.code, bytes.fromhex("7f" + "ff" * 9 + "00" * 122))
            build["layoutSites"] = [(30, "b"), (10, "a"), (50, "a")]
            file = parse_bytecode_file(
                gen_bytecode.render_bytecode_file(d, "M", "Foo", "foo", build), d / "x")
            self.assertEqual(file.names, ("a", "b"))

    def test_parse_bytecode_file(self) -> None:
        needs_converted(self, "Benchmarks/Morpho/MorphoBlue")
        from bytecode_io import (bytecode_file_constants, bytecode_file_namespace,
                                 parse_bytecode_file)
        text = (ROOT / "Benchmarks/Morpho/MorphoBlue/Bytecode.lean").read_text(encoding="utf-8")
        self.assertEqual(bytecode_file_namespace(text), "Benchmarks.Morpho.MorphoBlue.Bytecode")
        self.assertEqual(bytecode_file_constants(text),
                         ["Benchmarks.Morpho.MorphoBlue.morphoBytecode"])
        file = parse_bytecode_file(text)
        self.assertEqual((file.layout, file.blocks, file.imports[0]),
                         ("Benchmarks.Morpho.MorphoBlue.immutableLayout", "morphoBlocks",
                          "Benchmarks.Morpho.MorphoBlue.ImmutableCode"))
        from bytecode_io import read_bytecode
        self.assertEqual(file.code,
                         read_bytecode(ROOT / "Benchmarks/Morpho/MorphoBlue/runtime.template.hex"))
        self.assertIsNone(parse_bytecode_file("namespace A.Bytecode\nend A.Bytecode\n"))
        named = text.replace(
            "def names : List String := eval% keyOrder Benchmarks.Morpho.MorphoBlue.immutableLayout.sites",
            'def names : List String := ["X", "Y"]')
        self.assertEqual(parse_bytecode_file(named).names, ("X", "Y"))
        with self.assertRaises(ValueError):
            parse_bytecode_file(text.replace("0x60, 0x80", "0x60, 0xzz", 1))

    def test_read_bytecode_of_a_bytecode_file(self) -> None:
        needs_converted(self, "Tests/Pipeline/VyperRegistry")
        from bytecode_io import is_bytecode_file, read_bytecode
        self.assertTrue(is_bytecode_file(self.DIR / "Bytecode.lean"))
        self.assertFalse(is_bytecode_file(ROOT / "Examples/TinyImmutable/runtime.hex"))
        self.assertEqual(read_bytecode(self.DIR / "Bytecode.lean", "registryBytecode"),
                         read_bytecode(self.DIR / "runtime.hex"))
        self.assertEqual(read_bytecode(self.DIR / "CreationBytecode.lean", "registryCreationBytecode"),
                         read_bytecode(self.DIR / "creation.hex"))
        with self.assertRaises(ValueError):
            read_bytecode(self.DIR / "Bytecode.lean", "registryCreationBytecode")
        # the sites are zeroed whatever the hex file has there (Morpho's runtime.hex is mainnet code)
        morpho = ROOT / "Benchmarks/Morpho/MorphoBlue"
        self.assertEqual(read_bytecode(morpho / "Bytecode.lean", "morphoBytecode"),
                         read_bytecode(morpho / "runtime.template.hex"))
        self.assertNotEqual(read_bytecode(morpho / "runtime.hex"),
                            read_bytecode(morpho / "runtime.template.hex"))

    def test_hex_file_is_compared(self) -> None:
        needs_converted(self, "Tests/Pipeline/VyperRegistry")
        # `check_bytecode_hex` compares the bytes with the hex file
        from bytecode_io import check_bytecode_hex, read_bytecode, read_bytecode_file
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            for name in ("Bytecode.lean", "runtime.hex"):
                shutil.copy(self.DIR / name, d / name)
            file = read_bytecode_file(d / "Bytecode.lean")
            check_bytecode_hex(file)
            code = read_bytecode(d / "runtime.hex")
            (d / "runtime.hex").write_text("00" + (d / "runtime.hex").read_text())
            with self.assertRaisesRegex(ValueError, "differ from .*first difference at byte 0"):
                check_bytecode_hex(file)
            self.assertEqual(read_bytecode(d / "Bytecode.lean", "registryBytecode"), code)
            (d / "runtime.hex").unlink()
            with self.assertRaisesRegex(ValueError, "does not exist"):
                check_bytecode_hex(file)
            self.assertEqual(read_bytecode(d / "Bytecode.lean", "registryBytecode"), code)

    def test_check_bytecode_file(self) -> None:
        needs_converted(self, "Benchmarks/Morpho/MorphoBlue")
        morpho = ROOT / "Benchmarks/Morpho/MorphoBlue"
        build = json.loads((morpho / "Morpho.build.json").read_text())
        ok: list[str] = []
        failures: list[str] = []
        scaffold.check_bytecode_file(morpho / "Bytecode.lean",
                                     "Benchmarks.Morpho.MorphoBlue.morphoBytecode",
                                     "Benchmarks.Morpho.MorphoBlue.Bytecode", "runtime.hex", build,
                                     ok, failures)
        self.assertEqual(failures, [])
        self.assertTrue(any("layout sites match the build JSON" in line
                            or "layout sites not compared" in line for line in ok))
        failures = []
        scaffold.check_bytecode_file(morpho / "CreationBytecode.lean",
                                     "Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode",
                                     "Benchmarks.Morpho.MorphoBlue.CreationBytecode", "creation.hex",
                                     build, [], failures)
        self.assertEqual(failures, [])
        # a wrong constant, a missing tail, a hex file whose bytes are not the bytecode file's
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            for name in ("Bytecode.lean", "runtime.hex"):
                shutil.copy(self.DIR / name, d / name)
            shutil.copy(self.DIR / "runtime.hex", d / "creation.hex")
            failures = []
            scaffold.check_bytecode_file(d / "Bytecode.lean",
                                         "Tests.Pipeline.VyperRegistry.otherBytecode",
                                         "Tests.Pipeline.VyperRegistry.Bytecode", "creation.hex",
                                         None, [], failures)
            self.assertTrue(any("otherBytecode" in line for line in failures))
            self.assertTrue(any("expected tail" in line and "`creation` flag wrong" in line
                                for line in failures))
            (d / "runtime.hex").write_text("00" + (d / "runtime.hex").read_text())
            failures = []
            scaffold.check_bytecode_file(d / "Bytecode.lean",
                                         "Tests.Pipeline.VyperRegistry.registryBytecode",
                                         "Tests.Pipeline.VyperRegistry.Bytecode", "runtime.hex",
                                         None, [], failures)
            self.assertTrue(any("differ from" in line for line in failures))


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

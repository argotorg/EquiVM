#!/usr/bin/env python3
"""Focused checks for primitive RD summaries and the return-data copy rule."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
import sys
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_all_benchmark_blocks as benchmarks
import generate_rd_blocks as rd


def units(hex_code: str, **kwargs: object) -> str:
    return "\n".join(rd.generate_units(
        bytes.fromhex(hex_code), "sample", "sampleCode", keep_metadata=True, **kwargs
    ))


class GeneratorTests(unittest.TestCase):
    def test_unrelated_sequences_use_primitive_steps(self) -> None:
        rendered = units("60806040525f3560e01c")
        self.assertIn(".push1", rendered)
        self.assertIn("RD.genMstore", rendered)
        self.assertIn(".calldataload", rendered)
        self.assertIn(".shr", rendered)
        self.assertNotIn("solcSummary", rendered)

    def test_cursor_uses_current_account_map_interface(self) -> None:
        rendered = units("5b00")
        self.assertIn("{σ : AccountMap}", rendered)
        self.assertIn("rdata σ k C", rendered)
        self.assertIn("RDret sampleCode g s0 σ ByteArray.empty", rendered)
        self.assertNotIn("cA", rendered)

    def test_sload_uses_current_map_operations(self) -> None:
        rendered = units("54")
        self.assertIn("σ.get? ee.codeOwner", rendered)
        self.assertIn("ac.storage.getD", rendered)

    def test_new_local_opcodes_and_transient_storage(self) -> None:
        rendered = units("600160025d60015c434445600360020553")
        for step in (".tstore", ".tload", ".number", ".prevrandao",
                     ".gaslimit", ".sdiv", "RD.genMstore8"):
            self.assertIn(step, rendered)
        self.assertIn("tstoreAccountMap ee.codeOwner", rendered)
        self.assertIn("ac.tstorage.getD", rendered)
        self.assertIn("(hperm : ee.perm = true)", rendered)
        self.assertNotIn("Unsupported instruction boundary", rendered)

    def test_cancun_arith_and_account_opcodes(self) -> None:
        rendered = units(
            "600360021d" "6001" "60ff1a" "600060800b"
            "60036002600108" "60036002600109"
            "600131" "60013f" "600140" "48"
            "6020600060405e" "60206000a0")
        for step in (".sar", ".byte", ".signextend", ".addmod", ".mulmod",
                     ".balance", ".extcodehash", ".blockhash", ".basefee",
                     "RD.genMcopy", "RD.genLog0"):
            self.assertIn(step, rendered)
        self.assertIn("balanceWord", rendered)
        self.assertIn("extCodeHashWord", rendered)
        self.assertIn("blockHashWord ee", rendered)
        self.assertIn("Mmcopy aw", rendered)
        self.assertIn("(hperm : ee.perm = true)", rendered)
        self.assertNotIn("Unsupported instruction boundary", rendered)
        # Without warm/cold operations the block keeps exact counters, so the MCOPY cost shows.
        rendered = units("6020600060405e")
        self.assertIn("RD.genMcopy", rendered)
        self.assertIn("mcopyExpansionCost aw", rendered)

    def test_immutable_mode_uses_deployed_code_and_symbolic_push(self) -> None:
        code = bytes([0x7F, *([0] * 32), 0x56])
        sites = rd.validate_immutable_sites(
            [{"offset": 1, "length": 32, "key": "owner"}], code)
        rendered = rd.generate(code, "imm", "template", ["Contract.Immutables"],
                               immutable_sites=sites, layout_term="Contract.layout")
        self.assertIn("RD (Contract.layout.runtime template immWords) ee g s0", rendered)
        self.assertNotIn("def immutableLayout", rendered)
        self.assertIn('immWords "owner"', rendered)
        self.assertIn("Layout.decodeSite", rendered)
        self.assertIn("immutable_decode(", rendered)
        self.assertIn("theorem immutableLayout_inBounds", rendered)
        self.assertIn("theorem immutableTemplate_size64", rendered)
        self.assertIn("theorem immutableDecode_0", rendered)
        self.assertNotIn("theorem immutableDecode_33", rendered)
        self.assertIn("(D_J (Contract.layout.runtime template immWords) 0)", rendered)
        self.assertIn("immutableRuntime_size", rendered)

    def test_listing_mode_runs_over_the_listing(self) -> None:
        code = bytes.fromhex("60806040525f3560e01c5b5033ff")
        listing = rd.Listing("Sample.Listing", rd.listing_positions(code))
        rendered = units(code.hex(), listing=listing)
        # the first block: entered at instruction 0 of section 0, seven instructions
        self.assertIn("Reasoning.Listing.RDL.enter (Sample.Listing.decodes_code (t := 0) rfl) 0 0 rfl [] h",
                      rendered)
        self.assertIn("have r := e.run 7 [] 2 rfl rfl hstack trivial", rendered)
        self.assertNotIn("native_decide", rendered)
        # the second block starts at the JUMPDEST at 10; POP is its instruction 1
        self.assertIn("(t := 10) rfl) 0 10 rfl [x0] h", rendered)
        self.assertEqual(rd.listing_positions(code)[11], (10, 1))

    def test_listing_mode_covers_transient_storage(self) -> None:
        # PUSH0; TLOAD; PUSH0; TSTORE; STOP
        code = bytes.fromhex("5f5c5f5d00")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        self.assertIn("Sample.Listing.decodes_code (t := 0) rfl", rendered)
        self.assertIn("hperm", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_covers_mod_sdiv_mcopy(self) -> None:
        # PUSH0; PUSH0; MOD; PUSH0; SDIV; PUSH0; PUSH0; PUSH0; MCOPY; STOP
        code = bytes.fromhex("5f5f065f055f5f5f5e00")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        self.assertIn("Sample.Listing.decodes_code (t := 0) rfl", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_covers_byte(self) -> None:
        # PUSH0; PUSH0; BYTE; STOP
        code = bytes.fromhex("5f5f1a00")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        self.assertIn("Sample.Listing.decodes_code (t := 0) rfl", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_covers_sar_signextend_mulmod(self) -> None:
        # PUSH0; PUSH0; SAR; PUSH0; SIGNEXTEND; PUSH0; PUSH0; MULMOD; STOP
        code = bytes.fromhex("5f5f1d5f0b5f5f0900")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        self.assertIn("Sample.Listing.decodes_code (t := 0) rfl", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_covers_exp(self) -> None:
        # PUSH0; PUSH0; EXP; STOP
        code = bytes.fromhex("5f5f0a00")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        self.assertIn("Sample.Listing.decodes_code (t := 0) rfl", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_covers_basefee_and_mstore8(self) -> None:
        # BASEFEE; PUSH0; MSTORE8; STOP
        code = bytes.fromhex("485f5300")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        self.assertIn("Sample.Listing.decodes_code (t := 0) rfl", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_copies_the_whole_return_data(self) -> None:
        # RETURNDATASIZE; PUSH0; PUSH0; RETURNDATACOPY; RETURNDATASIZE; PUSH0; REVERT
        code = bytes.fromhex("3d5f5f3e3d5ffd")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        self.assertIn("⟨trivial, (returnDataCopyFullGuard rdata)⟩", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_keeps_the_statement(self) -> None:
        code = "60806040525f3560e01c"
        listing = rd.Listing("Sample.Listing", rd.listing_positions(bytes.fromhex(code)))
        statement = lambda text: text.split(" := by")[0]
        self.assertEqual(statement(units(code)), statement(units(code, listing=listing)))

    def test_listing_mode_needs_a_tail_for_creation_code(self) -> None:
        listing = rd.Listing("Sample.Listing", {})
        with self.assertRaises(ValueError):
            units("6000", creation_code=True, listing=listing)

    def test_listing_mode_for_creation_code_passes_the_tail(self) -> None:
        code = bytes.fromhex("5b600356")
        listing = rd.Listing.of("Sample.CreationListing", code, "tail")
        rendered = units(code.hex(), creation_code=True, listing=listing)
        self.assertIn("Sample.CreationListing.decodes_code tail (t := 0) rfl", rendered)
        # 3 is not the start of a section here, so the hypothesis stays and the chain's lifting
        # of it to the code with its tail is reused
        self.assertIn("r.jumpX (j tail (UInt256.ofNat 3) hvalid)", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_enters_a_cut_short_last_section_through_its_prefix(self) -> None:
        # JUMPDEST, POP, then a PUSH2 with one data byte: the section's two whole instructions
        code = bytes.fromhex("5b506100")
        listing = rd.Listing.of("Sample.CreationListing", code, "tail")
        self.assertEqual((listing.limit, listing.last_count), (0, 2))
        rendered = units(code.hex(), creation_code=True, listing=listing)
        self.assertIn("RDL.enter (Sample.CreationListing.decodes_last tail) 0 0 rfl [x0] h", rendered)
        self.assertNotIn("native_decide", rendered)

    def test_listing_mode_proves_literal_jump_targets(self) -> None:
        # PUSH1 3; JUMP; JUMPDEST; then a jump through a stack word
        code = bytes.fromhex("6003565b56")
        listing = rd.Listing.of("Sample.Listing", code)
        rendered = units(code.hex(), listing=listing)
        first, second = rendered.split("theorem sample_block_3 ")
        # the literal target is looked up in the listing: no hypothesis, neither in the packed form
        self.assertNotIn("hvalid", first)
        self.assertIn("r.jumpX (Sample.Listing.jumpdest_code (t := 3) rfl rfl)", first)
        # a target taken from the stack still needs it
        self.assertIn("(hvalid : (D_J sampleCode 0).contains x0 = true)", second)
        self.assertIn("r.jumpX hvalid", second)
        # without a listing the statement is as before
        self.assertIn("(hvalid : (D_J sampleCode 0).contains (UInt256.ofNat 3) = true)", units(code.hex()))

    def test_listing_file_is_imported_once_under_its_namespace(self) -> None:
        # `Bytecode.lean` holds the listing `Sample.Listing` and defines the bytecode constant:
        # the summaries name the namespace and import the file once, after the runner.
        code = bytes.fromhex("6003565b00")
        listing = rd.Listing.of("Sample.Listing", code, None, "Sample.Bytecode")
        units_ = rd.generate_unit_records(code, "sample", "Sample.sampleBytecode", listing=listing)
        text = rd.render_module("sample", ["Sample.Bytecode", "Other"], units_, listing=listing)
        imports = [line for line in text.splitlines() if line.startswith("import ")]
        self.assertEqual(imports, ["import Reasoning.Reach", "import Other",
                                   "import Reasoning.Listing.Run", "import Sample.Bytecode"])
        self.assertIn("Sample.Listing.jumpdest_code (t := 3) rfl rfl", text)
        self.assertNotIn("Sample.Bytecode.jumpdest_code", text)

    def test_directory_listing_by_content(self) -> None:
        root = Path(__file__).resolve().parent.parent
        morpho = root / "Benchmarks/Morpho/MorphoBlue"
        module = "Benchmarks.Morpho.MorphoBlue"
        runtime = bytes.fromhex((morpho / "runtime.hex").read_text().strip())
        listing = rd.directory_listing(morpho, module, runtime)
        self.assertEqual((listing.module, listing.lean_import, listing.tail),
                         (f"{module}.Listing", f"{module}.Bytecode", None))
        creation = bytes.fromhex((morpho / "creation.hex").read_text().strip())
        ctor = rd.directory_listing(morpho, module, creation, creation=True)
        self.assertEqual((ctor.module, ctor.lean_import, ctor.tail),
                         (f"{module}.CreationListing", f"{module}.CreationBytecode", "tail"))
        self.assertEqual(rd.bytecode_imports(morpho, module), [f"{module}.Bytecode"])
        self.assertEqual(rd.bytecode_imports(morpho, module, creation=True),
                         [f"{module}.CreationBytecode"])
        # a directory without the file has no listing and nothing to import
        empty = root / "Examples/CtorStore"
        self.assertIsNone(rd.directory_listing(empty, "Examples.CtorStore", b"", creation=True))
        self.assertEqual(rd.bytecode_imports(empty, "Examples.CtorStore", creation=True), [])
        # the command line's `--listing <module>` reads the namespace from the file
        self.assertEqual(rd.listing_of_module(f"{module}.Bytecode", runtime).module,
                         f"{module}.Listing")

    def test_immutable_mode_requires_imported_layout_term(self) -> None:
        with self.assertRaisesRegex(ValueError, "imported Lean layout term"):
            rd.generate(bytes.fromhex("5b00"), "imm", "template", [],
                        immutable_sites={})

    def test_runtime_suffix_reads_appended_data_symbolically(self) -> None:
        # CODECOPY reads 32 bytes starting at the end of the 10-byte template.
        code = bytes.fromhex("6020600a600039600051")
        rendered = rd.generate(code, "suffix", "template", [],
                               runtime_suffix=True)
        self.assertIn("{suffix : ByteArray}", rendered)
        self.assertIn("RD (template ++ suffix) ee g s0", rendered)
        self.assertIn("(template ++ suffix).write", rendered)
        self.assertIn("append_decode(template, suffix,", rendered)
        self.assertNotIn("immWords", rendered)
        self.assertNotIn("Layout.runtime", rendered)

    def test_runtime_suffix_covers_codesize(self) -> None:
        rendered = rd.generate(bytes.fromhex("38"), "suffix", "template", [],
                               runtime_suffix=True)
        self.assertIn("(template ++ suffix).size", rendered)
        self.assertIn("(suffix := suffix)", rendered)

    def test_runtime_suffix_is_exclusive_with_splicing(self) -> None:
        with self.assertRaisesRegex(ValueError, "separate"):
            rd.generate(bytes.fromhex("5b00"), "suffix", "template", [],
                        runtime_suffix=True, immutable_sites={},
                        layout_term="Contract.layout")

    def test_immutable_layout_rejects_non_push_payload(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a PUSH32 payload"):
            rd.validate_immutable_sites(
                [{"offset": 2, "length": 32, "key": "owner"}],
                bytes([0x7F, *([0] * 32)]))

    def test_immutable_layout_rejects_width_mismatched_to_opcode(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a PUSH20 payload"):
            rd.validate_immutable_sites(
                [{"offset": 1, "length": 20, "key": "owner"}],
                bytes([0x7F, *([0] * 32)]))
        with self.assertRaisesRegex(ValueError, "length 20 or 32"):
            rd.validate_immutable_sites(
                [{"offset": 1, "length": 21, "key": "owner"}],
                bytes([0x74, *([0] * 21)]))

    def test_immutable_layout_accepts_push20(self) -> None:
        code = bytes([0x73, *([0] * 20), 0x50, 0x00])
        sites = rd.validate_immutable_sites(
            [{"offset": 1, "length": 20, "key": "owner"}], code)
        rendered = rd.generate(code, "imm20", "template", ["Contract.Immutables"],
                               immutable_sites=sites, layout_term="Contract.layout")
        self.assertIn("RD (Contract.layout.runtimeN template immWords)", rendered)
        self.assertIn('Layout.siteWord 20 (immWords "owner")', rendered)
        self.assertIn("Layout.decodeSite20", rendered)
        self.assertIn("immutable_decode_n(", rendered)

    def test_full_copy_variants_discharge_guard(self) -> None:
        variants = (
            "3d5f5f3e", "3d5f803e", "3d5f60003e", "3d60005f3e",
            "3d6000803e", "3d600060003e", "3d6100005f3e",
            "3d5f6100003e", "3d610000803e", "3d610000620000003e",
        )
        for code in variants:
            with self.subTest(code=code):
                rendered = units(code)
                self.assertIn(".returndatasize", rendered)
                self.assertIn("RD.genReturndatacopy", rendered)
                self.assertIn("returnDataCopyFullGuard rdata", rendered)
                self.assertNotIn("genReturndatacopyFull", rendered)
                self.assertNotIn("hguard", rendered)

    def test_generic_copy_keeps_semantic_guard(self) -> None:
        rendered = units("3e")
        self.assertIn("(hguard0 :", rendered)
        self.assertIn("RD.genReturndatacopy", rendered)

    def test_every_push_width_has_a_generator_step(self) -> None:
        for width in range(1, 33):
            with self.subTest(width=width):
                code = bytes([0x5F + width, *([width] * width)])
                rendered = "\n".join(rd.generate_units(
                    code, "push", "pushCode", keep_metadata=True,
                    fail_on_unsupported=True,
                ))
                step = f".push{width} " if width in {1, 2, 4, 20} else ".pushConst "
                self.assertIn(step, rendered)
                self.assertNotIn("Unsupported instruction boundary", rendered)

    def test_incomplete_push_is_explicit_boundary(self) -> None:
        rendered = units("7f01")
        self.assertIn("Unsupported instruction boundary at pc 0: push32", rendered)

    def test_copy_is_not_split_by_small_bound(self) -> None:
        rendered = units("3d5f5f3e", max_summary_instructions=2)
        self.assertEqual(1, rendered.count("/-- Automatically generated RD summary"))
        self.assertIn("returnDataCopyFullGuard rdata", rendered)

    def test_creation_mode_lifts_concrete_decodes(self) -> None:
        rendered = rd.generate(bytes.fromhex("600100"), "sample", "sampleCode",
                               ["Sample.Bytecode"], keep_metadata=True,
                               creation_code=True)
        self.assertIn("decode_append_left_of_decode", rendered)
        self.assertIn("RD (sampleCode ++ tail)", rendered)

    def test_creation_jump_destination_substitutes_codecopy_source(self) -> None:
        from bytecode_io import read_bytecode
        creation = read_bytecode(Path(__file__).resolve().parent.parent /
                                 "Examples/VyperImmutable/creation.hex")
        rendered = "\n".join(rd.generate_units(
            creation, "sample", "sampleCode", creation_code=True))
        self.assertIn("(j tail (memLoad", rendered)
        self.assertNotIn("__CODE__", rendered)

    def test_index_covers_generated_theorems(self) -> None:
        records = rd.generate_unit_records(bytes.fromhex("6001"), "sample", "sampleCode",
                                           keep_metadata=True)
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "Blocks.lean"
            rd.write_outputs(output, "sample", ["Sample.Bytecode"], records, None)
            index = output.with_suffix(".index").read_text()
            self.assertIn("sample_block_0\tBlocks.lean:", index)
            self.assertIn("sample_block_0_packed\tBlocks.lean:", index)

    def test_shards_and_index_refer_to_same_files(self) -> None:
        records = rd.generate_unit_records(bytes.fromhex("5b5b"), "sample", "sampleCode",
                                           keep_metadata=True)
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "Blocks.lean"
            shards = rd.write_outputs(output, "sample", ["Sample.Bytecode"], records, 1)
            self.assertEqual(2, len(shards))
            index = output.with_suffix(".index").read_text()
            for shard in shards:
                self.assertIn(shard.name + ":", index)

    def test_contract_variants_can_share_summary_prefix(self) -> None:
        records = rd.generate_unit_records(bytes.fromhex("5b5b"), "sample", "sampleCode",
                                           keep_metadata=True)
        for shard_size in (None, 1):
            with self.subTest(shard_size=shard_size), tempfile.TemporaryDirectory() as tmp:
                for variant in ("Main", "Alternate"):
                    namespace = f"Sample.{variant}.RuntimeBlocks"
                    output = Path(tmp) / f"{variant}.lean"
                    paths = rd.write_outputs(output, "sample", ["Sample.Bytecode"], records,
                                             shard_size, namespace=namespace)
                    for path in paths:
                        rendered = path.read_text()
                        self.assertIn(f"namespace {namespace}\n", rendered)
                        self.assertIn(f"end {namespace}\n", rendered)
                        self.assertIn("theorem sample_block_", rendered)
                        self.assertNotIn("namespace sampleBlocks\n", rendered)


def minimal_listing(module: str, constant: str, layout: str | None = None,
                    layout_import: str | None = None) -> str:
    """Just enough of a listing (`gen_listing.py`) for the benchmark discovery."""
    imports = f"import {layout_import}\n" if layout_import else ""
    lay = f"\n  layout {layout} blocks sampleBlocks" if layout else ""
    return (f"{imports}import Reasoning.Listing.FromHex\n\nnamespace {module}.Listing\n\n"
            f'listing_from_hex "runtime.hex" sha256 "{"0" * 64}"\n'
            f"  bytecode {constant}{lay}\n\nend {module}.Listing\n")


class BenchmarkInputTests(unittest.TestCase):
    def test_discovery_is_independent_of_temporary_scaffolds(self) -> None:
        for with_scaffolds in (False, True):
            with self.subTest(with_scaffolds=with_scaffolds), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "Benchmarks"
                expected = [root / "Dss/End/Bytecode.lean",
                            root / "UniswapV3/Pool/Bytecode.lean"]
                paths = expected + ([root / "Scaffolds/Temporary/Bytecode.lean"]
                                    if with_scaffolds else [])
                for path in reversed(paths):
                    path.parent.mkdir(parents=True)
                    path.write_text(minimal_listing("M", "M.mBytecode"), encoding="utf-8")
                # a Bytecode.lean that is not a listing is not a benchmark
                (root / "Other").mkdir()
                (root / "Other/Bytecode.lean").write_text("-- not a listing\n")
                self.assertEqual(benchmarks.benchmark_paths(root), expected)

    def test_inputs_come_from_the_listing(self) -> None:
        # the constant, the blocks namespace and the layout (term and module) are the listing's
        for layout, layout_import in ((None, None),
                                      ("Sample.Immutables.immutableLayout", "Benchmarks.Sample.Immutables"),
                                      ("Sample.immutableLayout", "Benchmarks.Sample.ImmutableCode")):
            with self.subTest(layout=layout), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                path = root / "Benchmarks/Sample/Bytecode.lean"
                path.parent.mkdir(parents=True)
                path.write_text(minimal_listing("Benchmarks.Sample", "Sample.sampleBytecode",
                                                layout, layout_import), encoding="utf-8")
                with patch.object(benchmarks, "ROOT", root):
                    listing, module, layout_module = benchmarks.benchmark_inputs(path)
                self.assertEqual((listing.bytecode, module, layout_module, listing.layout,
                                  listing.blocks),
                                 ("Sample.sampleBytecode", "Benchmarks.Sample.Bytecode",
                                  layout_import, layout, "sampleBlocks" if layout else None))

if __name__ == "__main__":
    unittest.main()

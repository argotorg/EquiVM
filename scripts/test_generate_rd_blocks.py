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

    def test_osaka_clz_requires_the_fork(self) -> None:
        # Two CLZs in one block that ends in STOP: a single summary theorem, whose one fork
        # hypothesis is shared by every CLZ of the block.
        rendered = units("60011e60021e00")
        self.assertEqual(rendered.count("(hfork : ee.fork ≥ .osaka)"), 1)
        self.assertEqual(rendered.count(".clz hfork (by native_decide) (by evm_ov)"), 2)
        self.assertNotIn("Unsupported instruction boundary", rendered)
        # A block that falls through keeps the count on its output stack.
        rendered = units("60011e")
        self.assertIn("(UInt256.clz (UInt256.ofNat 1))", rendered)

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
                    path.touch()
                self.assertEqual(benchmarks.benchmark_paths(root), expected)

    def test_layout_module_supports_both_benchmark_formats(self) -> None:
        for files, expected in (((), None),
                                (("Immutables.lean",), "Immutables.lean"),
                                (("Immutables.lean", "ImmutableCode.lean"), "ImmutableCode.lean")):
            with self.subTest(files=files), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                path = root / "Benchmarks/Sample/Bytecode.lean"
                path.parent.mkdir(parents=True)
                path.write_text("namespace Sample\ndef sampleBytecode : ByteArray := ⟨#[0]⟩\n",
                                encoding="utf-8")
                for name in files:
                    path.with_name(name).touch()
                with patch.object(benchmarks, "ROOT", root):
                    self.assertEqual(
                        benchmarks.benchmark_inputs(path),
                        ("Sample.sampleBytecode", "Benchmarks.Sample.Bytecode",
                         path.with_name(expected) if expected else None),
                    )


if __name__ == "__main__":
    unittest.main()

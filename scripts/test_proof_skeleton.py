#!/usr/bin/env python3
"""Checks for the skeleton generator's dispatcher path analysis (no Lean needed)."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_rd_blocks as rd  # noqa: E402
import proof_skeleton as ps  # noqa: E402
from bytecode_io import read_bytecode  # noqa: E402
from evm_tools import dispatcher  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


def fake_contract(directory: Path, name: str, prefix: str) -> ps.Contract:
    return ps.Contract(directory, name, "X", "X", prefix, [], False, False, [], (0, 8, 0), [],
                       read_bytecode(directory / "runtime.hex"))


class PathTests(unittest.TestCase):
    def check_contract(self, directory: str, name: str, prefix: str, guard: bool) -> None:
        c = fake_contract(ROOT / directory, name, prefix)
        d = ps.Dispatcher(c, None)
        gen = ps.ProofGen(c, d)
        self.assertEqual(gen.global_guard, guard)
        disp = dispatcher(rd.disassemble(rd.strip_solidity_metadata(c.runtime)))
        self.assertTrue(disp.arms)
        for arm in disp.arms:
            steps = d.run(ps.Env(0, "big", arm.selector), arm.target)
            self.assertTrue(steps and not isinstance(steps[-1], ps.Fork))
            self.assertIsNone(steps[-1].summary.terminal)
            self.assertEqual(steps[-1].branch, "taken")
        # the short-calldata path reverts (these contracts have no fallback)
        short = d.run(ps.Env(0, "small", "nomatch"), None)
        self.assertIn("RDrev", short[-1].summary.terminal or "")
        # every no-match leaf reverts
        leaves = 0
        def explore(decisions):
            nonlocal leaves
            steps = gen.run_with_decisions(ps.Env(0, "big", "nomatch"), decisions)
            if isinstance(steps[-1], ps.Fork):
                fork = steps[-1]
                explore(decisions + [(fork.jumpi_pc, False)])
                explore(decisions + [(fork.jumpi_pc, True)])
            else:
                leaves += 1
                self.assertIn("RDrev", steps[-1].summary.terminal or "")
        explore([])
        self.assertGreaterEqual(leaves, 1)

    def test_pot_binary_search_with_guard(self) -> None:
        self.check_contract("Benchmarks/Dss/Pot", "Pot", "pot", True)

    def test_morpho_via_ir_without_guard(self) -> None:
        self.check_contract("Benchmarks/Morpho/MorphoBlue", "Morpho", "morpho", False)

    def test_tiny_immutable_linear(self) -> None:
        self.check_contract("Examples/TinyImmutable", "TinyImmutable", "tinyImmutable", True)


class ImmutableTests(unittest.TestCase):
    def test_jump_table_lemma_in_summary_form(self) -> None:
        c = fake_contract(ROOT / "Examples/TinyImmutable", "TinyImmutable", "tinyImmutable")
        c.immutables = [ps.Immutable("owner", "address"), ps.Immutable("scale", "uint256")]
        common = ps.render_common(c)
        # jump validity from the listing, no `native_decide` jump table
        self.assertIn("theorem tinyImmutableJumpdest (v : TinyImmutableImmutables)", common)
        self.assertIn("(D_J (deployedRuntime v) 0).contains pc = true", common)
        self.assertIn("Listing.jumpdest_code (wordsOf (immStore v)) h hjd pc.val.isLt", common)
        self.assertNotIn("native_decide", common)
        self.assertNotIn("PatchedValidJumps", common)
        gen = ps.ProofGen(c, ps.Dispatcher(c, None))
        self.assertEqual(gen.valid_proof(), "(by exact tinyImmutableJumpdest v rfl rfl)")

    def test_plain_contract_jumpdest_and_creation_import(self) -> None:
        c = fake_contract(ROOT / "Examples/TinyImmutable", "TinyImmutable", "tinyImmutable")
        common = ps.render_common(c)
        self.assertIn("(D_J tinyImmutableBytecode 0).contains pc = true", common)
        self.assertIn("  have hj := Listing.jumpdest_code h hjd pc.val.isLt", common)
        self.assertNotIn("native_decide", common)
        self.assertIn("import X.CreationBytecode", ps.render_constructor(c))

    def test_blocks_without_hvalid_get_no_argument(self) -> None:
        # Morpho's runtime blocks are proved from its listing: a literal jump target needs no
        # `hvalid`, and the dispatcher chains pass none for it.
        directory = ROOT / "Benchmarks/Morpho/MorphoBlue"
        hyps = ps.block_hypotheses(directory)
        self.assertIsNotNone(hyps)
        self.assertEqual(hyps["morpho_block_0_taken"], ["hstack", "hcond", "h"])
        c = fake_contract(directory, "Morpho", "morpho")
        c.block_hyps = hyps
        gen = ps.ProofGen(c, ps.Dispatcher(c, None))
        self.assertFalse(gen.takes("morpho_block_0_taken", "hvalid"))
        c.block_hyps = None
        self.assertTrue(gen.takes("morpho_block_0_taken", "hvalid"))


class VyperSpecTests(unittest.TestCase):
    def test_generated_config_uses_vyper_storage_and_abi(self) -> None:
        c = fake_contract(ROOT / "Examples/VyperImmutable", "Immutable", "immutable")
        c.compiler_kind = "vyper"
        text = ps.render_spec(c)
        self.assertIn("import Stele.MetaVyperLayout", text)
        self.assertIn("vyperStorage! [contract.storage]", text)
        self.assertIn("withMode DecodeMode.vyper", text)
        self.assertIn("withVyperABI", text)
        self.assertNotIn("solidityStorage!", text)

    def test_vyper_skeleton_proves_the_jump_table_dispatcher(self) -> None:
        source = ROOT / "Examples/VyperImmutable"
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for name in ("Immutable.build.json", "runtime.hex", "Selectors.lean"):
                (directory / name).write_bytes((source / name).read_bytes())
            (directory / "SpecSyntax.lean").write_text(
                "def contractSyntax : ContractDecl := solidity% contract Immutable {}\n")
            self.assertEqual(ps.main(["--dir", tmp, "--module", "Test.Vyper", "--only", "Spec"]), 0)
            self.assertIn("vyperStorage!", (directory / "Spec.lean").read_text())
            self.assertFalse((directory / "Dispatch.lean").exists())
            self.assertEqual(ps.main(["--dir", tmp, "--module", "Test.Vyper"]), 0)
            correct = (directory / "Correct.lean").read_text()
            self.assertIn("runtimeRefinement config", correct)
            self.assertNotIn("runtimeRefinementWithWF", correct)
            self.assertEqual(ps.main(["--dir", tmp, "--module", "Test.Vyper", "--force", "--wf", "storageWF"]), 0)
            correct = (directory / "Correct.lean").read_text()
            self.assertIn("runtimeRefinementWithWF storageWF noGasBound config", correct)
            self.assertIn("contractRefinementWF storageWF noGasBound config", correct)
            self.assertIn("hwf hcode hsize", correct)
            self.assertIn("def storageWF : StorageWF := fun _ _ => True", (directory / "Common.lean").read_text())
            self.assertIn("(hwf : storageWF σ I)", (directory / "Read.lean").read_text())
            self.assertEqual(ps.main(["--dir", tmp, "--module", "Test.Vyper", "--force"]), 0)
            dispatch = (directory / "Dispatch.lean").read_text()
            table = ps.vyper_table((source / "runtime.hex").read_bytes() and
                                   bytes.fromhex((source / "runtime.hex").read_text().strip()))
            self.assertIsNotNone(table)
            self.assertIn("def immutableDispatchMem", dispatch)
            for m in range(table.buckets):
                self.assertIn(f"theorem immutableBucket{m} ", dispatch)
            self.assertIn("theorem immutableReachReadBody", dispatch)
            self.assertIn("theorem immutableX_noMatch", dispatch)
            self.assertIn("theorem immutableX_short", dispatch)
            self.assertNotIn("sorry", dispatch)
            common = (directory / "Common.lean").read_text()
            self.assertIn("deployed_of_fit", common)
            self.assertIn("import Reasoning.VyperDispatch", common)
            correct = (directory / "Correct.lean").read_text()
            self.assertIn(".of_runtime immutableConstructorCorrect immutableCorrect", correct)
            self.assertNotIn("sorry", correct)


class SpellingTests(unittest.TestCase):
    def test_selector_term_is_rewritten(self) -> None:
        c = fake_contract(ROOT / "Examples/TinyImmutable", "TinyImmutable", "tinyImmutable")
        gen = ps.ProofGen(c, ps.Dispatcher(c, None))
        term = ("(UInt256.eq (UInt256.ofNat 7) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes "
                "(⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0)")
        self.assertEqual(gen.lib_spelling(term), "(UInt256.eq ⟨7⟩ (solcSelectorWord I)) ≠ ⟨0⟩")


if __name__ == "__main__":
    unittest.main()

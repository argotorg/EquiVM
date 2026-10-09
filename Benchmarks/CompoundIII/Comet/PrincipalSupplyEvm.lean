import Benchmarks.CompoundIII.Comet.PrincipalMagnitudeModel
import Benchmarks.CompoundIII.Comet.PrincipalCastEvm
import Benchmarks.CompoundIII.Comet.ArithmeticRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_059
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometPrincipalSupply {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw index present ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hindex : index.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12917⟩ (index :: present :: ret :: R)
      mem aw rdata σ k C) :
    (PrincipalMagnitudeFits false index present ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (principalMagnitudeWord false index present :: R) mem aw rdata σ k' C') ∨
    (¬ PrincipalMagnitudeFits false index present ∧ RDrev (deployedRuntime v) g s0) := by
  have hclean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
      index = index := by
    rw [u256_land_comm]; exact u256LandMaskCleanOfToNat _ _ (bits := 64) rfl hindex
  by_cases hm : present.toNat * 1000000000000000 < UInt256.size
  · have r1 := cometWithExtendedAssetList_block_12917_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (checkedMulGuard_zero hm) h
    by_cases hi : index ≠ ⟨0⟩
    · have r2 := cometWithExtendedAssetList_block_12947_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 6 ≤ 1024; omega)
        (by rw [hclean]; exact isZero_eq_zero_of_ne hi) r1
      dsimp only [cometWithExtendedAssetList_block_12947_fallthrough_stack] at r2
      rw [hclean] at r2
      have r3 := cometWithExtendedAssetList_block_12964
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      rcases cometSafe104 (v := v) (by change R.length + 1 + 6 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
        ⟨hq, k4, C4, r4⟩ | ⟨hq, hr⟩
      · have r5 := cometWithExtendedAssetList_block_2425
          (immWords := wordsOf (immStore v)) (by omega) hret r4
        exact Or.inl ⟨⟨⟨hm, (by intro hh; cases hh), hi⟩, hq⟩, _, _, r5⟩
      · exact Or.inr ⟨fun hf ↦ hq hf.2, hr⟩
    · have hz : index = ⟨0⟩ := not_ne_iff.mp hi
      have r2 := cometWithExtendedAssetList_block_12947_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 6 ≤ 1024; omega)
        (by rw [hclean, hz]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := cometWithExtendedAssetList_block_12971
        (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      exact Or.inr ⟨fun hf ↦ hi hf.1.2.2,
        cometWithExtendedAssetList_block_9151 (immWords := wordsOf (immStore v))
          (by change R.length + 5 + 2 ≤ 1024; omega) r3⟩
  · have r1 := cometWithExtendedAssetList_block_12917_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (checkedMulGuard_nonzero (by change UInt256.size ≤ present.toNat * 1000000000000000; omega))
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_12984
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨fun hf ↦ hm hf.1.1,
      cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
        (by change R.length + 5 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet

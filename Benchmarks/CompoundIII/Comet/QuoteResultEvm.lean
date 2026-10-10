import Benchmarks.CompoundIII.Comet.QuoteModel
import Benchmarks.CompoundIII.Comet.AssetMemory
import Benchmarks.CompoundIII.Comet.CheckedDivEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_055
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_081

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometQuoteResult {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {price amount discounted ptr free ret : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hm : AssetMemory mem ptr free out) (hv : AssetValid out)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12057⟩
      (price :: amount :: ⟨18155⟩ :: ⟨96⟩ ::
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
        ptr :: ⟨18165⟩ :: discounted :: ⟨2425⟩ :: ret :: R) mem aw rdata σ k C) :
    (QuoteResultValid v out amount price discounted ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
        (quoteResultWord v out amount price discounted :: R) mem aw' rdata σ k' C') ∨
    (¬ QuoteResultValid v out amount price discounted ∧ RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_12057 (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hm1 : price.toNat * amount.toNat < UInt256.size
  · obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v)
      (by change R.length + 7 + 5 ≤ 1024; omega) hm1
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_18155 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have hl : memLoad (ptr + (⟨96⟩ : UInt256)) mem = calldataWord out 96 := hm.words 3 (by decide)
    have hc : UInt256.land (calldataWord out 96)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = calldataWord out 96 := by
      rw [u256_land_comm]
      exact mask64Clean _ hv.2.2.2.2.1
    simp only [cometWithExtendedAssetList_block_18155_stack, hl, hc] at r3
    by_cases hm2 : (UInt256.mul price amount).toNat * (calldataWord out 96).toNat < UInt256.size
    · obtain ⟨k4, C4, r4⟩ := cometCheckedMul (v := v)
        (by change R.length + 3 + 5 ≤ 1024; omega) hm2
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      by_cases hn1 : discounted ≠ ⟨0⟩
      · have r5 := cometWithExtendedAssetList_block_18165_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
          (isZero_eq_zero_of_ne hn1) r4
        have r6 := cometWithExtendedAssetList_block_18173 (immWords := wordsOf (immStore v))
          (by change R.length + 2 + 3 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
        simp only [cometWithExtendedAssetList_block_18173_stack,
          cometWithExtendedAssetList_block_18165_fallthrough_stack,
          wordsOf_immStore_baseScale, wordOfInt_ofNat_toNat] at r6
        have r7 := cometCheckedDiv (v := v) (by change R.length + 1 + 6 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
        by_cases hn2 : v.baseScale ≠ ⟨0⟩
        · left; refine ⟨⟨hm1, hm2, hn1, hn2⟩, ?_⟩
          rw [if_pos hn2] at r7
          obtain ⟨k7, C7, r7⟩ := r7
          have r8 := cometWithExtendedAssetList_block_2425 (immWords := wordsOf (immStore v))
            (by omega) hret r7
          exact ⟨_, _, _, r8⟩
        · right; refine ⟨fun h ↦ hn2 h.2.2.2, ?_⟩
          rw [if_neg hn2] at r7
          exact r7
      · right; refine ⟨fun h ↦ hn1 h.2.2.1, ?_⟩
        have hz : discounted = ⟨0⟩ := not_ne_iff.mp hn1
        have r5 := cometWithExtendedAssetList_block_18165_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
          (by rw [hz]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
        have r6 := cometWithExtendedAssetList_block_18213 (immWords := wordsOf (immStore v))
          (by change R.length + 4 + 2 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
        exact cometWithExtendedAssetList_block_9151 (immWords := wordsOf (immStore v))
          (by change R.length + 4 + 2 ≤ 1024; omega) r6
    · right; refine ⟨fun h ↦ hm2 h.2.1, ?_⟩
      exact cometCheckedMul_revert (v := v) (by change R.length + 4 + 4 ≤ 1024; omega)
        (le_of_not_gt hm2) r3
  · right; refine ⟨fun h ↦ hm1 h.1, ?_⟩
    exact cometCheckedMul_revert (v := v) (by change R.length + 8 + 4 ≤ 1024; omega)
      (le_of_not_gt hm1) r1

end Benchmarks.CompoundIII.Comet

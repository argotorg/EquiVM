import Benchmarks.CompoundIII.Comet.TransferReturnEvm
import Benchmarks.CompoundIII.Comet.EmptyTupleDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_061
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_062
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_063

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferInReturnWord {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨13443⟩ (value :: R) mem aw out σ k C) :
    if value = ⟨0⟩ then RDrev (deployedRuntime v) g s0
    else ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨13449⟩ R mem aw out σ k' C' := by
  split_ifs with hz
  · have r1 := cometWithExtendedAssetList_block_13443_taken
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hz]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact cometWithExtendedAssetList_block_13545 (immWords := wordsOf (immStore v))
      hstack r1
  · have r1 := cometWithExtendedAssetList_block_13443_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (isZero_eq_zero_of_ne hz) h
    exact ⟨_, _, r1⟩

theorem cometTransferInReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {dummy asset : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hh : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨13414⟩ (dummy :: asset :: ⟨32⟩ :: R)
      mem aw out σ k C) :
    (TransferReturnValid out ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨13449⟩ (asset :: ⟨32⟩ :: R)
        (transferReplyMemory mem out) aw' out σ k' C') ∨
    (¬ TransferReturnValid out ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hz : out.size = 0
  · have r1 := cometWithExtendedAssetList_block_13414_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
      (by rw [hz]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_13563 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hr := cometTransferInReturnWord (v := v) (by change R.length + 2 + 3 ≤ 1024; omega) r2
    rw [if_neg (by decide)] at hr
    obtain ⟨k3, C3, r3⟩ := hr
    exact Or.inl ⟨Or.inl hz, _, _, _, by simpa only [transferReplyMemory, if_pos hz] using r3⟩
  · have hwsize : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hn := congrArg UInt256.toNat he
      change out.size % UInt256.size = 0 at hn
      rw [Nat.mod_eq_of_lt hh] at hn
      exact hz hn
    have r1 := cometWithExtendedAssetList_block_13414_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
      (isZero_eq_zero_of_ne hwsize) h
    by_cases h32 : out.size = 32
    · have r2 := cometWithExtendedAssetList_block_13423_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
        (by rw [h32]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := cometWithExtendedAssetList_block_13434 (immWords := wordsOf (immStore v))
        (by omega) (by change 0 + 32 ≤ out.size; omega) r2
      change RD _ _ _ _ ⟨13443⟩
        (memLoad ⟨0⟩ (out.write 0 mem 0 32) :: asset :: ⟨32⟩ :: R) _ _ _ _ _ _ at r3
      rw [returndataCopyWord mem out (by omega)] at r3
      have hr := cometTransferInReturnWord (v := v) (by change R.length + 2 + 3 ≤ 1024; omega) r3
      by_cases hw : calldataWord out 0 = ⟨0⟩
      · rw [if_pos hw] at hr
        exact Or.inr ⟨by simp [TransferReturnValid, hz, hw], hr⟩
      · rw [if_neg hw] at hr
        obtain ⟨k4, C4, r4⟩ := hr
        exact Or.inl ⟨Or.inr ⟨h32, hw⟩, _, _, _,
          by simpa only [transferReplyMemory, if_neg hz] using r4⟩
    · have hne : (UInt256.ofNat 32) ≠ UInt256.ofNat out.size := by
        intro he
        have hn := congrArg UInt256.toNat he
        change 32 = out.size % UInt256.size at hn
        rw [Nat.mod_eq_of_lt hh] at hn
        exact h32 hn.symm
      have r2 := cometWithExtendedAssetList_block_13423_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
        (u256_eq_of_ne hne) r1
      exact Or.inr ⟨by simp [TransferReturnValid, hz, h32],
        cometWithExtendedAssetList_block_13430 (immWords := wordsOf (immStore v))
          (by change R.length + 2 + 2 ≤ 1024; omega) r2⟩

theorem cometTransferInResponse {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr asset : UInt256} {R : List UInt256} {z : Bool}
    (hstack : R.length + 10 ≤ 1024) (hh : out.size < UInt256.size)
    (hb : ptr.toNat < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨13403⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ptr :: asset :: ⟨32⟩ :: R) mem aw out σ k C) :
    (z = true ∧ TransferReturnValid out ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨13449⟩ (asset :: ⟨32⟩ :: R)
        (transferReplyMemory (writeWord mem 64 ptr) out) aw' out σ k' C') ∨
    (¬ (z = true ∧ TransferReturnValid out) ∧ RDrev (deployedRuntime v) g s0) := by
  cases z with
  | false =>
    have r1 := cometWithExtendedAssetList_block_13403_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_13593 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨by simp, cometWithExtendedAssetList_block_7166
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
      (by change 0 + out.size % UInt256.size ≤ out.size
          simpa using Nat.mod_le out.size UInt256.size) r2⟩
  | true =>
    have r1 := cometWithExtendedAssetList_block_13403_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
      (by decide) h
    have r2 := cometWithExtendedAssetList_block_13409_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_13572 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    obtain ⟨aw4, k4, C4, r4⟩ := cometAllocateBounded (v := v) (bound := 0)
      (by change R.length + 4 + 6 ≤ 1024; omega) (by decide) (by simpa using hb)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    have hp : allocationEnd ptr (UInt256.ofNat 0) = ptr := by
      change ptr + ⟨0⟩ = ptr
      exact u256_add_zero ptr
    rw [hp] at r4
    obtain ⟨k5, C5, r5⟩ := cometDecodeEmptyTuple (v := v)
      (by change R.length + 2 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_13587 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    rcases cometTransferInReturn (v := v) (by omega) hh r6 with ⟨hv, hr⟩ | ⟨hv, hr⟩
    · exact Or.inl ⟨rfl, hv, hr⟩
    · exact Or.inr ⟨fun h ↦ hv h.2, hr⟩

end Benchmarks.CompoundIII.Comet

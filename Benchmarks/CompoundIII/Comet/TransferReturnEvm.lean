import Benchmarks.CompoundIII.Comet.TransferReturnSource
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_074
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_037

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferReplyMemory (mem out : ByteArray) : ByteArray :=
  if out.size = 0 then mem else out.write 0 mem 0 32

-- LIBRARY CANDIDATE: loading the first word after a bounded RETURNDATACOPY to scratch memory.
theorem returndataCopyWord (mem out : ByteArray) (h32 : 32 ≤ out.size) :
    memLoad ⟨0⟩ (out.write 0 mem 0 32) = calldataWord out 0 := by
  apply loadedWord_of_read
  · rw [copyWindow_size out mem 0 0 32 (by decide) (by omega) (by omega)]
    change 0 + 32 ≤ _
    omega
  · have h := copyWindow_read_word out mem 0 0 32 0
      (by decide) (by omega) (by omega) (by decide)
    rw [Nat.zero_add, readWithPadding_eq_extract out 0 (by omega)] at h
    exact h.trans (calldataWord_bytes h32).symm

theorem cometTransferReturnWord {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {value ret : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024) (hv : value ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16216⟩ (value :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret R mem aw out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_16216_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
    (isZero_eq_zero_of_ne hv) h
  exact ⟨_, _, cometWithExtendedAssetList_block_16222 (immWords := wordsOf (immStore v))
    (by omega) hret r1⟩

theorem cometTransferReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {x0 x1 ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hh : out.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16187⟩ (x0 :: x1 :: ret :: ⟨0⟩ :: R)
      mem aw out σ k C) :
    (TransferReturnValid out ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ret R (transferReplyMemory mem out) aw' out σ k' C') ∨
    (¬ TransferReturnValid out ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hz : out.size = 0
  · have r1 := cometWithExtendedAssetList_block_16187_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
      (by rw [hz]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_16241
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨k', C', r3⟩ := cometTransferReturnWord (by omega) (by decide) hret r2
    exact Or.inl ⟨Or.inl hz, _, k', C', by simpa only [transferReplyMemory, if_pos hz] using r3⟩
  · have hwsize : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hn := congrArg UInt256.toNat he
      change out.size % UInt256.size = 0 at hn
      rw [Nat.mod_eq_of_lt hh] at hn
      exact hz hn
    have r1 := cometWithExtendedAssetList_block_16187_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
      (isZero_eq_zero_of_ne hwsize) h
    by_cases h32 : out.size = 32
    · have r2 := cometWithExtendedAssetList_block_16198_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
        (by rw [h32]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := cometWithExtendedAssetList_block_16208
        (immWords := wordsOf (immStore v)) (by omega) (by change 0 + 32 ≤ out.size; omega) r2
      change RD _ _ _ _ ⟨16216⟩
        (memLoad ⟨0⟩ (out.write 0 mem 0 32) :: ret :: R) _ _ _ _ _ _ at r3
      rw [returndataCopyWord mem out (by omega)] at r3
      by_cases hw : calldataWord out 0 = ⟨0⟩
      · have r4 := cometWithExtendedAssetList_block_16216_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
          (by rw [hw]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        exact Or.inr ⟨by simp [TransferReturnValid, hz, hw],
          cometWithExtendedAssetList_block_16223 (immWords := wordsOf (immStore v))
            (by change R.length + 1 + 3 ≤ 1024; omega) r4⟩
      · obtain ⟨k', C', r4⟩ := cometTransferReturnWord (by omega) hw hret r3
        exact Or.inl ⟨Or.inr ⟨h32, hw⟩, _, k', C',
          by simpa only [transferReplyMemory, if_neg hz] using r4⟩
    · have hne : (UInt256.ofNat 32) ≠ UInt256.ofNat out.size := by
        intro he
        have hn := congrArg UInt256.toNat he
        change 32 = out.size % UInt256.size at hn
        rw [Nat.mod_eq_of_lt hh] at hn
        exact h32 hn.symm
      have r2 := cometWithExtendedAssetList_block_16198_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
        (by exact u256_eq_of_ne hne) r1
      exact Or.inr ⟨by simp [TransferReturnValid, hz, h32],
        cometWithExtendedAssetList_block_16205 (immWords := wordsOf (immStore v))
          (by omega) r2⟩

theorem cometTransferResponse {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} {z : Bool}
    (hstack : R.length + 9 ≤ 1024) (hh : out.size < UInt256.size)
    (hb : ptr.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16176⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨0⟩ :: ptr :: ret :: ⟨0⟩ :: R)
      mem aw out σ k C) :
    (z = true ∧ TransferReturnValid out ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ret R
        (transferReplyMemory (writeWord mem 64 ptr) out) aw' out σ k' C') ∨
    (¬ (z = true ∧ TransferReturnValid out) ∧ RDrev (deployedRuntime v) g s0) := by
  cases z with
  | false =>
    have r1 := cometWithExtendedAssetList_block_16176_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_16268
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨by simp, cometWithExtendedAssetList_block_7166
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 4 ≤ 1024; omega)
      (by change 0 + out.size % UInt256.size ≤ out.size
          simpa using Nat.mod_le out.size UInt256.size) r2⟩
  | true =>
    have r1 := cometWithExtendedAssetList_block_16176_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
      (by decide) h
    have r2 := cometWithExtendedAssetList_block_16182_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_16252
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    obtain ⟨aw', k', C', r4⟩ := cometAllocateBounded (v := v) (bound := 0)
      (ptr := ptr) (len := ⟨0⟩) (ret := ⟨16261⟩) (R := ret :: ⟨0⟩ :: R)
      (by change R.length + 2 + 6 ≤ 1024; omega) (by decide) (by simpa using hb)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    have hp : allocationEnd ptr ⟨0⟩ = ptr := by
      change ptr + ⟨0⟩ = ptr
      exact u256_add_zero ptr
    rw [hp] at r4
    have r5 := cometWithExtendedAssetList_block_16261
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    rcases cometTransferReturn (by omega) hh hret r5 with ⟨hv, hr⟩ | ⟨hv, hr⟩
    · exact Or.inl ⟨rfl, hv, hr⟩
    · exact Or.inr ⟨fun hh ↦ hv hh.2, hr⟩

end Benchmarks.CompoundIII.Comet

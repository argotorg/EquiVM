import Benchmarks.CompoundIII.Comet.PrincipalValueModel
import Benchmarks.CompoundIII.Comet.PrincipalBorrowEvm
import Benchmarks.CompoundIII.Comet.SignedNegation
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometPrincipalValue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw present ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12742⟩ (present :: ret :: R) mem aw rdata σ k C) :
    (PrincipalValueFits evm present ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (principalValueWord evm present :: R) mem aw rdata σ k' C') ∨
    (¬ PrincipalValueFits evm present ∧ RDrev (deployedRuntime v) g s0) := by
  have hw0 : solcSlotWordAt (UInt256.ofNat 0) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ := by
    simpa only [hs.env] using (hs.storageRead ⟨0⟩).symm
  have hiS : principalValueIndex evm false = UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) := totalsIndexWord_eq _ false
  have hiB : principalValueIndex evm true = UInt256.land
      (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
        (UInt256.ofNat 64))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) := totalsIndexWord_eq _ true
  by_cases hpos : 0 ≤ signedWord present
  · have hneg : ¬ signedWord present < 0 := by omega
    have hmin : -(2^255 : Int) < signedWord present := by omega
    have r1 := cometWithExtendedAssetList_block_12742_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
      (by rw [signedWord_slt]
          change UInt256.fromBool (decide (signedWord present < 0)) = _
          rw [decide_eq_false hneg]; rfl) h
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_12751
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    change RD _ _ _ _ _ (UInt256.land _ (solcSlotWordAt (UInt256.ofNat 0) σ ee) ::
      present :: ⟨12775⟩ :: ⟨2425⟩ :: ret :: R) _ _ _ _ _ _ at r2
    rw [hw0, u256_land_comm, ← hiS] at r2
    change RD _ _ _ _ _ (principalValueIndex evm false :: present :: ⟨12775⟩ ::
      ⟨2425⟩ :: ret :: R) _ _ _ _ _ _ at r2
    rcases cometPrincipalSupply (v := v) (by change R.length + 2 + 8 ≤ 1024; omega)
        (totalsIndexWord_lt _ false)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2 with
      ⟨hm, k3, C3, r3⟩ | ⟨hm, hr⟩
    · have r4 := cometWithExtendedAssetList_block_12775
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      rcases cometSigned104 (v := v) (by change R.length + 1 + 5 ≤ 1024; omega) hm.2
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4 with
        ⟨hq, k5, C5, r5⟩ | ⟨hq, hr⟩
      · have r6 := cometWithExtendedAssetList_block_2425
          (immWords := wordsOf (immStore v)) (by omega) hret r5
        refine Or.inl ⟨?_, k5 + 3, C5 + 12, ?_⟩
        · exact ⟨hmin, by simpa only [decide_eq_false hneg] using And.intro hm hq⟩
        · simpa only [principalValueWord, if_pos hpos, principalValueMagnitude,
            principalValueAmount, Bool.false_eq_true, if_false] using r6
      · refine Or.inr ⟨?_, hr⟩
        intro hf; exact hq (by simpa only [decide_eq_false hneg] using hf.2.2)
    · refine Or.inr ⟨?_, hr⟩
      intro hf; exact hm (by simpa only [decide_eq_false hneg] using hf.2.1)
  · have hneg : signedWord present < 0 := by omega
    have r1 := cometWithExtendedAssetList_block_12742_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
      (by rw [signedWord_slt]
          change UInt256.fromBool (decide (signedWord present < 0)) ≠ _
          rw [decide_eq_true hneg]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_12780
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    change RD _ _ _ _ _ (present :: ⟨12813⟩ :: UInt256.land
      (UInt256.shiftRight (solcSlotWordAt (UInt256.ofNat 0) σ ee) (UInt256.ofNat 64)) _ ::
      ⟨12775⟩ :: ⟨12873⟩ :: ⟨2425⟩ :: ret :: R) _ _ _ _ _ _ at r2
    rw [hw0, ← hiB] at r2
    change RD _ _ _ _ _ (present :: ⟨12813⟩ :: principalValueIndex evm true ::
      ⟨12775⟩ :: ⟨12873⟩ :: ⟨2425⟩ :: ret :: R) _ _ _ _ _ _ at r2
    rcases cometNegate256 (v := v) (by change R.length + 5 + 4 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2 with
      ⟨hmin, k3, C3, r3⟩ | ⟨hmin, hr⟩
    · rcases cometPrincipalBorrow (v := v) (by change R.length + 3 + 9 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
        ⟨hm, k4, C4, r4⟩ | ⟨hm, hr⟩
      · have r5 := cometWithExtendedAssetList_block_12775
          (immWords := wordsOf (immStore v)) (by change R.length + 4 + 1 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
        rcases cometSigned104 (v := v) (by change R.length + 2 + 5 ≤ 1024; omega) hm.2
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5 with
          ⟨hq, k6, C6, r6⟩ | ⟨hq, hr⟩
        · have r7 := cometWithExtendedAssetList_block_12873
            (immWords := wordsOf (immStore v)) (by change R.length + 3 + 1 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
          obtain ⟨k8, C8, r8⟩ := cometNegate104Nonneg (v := v)
            (by change R.length + 1 + 5 ≤ 1024; omega) hq
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
          have r9 := cometWithExtendedAssetList_block_2425
            (immWords := wordsOf (immStore v)) (by omega) hret r8
          refine Or.inl ⟨?_, k8 + 3, C8 + 12, ?_⟩
          · exact ⟨hmin, by simpa only [decide_eq_true hneg] using And.intro hm hq⟩
          · simpa only [principalValueWord, if_neg hpos, principalValueMagnitude,
              principalValueAmount, if_true] using r9
        · refine Or.inr ⟨?_, hr⟩
          intro hf; exact hq (by simpa only [decide_eq_true hneg] using hf.2.2)
      · refine Or.inr ⟨?_, hr⟩
        intro hf; exact hm (by simpa only [decide_eq_true hneg] using hf.2.1)
    · exact Or.inr ⟨fun hf ↦ hmin hf.1, hr⟩

end Benchmarks.CompoundIII.Comet

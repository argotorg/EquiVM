import Benchmarks.CompoundIII.Comet.SignedPresentValueModel
import Benchmarks.CompoundIII.Comet.PresentValueEvm
import Benchmarks.CompoundIII.Comet.Signed256
import Benchmarks.CompoundIII.Comet.Negate104Evm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_051
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: checked negation of a nonnegative signed 256-bit word cannot overflow.
theorem cometNegate256Nonneg {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {value ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hb : value.toNat < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10671⟩ (value :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.sub (UInt256.ofNat 0) value :: R) mem aw rdata σ k' C' := by
  have hne : value ≠ UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255) := by
    intro he
    rw [he] at hb
    contradiction
  have r1 := cometWithExtendedAssetList_block_10671_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (uInt256_eq_zero_of_ne (fun he ↦ hne (uInt256_eq_one_eq he))) h
  have r2 := cometWithExtendedAssetList_block_10683
    (immWords := wordsOf (immStore v)) (by omega) hret r1
  exact ⟨_, _, r2⟩

theorem cometSignedPresentValue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {principal ret : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10688⟩
      (UInt256.signextend (UInt256.ofNat 12) principal :: ret :: R) mem aw rdata σ k C) :
    (-(2^103 : Int) < signed104 principal ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (signedPresentValueWord evm principal :: R) mem aw rdata σ k' C') ∨
    (¬ -(2^103 : Int) < signed104 principal ∧ RDrev (deployedRuntime v) g s0) := by
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hw0 : solcSlotWordAt (UInt256.ofNat 0) σ ee = w0 := by
    simpa only [w0, hs.env] using (hs.storageRead ⟨0⟩).symm
  by_cases hpos : 0 ≤ signed104 principal
  · have hmin : -(2^103 : Int) < signed104 principal := by omega
    refine Or.inl ⟨hmin, ?_⟩
    rw [signedPresentValueWord, if_pos hpos]
    have r1 := cometWithExtendedAssetList_block_10688_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [signextend104_idem]; exact signed104_slt_nonneg hpos) h
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_10701
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hpclean : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
          (UInt256.ofNat 1)) (UInt256.signextend (UInt256.ofNat 12) principal) =
        positivePrincipal principal := by
      rw [show UInt256.signextend (UInt256.ofNat 12) principal = positivePrincipal principal
        from signextend104_nonneg hpos, u256_land_comm]
      exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl
        (lt_trans (positivePrincipal_lt _) (by decide))
    dsimp only [cometWithExtendedAssetList_block_10701_stack] at r2
    rw [hpclean] at r2
    change RD _ _ _ _ _ (positivePrincipal principal ::
      UInt256.land (solcSlotWordAt (UInt256.ofNat 0) σ ee)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) :: _) _ _ _ _ _ _ at r2
    have hiS : totalsIndexWord w0 false = UInt256.land w0
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) := totalsIndexWord_eq w0 false
    rw [hw0, ← hiS] at r2
    obtain ⟨k3, C3, r3⟩ := cometCheckedMul (v := v)
      (by simp only [List.length_cons]; omega)
      (lt_trans (presentValue_mul_lt (totalsIndexWord_lt w0 false)
        (lt_trans (positivePrincipal_lt principal) (by decide))) (by decide))
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_10746 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    obtain ⟨k5, C5, r5⟩ := cometSigned256 (v := v)
      (by change R.length + 1 + 5 ≤ 1024; omega)
      (lt_trans (signedPresentMagnitude_lt evm principal false hmin) (by decide))
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_2425 (immWords := wordsOf (immStore v))
      (by omega) hret r5
    exact ⟨_, _, r6⟩
  · have hn : signed104 principal < 0 := by omega
    have r1 := cometWithExtendedAssetList_block_10688_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [signextend104_idem]; exact signed104_slt_neg hn)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_10752
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    by_cases hmin : -(2^103 : Int) < signed104 principal
    · refine Or.inl ⟨hmin, ?_⟩
      rw [signedPresentValueWord, if_neg hpos]
      obtain ⟨k3, C3, r3⟩ := cometNegate104 (v := v)
        (by change R.length + 5 + 5 ≤ 1024; omega) (le_of_lt hn) hmin
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
      have r4 := cometWithExtendedAssetList_block_10785 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      dsimp only [cometWithExtendedAssetList_block_10785_stack] at r4
      have hclean : UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
            (UInt256.ofNat 1)) (negativePrincipal principal) = negativePrincipal principal := by
        rw [u256_land_comm]
        exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl
          (lt_trans (negativePrincipal_lt hmin) (by decide))
      rw [hclean] at r4
      change RD _ _ _ _ _ (UInt256.land
        (UInt256.shiftRight (solcSlotWordAt (UInt256.ofNat 0) σ ee) (UInt256.ofNat 64))
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) :: _) _ _ _ _ _ _ at r4
      have hiB : totalsIndexWord w0 true = UInt256.land
          (UInt256.shiftRight w0 (UInt256.ofNat 64))
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
            (UInt256.ofNat 1)) := totalsIndexWord_eq w0 true
      rw [hw0, ← hiB] at r4
      obtain ⟨k5, C5, r5⟩ := cometPresentValue (v := v)
        (by change R.length + 3 + 8 ≤ 1024; omega) (totalsIndexWord_lt w0 true)
        (lt_trans (negativePrincipal_lt hmin) (by decide))
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
      have r6 := cometWithExtendedAssetList_block_10598 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      obtain ⟨k7, C7, r7⟩ := cometSigned256 (v := v)
        (by change R.length + 2 + 5 ≤ 1024; omega)
        (lt_trans (signedPresentMagnitude_lt evm principal true hmin) (by decide))
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
      have r8 := cometWithExtendedAssetList_block_10800 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
      obtain ⟨k9, C9, r9⟩ := cometNegate256Nonneg (v := v)
        (by change R.length + 1 + 4 ≤ 1024; omega)
        (lt_trans (signedPresentMagnitude_lt evm principal true hmin) (by decide))
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
      have r10 := cometWithExtendedAssetList_block_2425 (immWords := wordsOf (immStore v))
        (by omega) hret r9
      exact ⟨_, _, r10⟩
    · refine Or.inr ⟨hmin, ?_⟩
      exact cometNegate104_revert (v := v) (by change R.length + 5 + 5 ≤ 1024; omega)
        (by have := signed104_bounds principal; omega) r2

end Benchmarks.CompoundIII.Comet

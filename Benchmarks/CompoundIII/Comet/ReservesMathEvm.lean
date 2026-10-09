import Benchmarks.CompoundIII.Comet.ReservesMath
import Benchmarks.CompoundIII.Comet.SignedArithmeticEvm
import Benchmarks.CompoundIII.Comet.ArithmeticRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometReservesPresentValues {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {w0 w1 time balance dummy : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hv : CurrentIndicesValid v w0 w1 time)
    (h : RD (deployedRuntime v) ee g s0 ⟨9965⟩
      (dummy :: w1 :: currentIndex v w0 w1 time false ::
        currentIndex v w0 w1 time true :: balance :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨10129⟩
      (balance :: ⟨10042⟩ :: ⟨10048⟩ :: totalReadWord v w0 w1 time false ::
        ⟨10042⟩ :: ⟨10054⟩ :: totalReadWord v w0 w1 time true :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_9965
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 16 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hsI := currentIndex_lt hv false
  have hbI := currentIndex_lt hv true
  have hsP := totalsPrincipalWord_lt w1 false
  have hbP := totalsPrincipalWord_lt w1 true
  have hsE : UInt256.land w1
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
        (UInt256.ofNat 1)) = totalsPrincipalWord w1 false := (totalsPrincipalWord_eq w1 false).symm
  have hbE : UInt256.land (UInt256.shiftRight w1 (UInt256.ofNat 104))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
        (UInt256.ofNat 1)) = totalsPrincipalWord w1 true := (totalsPrincipalWord_eq w1 true).symm
  have hclean (idx : UInt256) (hi : idx.toNat < 2^64) : UInt256.land idx
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = idx := u256LandMaskCleanOfToNat _ _ rfl hi
  simp only [cometWithExtendedAssetList_block_9965_stack, hsE, hclean _ hsI] at r1
  obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v)
    (by change R.length + 12 + 5 ≤ 1024; omega)
    (lt_trans (presentValue_mul_lt hsI hsP) (by decide))
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_10022
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [cometWithExtendedAssetList_block_10022_stack, hbE, hclean _ hbI] at r3
  obtain ⟨k4, C4, r4⟩ := cometCheckedMul (v := v)
    (by change R.length + 7 + 5 ≤ 1024; omega)
    (lt_trans (presentValue_mul_lt hbI hbP) (by decide))
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_10035
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  exact ⟨_, _, r5⟩

theorem cometReservesSigned {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw ret : UInt256}
    {σ : AccountMap} {k C : Nat} {w0 w1 time balance : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hv : CurrentIndicesValid v w0 w1 time)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10129⟩
      (balance :: ⟨10042⟩ :: ⟨10048⟩ :: totalReadWord v w0 w1 time false ::
        ⟨10042⟩ :: ⟨10054⟩ :: totalReadWord v w0 w1 time true :: ⟨2425⟩ :: ret :: R)
      mem aw rdata σ k C) :
    if ReservesMathValid v w0 w1 time balance then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (reservesWord v w0 w1 time balance :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hbal : balance.toNat < 2^255
  · obtain ⟨k1, C1, r1⟩ := cometSigned256 (v := v)
      (by change R.length + 7 + 5 ≤ 1024; omega) hbal
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_10042
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hs : (totalReadWord v w0 w1 time false).toNat < 2^255 :=
      lt_trans (totalReadWord_lt hv false) (by decide)
    have hb : (totalReadWord v w0 w1 time true).toNat < 2^255 :=
      lt_trans (totalReadWord_lt hv true) (by decide)
    obtain ⟨k3, C3, r3⟩ := cometSigned256 (v := v)
      (by change R.length + 6 + 5 ≤ 1024; omega) hs
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_10048
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    obtain ⟨k5, C5, r5⟩ := cometSignedSubNonneg (v := v)
      (by change R.length + 4 + 7 ≤ 1024; omega) hbal hs
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_10042
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    obtain ⟨k7, C7, r7⟩ := cometSigned256 (v := v)
      (by change R.length + 3 + 5 ≤ 1024; omega) hb
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
    have r8 := cometWithExtendedAssetList_block_10054
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
    have hr := cometSignedAddNonnegRight (v := v)
      (by change R.length + 1 + 8 ≤ 1024; omega) hb
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
    rw [signedWord_sub_low hbal hs] at hr
    change if reservesValue v w0 w1 time balance < (2^255 : Int) then
      ∃ k' C', RD _ _ _ _ ⟨2425⟩ (reservesWord v w0 w1 time balance :: ret :: R)
        mem aw rdata σ k' C' else _ at hr
    by_cases hi : reservesValue v w0 w1 time balance < (2^255 : Int)
    · rw [if_pos hi] at hr
      rw [if_pos (show ReservesMathValid v w0 w1 time balance from ⟨hbal, hi⟩)]
      obtain ⟨k9, C9, r9⟩ := hr
      exact ⟨_, _, cometWithExtendedAssetList_block_2425
        (immWords := wordsOf (immStore v)) (by omega) hret r9⟩
    · rw [if_neg hi] at hr
      rw [if_neg (show ¬ ReservesMathValid v w0 w1 time balance from fun h ↦ hi h.2)]
      exact hr
  · rw [if_neg (show ¬ ReservesMathValid v w0 w1 time balance from fun h ↦ hbal h.1)]
    exact cometSigned256_revert (v := v) (by change R.length + 7 + 5 ≤ 1024; omega) hbal h

end Benchmarks.CompoundIII.Comet

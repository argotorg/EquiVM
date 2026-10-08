import Benchmarks.CompoundIII.Comet.CurrentIndicesSource
import Benchmarks.CompoundIII.Comet.AccruedIndicesEvm
import Benchmarks.CompoundIII.Comet.AccrualTimeEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_013
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_024

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def totalTimeReturnPc (borrow : Bool) : UInt256 := if borrow then ⟨4270⟩ else ⟨1678⟩
def totalIndicesReturnPc (borrow : Bool) : UInt256 := if borrow then ⟨4299⟩ else ⟨1713⟩

theorem cometCurrentIndicesAfterLoad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024)
    (ht : (timestampWord ee).toNat < 2^40)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7753⟩
      (timestampWord ee :: lastAccrualWord (solcSlotWordAt ⟨1⟩ σ ee) ::
        ⟨1707⟩ :: ⟨1099511627775⟩ :: ret :: R) mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    if CurrentIndicesValid v w0 w1 (timestampWord ee) then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (currentIndex v w0 w1 (timestampWord ee) true ::
          currentIndex v w0 w1 (timestampWord ee) false :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  let w0 := solcSlotWordAt ⟨0⟩ σ ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let time := timestampWord ee
  change if CurrentIndicesValid v w0 w1 time then
    ∃ k' C', RD _ _ _ _ ret
      (currentIndex v w0 w1 time true :: currentIndex v w0 w1 time false :: R)
      mem aw rdata σ k' C' else _
  by_cases hle : (lastAccrualWord w1).toNat ≤ time.toNat
  · obtain ⟨k3, C3, r3⟩ := cometCheckedSub40 (v := v)
      (by simp only [List.length_cons]; omega) ht (lastAccrualWord_lt _) hle
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
    have hd := currentElapsed_lt ht hle
    have r4 := cometWithExtendedAssetList_block_1707
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    change RD _ _ _ _ _
      (UInt256.land (currentElapsed time w1) (UInt256.ofNat 1099511627775) ::
        ret :: R) _ _ _ _ _ _ at r4
    rw [u256LandMaskCleanOfToNat _ _ (bits := 40) rfl hd] at r4
    have ha := cometAccruedIndices (v := v) (elapsed := currentElapsed time w1)
      hstack hd hret r4
    dsimp only at ha
    change if AccruedIndicesValid v w0 w1 (currentElapsed time w1) then
      ∃ k' C', RD _ _ _ _ ret
        (currentIndex v w0 w1 time true :: currentIndex v w0 w1 time false :: R)
        mem aw rdata σ k' C' else _ at ha
    by_cases hv : AccruedIndicesValid v w0 w1 (currentElapsed time w1)
    · rw [if_pos hv] at ha
      rw [if_pos (show CurrentIndicesValid v w0 w1 time from ⟨ht, hle, hv⟩)]
      exact ha
    · rw [if_neg hv] at ha
      rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hv h.2.2)]
      exact ha
  · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hle h.2.1)]
    exact cometCheckedSub40_revert (v := v) (by simp only [List.length_cons]; omega)
      ht (lastAccrualWord_lt _) (Nat.lt_of_not_ge hle) h

theorem cometCurrentIndices {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256} (borrow : Bool)
    (hstack : R.length + 33 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨7614⟩ (totalTimeReturnPc borrow :: R)
      mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    if CurrentIndicesValid v w0 w1 (timestampWord ee) then
      ∃ k' C', RD (deployedRuntime v) ee g s0 (totalIndicesReturnPc borrow)
        (currentIndex v w0 w1 (timestampWord ee) true ::
          currentIndex v w0 w1 (timestampWord ee) false :: w1 :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  let w0 := solcSlotWordAt ⟨0⟩ σ ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let time := timestampWord ee
  change if CurrentIndicesValid v w0 w1 time then
    ∃ k' C', RD _ _ _ _ (totalIndicesReturnPc borrow)
      (currentIndex v w0 w1 time true :: currentIndex v w0 w1 time false :: w1 :: R)
      mem aw rdata σ k' C' else _
  by_cases ht : time.toNat < 2^40
  · obtain ⟨k1, C1, r1⟩ := cometNow (v := v) (by omega) ht
      (by cases borrow <;> rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest) h
    have hload : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7753⟩
        (time :: UInt256.land (UInt256.shiftRight w1 ⟨208⟩) ⟨1099511627775⟩ :: ⟨1707⟩ ::
          ⟨1099511627775⟩ :: totalIndicesReturnPc borrow :: w1 :: R) mem aw rdata σ k' C' := by
      cases borrow
      · exact cometWithExtendedAssetList_block_1678 (immWords := wordsOf (immStore v))
          (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      · exact cometWithExtendedAssetList_block_4270 (immWords := wordsOf (immStore v))
          (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨k2, C2, r2⟩ := hload
    rw [← lastAccrualWord_eq] at r2
    exact cometCurrentIndicesAfterLoad (v := v) (by simpa using hstack) ht
      (by cases borrow <;> rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest) r2
  · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ ht h.1)]
    exact cometNow_revert (v := v) (by simp only [List.length_cons]; omega) ht h

end Benchmarks.CompoundIII.Comet

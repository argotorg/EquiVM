import Benchmarks.CompoundIII.Comet.PauseWrites
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem boolShiftClean (b : Bool) (bit : Fin 5) :
    UInt256.land (UInt256.shiftLeft (UInt256.land (boolWord b) (UInt256.ofNat 255))
      (UInt256.land (UInt256.ofNat bit.val) (UInt256.ofNat 255))) (UInt256.ofNat 255) =
      UInt256.shiftLeft (boolWord b) (UInt256.ofNat bit.val) := by
  rcases bit with ⟨bit, hb⟩
  interval_cases bit <;> cases b <;> (dsimp only; decide)

theorem cometBoolShift {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256} (b : Bool) (bit : Fin 5)
    (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11118⟩
      (boolWord b :: UInt256.ofNat 3543 :: UInt256.ofNat bit.val :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.shiftLeft (boolWord b) (UInt256.ofNat bit.val) :: R) mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := cometToUInt8 (v := v) b
    (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
  have rd2 := cometWithExtendedAssetList_block_3543 (immWords := wordsOf (immStore v))
    hstack hret rd1
  unfold cometWithExtendedAssetList_block_3543_stack at rd2
  rw [boolShiftClean b bit] at rd2
  exact ⟨_, _, rd2⟩

def pauseTopic : UInt256 :=
  UInt256.ofNat 27088591580420894717312876173690122728946008261836708786452982051665301432589

theorem cometPauseFlags {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (a : PauseInputs)
    (hstack : R.length + 15 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨3489⟩
      (boolWord a.buy :: boolWord a.withdraw :: boolWord a.supply :: boolWord a.transfer ::
        boolWord a.absorb :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11083⟩
      (⟨1⟩ :: pauseFlagWord a :: ⟨3624⟩ :: boolWord a.withdraw :: boolWord a.absorb ::
        boolWord a.buy :: ⟨3677⟩ :: boolWord a.supply :: boolWord a.transfer :: pauseTopic :: R)
      mem aw rdata σ k' C' := by
  have rd1 := cometWithExtendedAssetList_block_3489 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨k2, C2, rd2⟩ := cometBoolShift (v := v) a.supply ⟨0, by decide⟩
    (by change R.length + 8 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd1
  have rd3 := cometWithExtendedAssetList_block_3557 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 13 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
  obtain ⟨k4, C4, rd4⟩ := cometBoolShift (v := v) a.transfer ⟨1, by decide⟩
    (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd3
  have rd5 := cometWithExtendedAssetList_block_3571 (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd4
  obtain ⟨k6, C6, rd6⟩ := cometBoolShift (v := v) a.withdraw ⟨2, by decide⟩
    (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd5
  have rd7 := cometWithExtendedAssetList_block_3586 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 9 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd6
  obtain ⟨k8, C8, rd8⟩ := cometBoolShift (v := v) a.absorb ⟨3, by decide⟩
    (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd7
  have rd9 := cometWithExtendedAssetList_block_3601 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd8
  obtain ⟨k10, C10, rd10⟩ := cometBoolShift (v := v) a.buy ⟨4, by decide⟩
    (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd9
  have rd11 := cometWithExtendedAssetList_block_3616 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd10
  have hz : UInt256.shiftLeft (boolWord a.supply) (UInt256.ofNat 0) = boolWord a.supply := by
    cases a.supply <;> rfl
  unfold cometWithExtendedAssetList_block_3616_stack at rd11
  rw [hz] at rd11
  exact ⟨_, _, rd11⟩

end Benchmarks.CompoundIII.Comet

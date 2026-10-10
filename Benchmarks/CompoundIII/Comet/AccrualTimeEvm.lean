import Benchmarks.CompoundIII.Comet.AccrualTime
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometNow {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024) (ht : (timestampWord ee).toNat < 2^40)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7614⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (timestampWord ee :: R)
      mem aw rdata σ k' C' := by
  have hg : UInt256.lt (timestampWord ee)
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 40)) = ⟨1⟩ := ult_one ht
  have r1 := cometWithExtendedAssetList_block_7614_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [show UInt256.ofNat ee.header.timestamp = timestampWord ee from rfl, hg]; decide) h
  have r2 := cometWithExtendedAssetList_block_7627
    (immWords := wordsOf (immStore v)) hstack hvalid r1
  simp only [cometWithExtendedAssetList_block_7627_stack] at r2
  change (UInt256.ofNat ee.header.timestamp).toNat < 2^40 at ht
  rw [u256LandMaskCleanOfToNat _ _ (bits := 40) rfl ht] at r2
  exact ⟨_, _, r2⟩

theorem cometNow_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024) (ht : ¬ (timestampWord ee).toNat < 2^40)
    (h : RD (deployedRuntime v) ee g s0 ⟨7614⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hg : UInt256.lt (timestampWord ee)
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 40)) = ⟨0⟩ :=
    ult_zero (Nat.le_of_not_gt ht)
  have r1 := cometWithExtendedAssetList_block_7614_taken
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [show UInt256.ofNat ee.header.timestamp = timestampWord ee from rfl, hg]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometWithExtendedAssetList_block_7637
    (immWords := wordsOf (immStore v)) hstack r1

theorem mask40Clean (x : UInt256) (hx : x.toNat < 2^40) :
    UInt256.land (UInt256.ofNat 1099511627775) x = x := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat x _ rfl hx

theorem sub40_lt {x y : UInt256} (hx : x.toNat < 2^40) (hle : y.toNat ≤ x.toNat) :
    (UInt256.sub x y).toNat < 2^40 := by rw [usub_toNat hle]; omega

theorem cometCheckedSub40 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hx : x.toNat < 2^40) (hy : y.toNat < 2^40)
    (hle : y.toNat ≤ x.toNat) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7753⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub x y :: R)
      mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7753_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [mask40Clean x hx, mask40Clean y hy]; exact ult_zero hle) h
  simp only [cometWithExtendedAssetList_block_7753_fallthrough_stack,
    mask40Clean x hx, mask40Clean y hy] at r1
  have r2 := cometWithExtendedAssetList_block_7772
    (immWords := wordsOf (immStore v)) (by omega) hvalid r1
  exact ⟨_, _, r2⟩

theorem cometCheckedSub40_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hx : x.toNat < 2^40) (hy : y.toNat < 2^40)
    (hlt : x.toNat < y.toNat)
    (h : RD (deployedRuntime v) ee g s0 ⟨7753⟩ (x :: y :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_7753_taken
    (immWords := wordsOf (immStore v)) hstack
    (by rw [mask40Clean x hx, mask40Clean y hy, ult_one hlt]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7775
    (immWords := wordsOf (immStore v)) (by simpa [cometWithExtendedAssetList_block_7753_taken_stack] using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7730
    (immWords := wordsOf (immStore v)) (by simpa [cometWithExtendedAssetList_block_7753_taken_stack] using hstack) r2

end Benchmarks.CompoundIII.Comet

import Benchmarks.CompoundIII.Comet.IsInAssetEvm
import Benchmarks.CompoundIII.Comet.CollateralLoopWords
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_077
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_079

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbLoopStack (i : Nat) (assets reserved old principal price account delta ptr absorber : UInt256)
    (R : List UInt256) : List UInt256 :=
  UInt256.ofNat i :: reserved :: assets :: old :: principal :: price :: account :: delta ::
    ptr :: absorber :: R

theorem cometAbsorbMembership {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets reserved : UInt256} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hi : i < v.numAssets.toNat)
    (ha : assets.toNat < 2^16) (hr : reserved.toNat < 2^8)
    (h : RD (deployedRuntime v) ee g s0 ⟨17110⟩
      (UInt256.ofNat i :: reserved :: assets :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨17562⟩
      (boolWord (isInAssetBool assets (UInt256.ofNat i) reserved) ::
        UInt256.ofNat i :: reserved :: assets :: R) mem aw rdata σ k' C' := by
  have hi8 : i < 256 := lt_trans hi v.numAssets_lt
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  have hmask : UInt256.land (UInt256.ofNat i) (UInt256.ofNat 255) = UInt256.ofNat i :=
    lowByteClean (by rw [hin]; exact hi8)
  have hnum : UInt256.land (wordsOf (immStore v) "numAssets") (UInt256.ofNat 255) = v.numAssets := by
    rw [wordsOf_immStore_numAssets, wordOfInt_ofNat_toNat]
    exact lowByteClean v.numAssets_lt
  have r1 := cometWithExtendedAssetList_block_17110_taken (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [hmask, hnum, ult_one (by rw [hin]; exact hi)]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_17551 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometIsInAsset (v := v) (by change R.length + 3 + 7 ≤ 1024; omega)
    ha (by rw [hin]; exact hi8) hr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2

theorem cometAbsorbMemberBranch {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (member : Bool) (hstack : R.length + 2 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨17562⟩ (boolWord member :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (if member then ⟨17578⟩ else ⟨17567⟩)
      R mem aw rdata σ k' C' := by
  cases member
  · exact ⟨_, _, cometWithExtendedAssetList_block_17562_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by decide) h⟩
  · exact ⟨_, _, cometWithExtendedAssetList_block_17562_taken
      (immWords := wordsOf (immStore v)) hstack (by decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h⟩

theorem cometAbsorbIncrement {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024) (hi : i + 1 < 256)
    (h : RD (deployedRuntime v) ee g s0 ⟨17567⟩ (UInt256.ofNat i :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨17110⟩
      (UInt256.ofNat (i + 1) :: R) mem aw rdata σ k' C' := by
  have hr := cometWithExtendedAssetList_block_17567 (immWords := wordsOf (immStore v))
    hstack (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_17567_stack] at hr
  simp only [show UInt256.ofNat 255 = (⟨255⟩ : UInt256) from rfl,
    uint8IncrementWord i hi] at hr
  exact ⟨_, _, hr⟩

theorem cometAbsorbLoopExit {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hi : v.numAssets.toNat ≤ i) (hi8 : i < 256)
    (h : RD (deployedRuntime v) ee g s0 ⟨17110⟩ (UInt256.ofNat i :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨17156⟩
      (UInt256.ofNat i :: R) mem aw rdata σ k' C' := by
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  have hmask : UInt256.land (UInt256.ofNat i) (UInt256.ofNat 255) = UInt256.ofNat i :=
    lowByteClean (by rw [hin]; exact hi8)
  have hnum : UInt256.land (wordsOf (immStore v) "numAssets") (UInt256.ofNat 255) = v.numAssets := by
    rw [wordsOf_immStore_numAssets, wordOfInt_ofNat_toNat]
    exact lowByteClean v.numAssets_lt
  exact ⟨_, _, cometWithExtendedAssetList_block_17110_fallthrough
    (immWords := wordsOf (immStore v)) hstack
    (by rw [hmask, hnum]; exact ult_zero (by rw [hin]; exact hi)) h⟩

end Benchmarks.CompoundIII.Comet

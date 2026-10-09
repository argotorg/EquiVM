import Benchmarks.CompoundIII.Comet.CollateralLoopWords
import Benchmarks.CompoundIII.Comet.IsInAssetEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_049
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def collateralLoopPc (borrow : Bool) : UInt256 := if borrow then ⟨10391⟩ else ⟨10912⟩
def collateralMemberPc (borrow : Bool) : UInt256 := if borrow then ⟨10422⟩ else ⟨10942⟩
def collateralIncrementPc (borrow : Bool) : UInt256 := if borrow then ⟨10427⟩ else ⟨10947⟩
def collateralSelectedPc (borrow : Bool) : UInt256 := if borrow then ⟨10437⟩ else ⟨10957⟩

def collateralLoopStack (i : Nat) (assets reserved account total liquidity ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  UInt256.ofNat i :: assets :: reserved :: account :: total :: ⟨255⟩ ::
    liquidity :: ⟨0⟩ :: ret :: R

theorem cometCollateralMembership {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets reserved account total liquidity ret : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 17 ≤ 1024)
    (hi : i < total.toNat) (hi8 : i < 256)
    (ha : assets.toNat < 2^16) (hr : reserved.toNat < 2^8)
    (h : RD (deployedRuntime v) ee g s0 (collateralLoopPc borrow)
      (collateralLoopStack i assets reserved account total liquidity ret R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (collateralMemberPc borrow)
      (boolWord (isInAssetBool assets (UInt256.ofNat i) reserved) ::
        collateralLoopStack i assets reserved account total liquidity ret R)
      mem aw rdata σ k' C' := by
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  have hmask : UInt256.land (UInt256.ofNat i) ⟨255⟩ = UInt256.ofNat i :=
    lowByteClean (by rw [hin]; exact hi8)
  have hstep : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11456⟩
      (assets :: UInt256.ofNat i :: reserved :: collateralMemberPc borrow ::
        collateralLoopStack i assets reserved account total liquidity ret R)
      mem aw rdata σ k' C' := by
    cases borrow with
    | false =>
        have r1 := cometWithExtendedAssetList_block_10912_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 9 ≤ 1024; omega)
          (by rw [hmask, ult_one (by rw [hin]; exact hi)]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
        have r2 := cometWithExtendedAssetList_block_10931 (immWords := wordsOf (immStore v))
          (by change R.length + 6 + 8 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
        exact ⟨_, _, r2⟩
    | true =>
        have r1 := cometWithExtendedAssetList_block_10391_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 9 ≤ 1024; omega)
          (by rw [hmask, ult_one (by rw [hin]; exact hi)]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
        have r2 := cometWithExtendedAssetList_block_10411 (immWords := wordsOf (immStore v))
          (by change R.length + 6 + 8 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
        exact ⟨_, _, r2⟩
  obtain ⟨k1, C1, r1⟩ := hstep
  exact cometIsInAsset (v := v) (by change R.length + 9 + 7 ≤ 1024; omega)
    ha (by rw [hin]; exact hi8) hr
    (by cases borrow <;> rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest) r1

theorem cometCollateralIncrement {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets reserved account total liquidity ret : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 10 ≤ 1024) (hi : i + 1 < 256)
    (h : RD (deployedRuntime v) ee g s0 (collateralIncrementPc borrow)
      (collateralLoopStack i assets reserved account total liquidity ret R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (collateralLoopPc borrow)
      (collateralLoopStack (i + 1) assets reserved account total liquidity ret R)
      mem aw rdata σ k' C' := by
  cases borrow with
  | false =>
      have r1 := cometWithExtendedAssetList_block_10947 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 7 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [cometWithExtendedAssetList_block_10947_stack] at r1
      rw [uint8IncrementWord i hi] at r1
      exact ⟨_, _, r1⟩
  | true =>
      have r1 := cometWithExtendedAssetList_block_10427 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 7 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [cometWithExtendedAssetList_block_10427_stack] at r1
      rw [uint8IncrementWord i hi] at r1
      exact ⟨_, _, r1⟩

theorem cometCollateralMemberBranch {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow member : Bool) (hstack : R.length + 2 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (collateralMemberPc borrow)
      (boolWord member :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0
      (if member then collateralSelectedPc borrow else collateralIncrementPc borrow)
      R mem aw rdata σ k' C' := by
  cases borrow <;> cases member
  · exact ⟨_, _, cometWithExtendedAssetList_block_10942_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by decide) h⟩
  · exact ⟨_, _, cometWithExtendedAssetList_block_10942_taken
      (immWords := wordsOf (immStore v)) hstack (by decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h⟩
  · exact ⟨_, _, cometWithExtendedAssetList_block_10422_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by decide) h⟩
  · exact ⟨_, _, cometWithExtendedAssetList_block_10422_taken
      (immWords := wordsOf (immStore v)) hstack (by decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h⟩

theorem cometCollateralExhausted {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets reserved account total liquidity ret : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 12 ≤ 1024)
    (hi : total.toNat ≤ i) (hi8 : i < 256)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (collateralLoopPc borrow)
      (collateralLoopStack i assets reserved account total liquidity ret R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (boolWord (collateralResultBool borrow liquidity) :: R) mem aw rdata σ k' C' := by
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  have hmask : UInt256.land (UInt256.ofNat i) ⟨255⟩ = UInt256.ofNat i :=
    lowByteClean (by rw [hin]; exact hi8)
  cases borrow with
  | false =>
      have r1 := cometWithExtendedAssetList_block_10912_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 9 ≤ 1024; omega)
        (by rw [hmask]; exact ult_zero (by rw [hin]; exact hi)) h
      have r2 := cometWithExtendedAssetList_block_10922 (immWords := wordsOf (immStore v))
        (by omega) hret r1
      dsimp only [cometWithExtendedAssetList_block_10922_stack] at r2
      rw [signedSltZeroWord] at r2
      exact ⟨_, _, r2⟩
  | true =>
      have r1 := cometWithExtendedAssetList_block_10391_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 9 ≤ 1024; omega)
        (by rw [hmask]; exact ult_zero (by rw [hin]; exact hi)) h
      have r2 := cometWithExtendedAssetList_block_10401 (immWords := wordsOf (immStore v))
        (by omega) hret r1
      dsimp only [cometWithExtendedAssetList_block_10401_stack] at r2
      rw [signedNonnegWord] at r2
      exact ⟨_, _, r2⟩

end Benchmarks.CompoundIII.Comet

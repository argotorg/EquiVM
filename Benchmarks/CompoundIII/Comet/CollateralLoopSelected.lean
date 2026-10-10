import Benchmarks.CompoundIII.Comet.CollateralLoopControl
import Benchmarks.CompoundIII.Comet.CollateralValueEvm
import Benchmarks.CompoundIII.Comet.SignedArithmeticEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_050
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def collateralSumPc (borrow : Bool) : UInt256 := if borrow then ⟨10603⟩ else ⟨11059⟩

def collateralValueRest (i : Nat) (assets reserved account total ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  ⟨255⟩ :: assets :: reserved :: account :: total :: ⟨255⟩ :: UInt256.ofNat i :: ⟨0⟩ :: ret :: R

theorem cometCollateralSolvent {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets reserved account total liquidity ret : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 11 ≤ 1024) (hl : 0 ≤ signedWord liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (collateralSelectedPc borrow)
      (collateralLoopStack i assets reserved account total liquidity ret R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (boolWord borrow :: R)
      mem aw rdata σ k' C' := by
  have hcond : UInt256.isZero (UInt256.slt liquidity ⟨0⟩) ≠ UInt256.ofNat 0 := by
    rw [signedNonnegWord, decide_eq_true hl]
    decide
  cases borrow with
  | false =>
      have r1 := cometWithExtendedAssetList_block_10957_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega) hcond
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact ⟨_, _, cometWithExtendedAssetList_block_11068
        (immWords := wordsOf (immStore v)) (by omega) hret r1⟩
  | true =>
      have r1 := cometWithExtendedAssetList_block_10437_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega) hcond
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact ⟨_, _, cometWithExtendedAssetList_block_10612
        (immWords := wordsOf (immStore v)) (by omega) hret r1⟩

theorem cometCollateralValueStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets reserved account total liquidity ret : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 25 ≤ 1024) (hl : signedWord liquidity < 0)
    (h : RD (deployedRuntime v) ee g s0 (collateralSelectedPc borrow)
      (collateralLoopStack i assets reserved account total liquidity ret R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7179⟩
      (UInt256.ofNat i :: ⟨10490⟩ :: ⟨10498⟩ :: ⟨10518⟩ :: collateralPricePc borrow ::
        ⟨10579⟩ :: UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ ::
        account :: ⟨10598⟩ :: ⟨10054⟩ :: liquidity :: collateralSumPc borrow :: ⟨1⟩ ::
        collateralValueRest i assets reserved account total ret R)
      mem aw rdata σ k' C' := by
  have hcond : UInt256.isZero (UInt256.slt liquidity ⟨0⟩) = UInt256.ofNat 0 := by
    rw [signedNonnegWord, decide_eq_false (by omega)]
    rfl
  cases borrow with
  | false =>
      have r1 := cometWithExtendedAssetList_block_10957_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega) hcond h
      exact ⟨_, _, cometWithExtendedAssetList_block_10967
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 23 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1⟩
  | true =>
      have r1 := cometWithExtendedAssetList_block_10437_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega) hcond h
      exact ⟨_, _, cometWithExtendedAssetList_block_10447
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 23 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1⟩

theorem cometCollateralSum {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets reserved account total liquidity value ret : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 18 ≤ 1024) (hi : i + 1 < 256)
    (hl : signedWord liquidity < 0) (hv : value.toNat < 2^255)
    (h : RD (deployedRuntime v) ee g s0 ⟨10054⟩
      (value :: liquidity :: collateralSumPc borrow :: ⟨1⟩ ::
        collateralValueRest i assets reserved account total ret R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (collateralLoopPc borrow)
      (collateralLoopStack (i + 1) assets reserved account total (liquidity + value) ret R)
      mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_10054 (immWords := wordsOf (immStore v))
    (by change R.length + 11 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometSignedAddNonnegRight (v := v)
    (by change R.length + 10 + 8 ≤ 1024; omega) hv
    (by cases borrow <;> rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest) r1
  rw [if_pos (collateralSum_bounds hl hv).2] at hr
  obtain ⟨k2, C2, r2⟩ := hr
  have hstep : ∃ k' C', RD (deployedRuntime v) ee g s0 (collateralIncrementPc borrow)
      (collateralLoopStack i assets reserved account total (liquidity + value) ret R)
      mem aw rdata σ k' C' := by
    cases borrow with
    | false =>
        exact ⟨_, _, cometWithExtendedAssetList_block_11059
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 9 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2⟩
    | true =>
        exact ⟨_, _, cometWithExtendedAssetList_block_10603
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 9 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2⟩
  obtain ⟨k3, C3, r3⟩ := hstep
  exact cometCollateralIncrement borrow (by omega) hi r3

end Benchmarks.CompoundIII.Comet

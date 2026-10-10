import Benchmarks.CompoundIII.Comet.ArithmeticRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

-- GENERALIZES Reasoning.SolmBody.uint256RangeSourceOk to every unsigned width.
theorem uintRangeSourceOk {cfg solm evm expr} {n : Nat} (width : BitWidth)
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hn : n < 2^width.val) :
    evalExpr? cfg solm evm (.inRange (.uint width) expr) = .ok (.int (Int.ofNat n)) := by
  have hi0 : ¬ Int.ofNat n < 0 := by simp only [Int.ofNat_eq_natCast]; omega
  have hi : ¬ Int.ofNat n ≥ (2 : Int)^width.val := by
    have hp : ((2^width.val : Nat) : Int) = (2 : Int)^width.val := by simp
    rw [← hp]
    simp only [Int.ofNat_eq_natCast]
    exact_mod_cast Nat.not_le.mpr hn
  simp only [evalExpr?, he, bind, EvalResult.bind, hi0, hi, decide_false, Bool.or_self,
    Bool.false_eq_true, if_false, pure]

-- GENERALIZES Reasoning.SolmBody.uint256RangeSourceOverflow to every unsigned width.
theorem uintRangeSourceOverflow {cfg solm evm expr} {n : Nat} (width : BitWidth)
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hn : 2^width.val ≤ n) :
    evalExpr? cfg solm evm (.inRange (.uint width) expr) = .revert := by
  have hi : Int.ofNat n ≥ (2 : Int)^width.val := by
    simp only [Int.ofNat_eq_natCast]
    exact_mod_cast hn
  simp only [evalExpr?, he, bind, EvalResult.bind, hi, decide_true, Bool.or_true, if_true]

-- LIBRARY CANDIDATE: checked addition at a narrow unsigned width, with a word result.
theorem checkedNarrowAddSourceOk {cfg solm evm lhs rhs} {a b : UInt256}
    (width : BitWidth) (hw : width.val ≤ 256)
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hfit : a.toNat + b.toNat < 2^width.val) :
    evalExpr? cfg solm evm (.inRange (.uint width) (.binary .add lhs rhs)) =
      .ok (.int (Int.ofNat (a + b).toNat)) := by
  have hsize : a.toNat + b.toNat < UInt256.size :=
    lt_of_lt_of_le hfit (Nat.pow_le_pow_right (by decide) hw)
  have hn : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b hsize
  rw [hn]
  exact uintRangeSourceOk width (naturalAddSource ha hb) hfit

theorem mask64Clean (x : UInt256) (hx : x.toNat < 2^64) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1)) x = x := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat x _ rfl hx

-- LIBRARY CANDIDATE: checked subtraction at an unsigned width.
theorem checkedNarrowSubSourceOk {cfg solm evm lhs rhs} {a b : UInt256}
    (width : BitWidth)
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hfit : a.toNat < 2^width.val) (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg solm evm (.inRange (.uint width) (.binary .sub lhs rhs)) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  apply uintRangeSourceOk width (subSourceOk ha hb hle)
  rw [usub_toNat hle]
  omega

theorem checkedNarrowSubSourceUnderflow {cfg solm evm lhs rhs} {a b : UInt256}
    (width : BitWidth)
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg solm evm (.inRange (.uint width) (.binary .sub lhs rhs)) = .revert := by
  have hneg : Int.ofNat a.toNat - Int.ofNat b.toNat < 0 := by
    simp only [Int.ofNat_eq_natCast]
    exact sub_neg.mpr (by exact_mod_cast hlt)
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, hneg,
    decide_true, Bool.true_or, if_true]

theorem cometCheckedAdd64 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hx : x.toNat < 2^64) (hy : y.toNat < 2^64)
    (hfit : x.toNat + y.toNat < 2^64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7830⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((x + y) :: R) mem aw rdata σ k' C' := by
  have hg : UInt256.gt x (UInt256.sub
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) y) = ⟨0⟩ := by
    apply ugt_zero
    rw [usub_toNat]
    · change x.toNat ≤ 2^64 - 1 - y.toNat
      omega
    · change y.toNat ≤ 2^64 - 1
      omega
  have r1 := cometWithExtendedAssetList_block_7830_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [mask64Clean x hx, mask64Clean y hy]; exact hg) h
  simp only [cometWithExtendedAssetList_block_7830_fallthrough_stack,
    mask64Clean x hx, mask64Clean y hy] at r1
  have r2 := cometWithExtendedAssetList_block_7856
    (immWords := wordsOf (immStore v)) (by omega) hvalid r1
  exact ⟨_, _, r2⟩

theorem cometCheckedAdd64_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hx : x.toNat < 2^64) (hy : y.toNat < 2^64)
    (hover : 2^64 ≤ x.toNat + y.toNat)
    (h : RD (deployedRuntime v) ee g s0 ⟨7830⟩ (x :: y :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hg : UInt256.gt x (UInt256.sub
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) y) ≠ ⟨0⟩ := by
    rw [ugt_one (by
      rw [usub_toNat]
      · change 2^64 - 1 - y.toNat < x.toNat
        omega
      · change y.toNat ≤ 2^64 - 1
        omega)]
    decide
  have r1 := cometWithExtendedAssetList_block_7830_taken
    (immWords := wordsOf (immStore v)) hstack
    (by rw [mask64Clean x hx, mask64Clean y hy]; exact hg)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7859
    (immWords := wordsOf (immStore v)) (by change R.length + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7730
    (immWords := wordsOf (immStore v)) (by change R.length + 4 ≤ 1024; omega) r2

end Benchmarks.CompoundIII.Comet

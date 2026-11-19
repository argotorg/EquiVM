import Benchmarks.Midnight.LiquidateLif

/-! Select the recovery-threshold check for a pre-maturity liquidation below full LLTV. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def LiquidateRcfEnabled (mode lltv : UInt256) : Prop :=
  mode = ⟨0⟩ ∧ lltv.toNat < lifScale.toNat

def liquidateRcfExpr : Expr :=
  .binary .and (.unary .not (.var "postMaturityMode"))
    (.binary .lt (.var "lltv") (.intLit 1000000000000000000))

theorem evalLiquidateRcfGuard {frame : Frame} {evm : State} {mode lltv : UInt256}
    (hm : frame.locals.get? "postMaturityMode" = some (wordToElem .bool mode))
    (hl : frame.locals.get? "lltv" = some (.int lltv.toNat)) :
    evalExpr? config frame evm liquidateRcfExpr =
      .ok (.bool (decide (mode = ⟨0⟩ ∧ lltv.toNat < lifScale.toNat))) := by
  by_cases hz : mode = ⟨0⟩ <;>
    simp only [liquidateRcfExpr, evalExpr?, hm, hl, wordToElemBool, hz, decide_true,
      decide_false, Bool.not_true, Bool.not_false, EvalResult.ofOption, bind, pure,
      EvalResult.bind, evalUnaryOp?, evalBinaryOp?, true_and, false_and, Int.ofNat_eq_natCast,
      show lifScale.toNat = 1000000000000000000 from rfl, Int.ofNat_lt]
  norm_num

theorem midnightLiquidateRcfGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw maxDebt lltv lif price pos dp dl borrower badDebt receiver mode : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 14 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨6731⟩
      ([maxDebt, lltv, lif, price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R)
      mem aw rdata σ k C) :
    (LiquidateRcfEnabled mode lltv ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨7014⟩
        ([maxDebt, lltv, lif, price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R)
        mem aw rdata σ k' C') ∨
    (¬ LiquidateRcfEnabled mode lltv ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨6744⟩
        ([maxDebt, lltv, lif, price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R)
        mem aw rdata σ k' C') := by
  by_cases hz : mode = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_6731_taken (R := R) hstack
      (by rw [hz]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_6731_taken_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_7322
      (R := [lif, price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_7322_stack] at rd2
    by_cases hl : lltv.toNat < lifScale.toNat
    · have hg : UInt256.lt lltv (UInt256.ofNat 1000000000000000000) ≠ ⟨0⟩ := by
        change UInt256.lt lltv lifScale ≠ ⟨0⟩
        rw [ult_one hl]; decide
      have rd3 := midnightBlocks.midnight_block_6739_taken
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        hg (by jump_dest) rd2
      exact Or.inl ⟨⟨hz, hl⟩, _, _, by omega, rd3⟩
    · have rd3 := midnightBlocks.midnight_block_6739_fallthrough
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (ult_zero (Nat.le_of_not_gt hl)) rd2
      exact Or.inr ⟨fun h ↦ hl h.2, _, _, by omega, rd3⟩
  · have rd1 := midnightBlocks.midnight_block_6731_fallthrough (R := R) hstack
      (isZero_eq_zero_of_ne hz) rd
    simp only [midnightBlocks.midnight_block_6731_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_6739_fallthrough
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (isZero_eq_zero_of_ne hz) rd1
    exact Or.inr ⟨fun h ↦ hz h.1, _, _, by omega, rd2⟩

end Benchmarks.Midnight

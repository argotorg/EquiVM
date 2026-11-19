import Benchmarks.Midnight.LiquidateBadDebt

/-! The short-circuit test for a nonzero repayment or collateral seizure. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateAmountsBody : List Stmt :=
  match liquidateTransition.body[18]! with
  | .ite _ body _ => body
  | _ => []

theorem evalLiquidateAmountsGuard {frame : Frame} {evm : State} {seized repaid : UInt256}
    (hs : frame.locals.get? "seizedAssets" = some (.int seized.toNat))
    (hr : frame.locals.get? "repaidUnits" = some (.int repaid.toNat)) :
    evalExpr? config frame evm (.binary .or
      (.binary .gt (.var "repaidUnits") (.intLit 0))
      (.binary .gt (.var "seizedAssets") (.intLit 0))) =
      .ok (.bool (decide (0 < repaid.toNat ∨ 0 < seized.toNat))) := by
  simp only [evalExpr?, hr, hs, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?]
  norm_num
  split <;> simp_all

theorem midnightLiquidateAmountsGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head seized repaid : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (hs : calldataWord I.calldata 68 = seized)
    (rd : RD midnightBytecode I g s0 ⟨5468⟩
      (head :: UInt256.isZero (UInt256.isZero repaid) :: UInt256.isZero repaid :: R)
      mem aw rdata σ k C) :
    (seized = ⟨0⟩ ∧ repaid = ⟨0⟩ ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨5480⟩ R mem aw rdata σ k' C') ∨
    ((repaid ≠ ⟨0⟩ ∨ seized ≠ ⟨0⟩) ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨6477⟩ R mem aw rdata σ k' C') := by
  by_cases hr : repaid = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_5468_taken hstack
      (by rw [hr]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_5468_taken_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_7420 (R := R) (by omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_7420_stack] at rd2
    change RD midnightBytecode I g s0 ⟨5475⟩
      (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 68)) :: R)
      mem aw rdata σ _ _ at rd2
    rw [hs] at rd2
    by_cases hz : seized = ⟨0⟩
    · have rd3 := midnightBlocks.midnight_block_5475_fallthrough (R := R) (by omega)
        (by rw [hz]; rfl) rd2
      exact Or.inl ⟨hz, hr, _, _, by omega, rd3⟩
    · have rd3 := midnightBlocks.midnight_block_5475_taken (R := R) (by omega)
        (by rw [isZero_eq_zero_of_ne hz]; decide) (by jump_dest) rd2
      exact Or.inr ⟨Or.inr hz, _, _, by omega, rd3⟩
  · have rd1 := midnightBlocks.midnight_block_5468_fallthrough hstack
      (isZero_eq_zero_of_ne hr) rd
    simp only [midnightBlocks.midnight_block_5468_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_5475_taken (R := R) (by omega)
      (by rw [isZero_eq_zero_of_ne hr]; decide) (by jump_dest) rd1
    exact Or.inr ⟨Or.inl hr, _, _, by omega, rd2⟩

end Benchmarks.Midnight

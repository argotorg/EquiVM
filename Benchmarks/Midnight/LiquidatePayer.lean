import Benchmarks.Midnight.LiquidateAmountsGuard
import Benchmarks.Midnight.RepayPayerSource
import Benchmarks.Midnight.TransferBudget

/-! The payer is the callback when present and the caller otherwise. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidatePayerSource {frame : Frame} {evm : State} {callback : AccountAddress}
    (hc : frame.locals.get? "callback" = some (.address callback)) :
    ExecStmt config frame evm (liquidateTransition.body[19]!)
      (.ok (repayPayerFrame frame evm.executionEnv callback) evm) := by
  apply ExecStmt.letDecl
  rw [evalExpr?]
  change (evalExpr? config frame evm repayCallbackCondition >>= _) = _
  rw [repayCallbackCondition_eval hc]
  by_cases hz : callback = 0
  · simp [hz, EvalResult.bind, bind, evalExpr?, envValue, repayPayer, pure]
  · simp only [decide_eq_true hz, hz, EvalResult.bind, bind, evalExpr?, hc,
      EvalResult.ofOption, repayPayer, if_false]

theorem midnightLiquidatePayer {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw d0 d1 d2 dp dl borrower badDebt receiver mode root : UInt256}
    {callback : AccountAddress} {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcb : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5480⟩
      ([d0, d1, d2, dp, dl, borrower, badDebt, receiver, mode] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨5508⟩
        ([mode, dp, dl, borrower, badDebt, receiver, UInt256.ofNat (repayPayer I callback).val] ++ R)
        mem aw' rdata σ k' C' := by
  have hc : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (memLoad (UInt256.ofNat 736) mem) = UInt256.ofNat callback.val := by
    rw [addressMask_computed, hcb, u256_land_comm, solcAddrMask_clean (addressWord_canonical callback)]
  by_cases hz : callback = 0
  · have rd1 := midnightBlocks.midnight_block_5480_taken
      (R := [dp, dl, borrower, badDebt, receiver, mode] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hc, hz]; decide) (by jump_dest) rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
    have rd2 := midnightBlocks.midnight_block_6470 (R := R) (by omega) (by jump_dest) rd1
    have hb2 := transferBudgetAt (root := root) (credit := credit) rd2 (hb1.mono (by omega))
    exact ⟨_, _, _, hb2, by
      simpa only [midnightBlocks.midnight_block_6470_stack, repayPayer, hz, if_true] using rd2⟩
  · have hword : UInt256.ofNat callback.val ≠ ⟨0⟩ := by
      intro h
      apply hz
      apply Fin.ext
      have hn := congrArg UInt256.toNat h
      change callback.val = 0
      simpa only [show (UInt256.ofNat callback.val).toNat = callback.val from
        addressWord_toNat_val callback] using hn
    have rd1 := midnightBlocks.midnight_block_5480_fallthrough
      (R := [dp, dl, borrower, badDebt, receiver, mode] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hc]; exact isZero_eq_zero_of_ne hword) rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
    have rd2 := midnightBlocks.midnight_block_5503 (R := R) (by omega) rd1
    have hb2 := transferBudgetAt (root := root) (credit := credit) rd2 (by transfer_budget hb1)
    exact ⟨_, _, _, hb2, by
      simpa only [midnightBlocks.midnight_block_5503_stack, hcb, repayPayer, hz, if_false] using rd2⟩

end Benchmarks.Midnight

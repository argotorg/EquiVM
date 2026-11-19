import Benchmarks.Midnight.PositionViewSourceBase

/-! The source tuple return and its checked-subtraction failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def positionViewReturnValues (postCredit postPending fee : UInt256) : List Value :=
  [.int (UInt256.sub (low128 postCredit) fee).toNat,
   .int (UInt256.sub (low128 postPending) fee).toNat, .int fee.toNat]

theorem positionViewReturnSource {frame : Frame} {evm : EVM.State}
    {postCredit postPending fee : UInt256}
    (hc : frame.locals.get? "postSlashCredit" = some (.int postCredit.toNat))
    (hp : frame.locals.get? "postSlashPendingFee" = some (.int postPending.toNat))
    (hf : frame.locals.get? "fee" = some (.int fee.toNat))
    (hcredit : fee.toNat ≤ (low128 postCredit).toNat)
    (hpending : fee.toNat ≤ (low128 postPending).toNat) :
    ExecBlock config frame evm (positionViewFunction.body.drop 12)
      (.returned frame evm (some (positionViewReturnValues postCredit postPending fee))) := by
  have hcs := evalCheckedSub128 (evalCast128 (evalWordLocal (cfg := config) (evm := evm) hc))
    (evalWordLocal hf) (low128_lt _) hcredit
  have hps := evalCheckedSub128 (evalCast128 (evalWordLocal (cfg := config) (evm := evm) hp))
    (evalWordLocal hf) (low128_lt _) hpending
  apply ExecBlock.consReturn
  apply ExecStmt.return
  change evalExprs? config frame evm
    [.inRange packedUInt128Int (.binary .sub (.cast (.var "postSlashCredit") (.elem (.int packedUInt128Int))) (.var "fee")),
     .inRange packedUInt128Int (.binary .sub (.cast (.var "postSlashPendingFee") (.elem (.int packedUInt128Int))) (.var "fee")),
     .var "fee"] = _
  simp only [evalExprs?, hcs, hps, evalWordLocal hf, bind, pure, EvalResult.bind,
    positionViewReturnValues]

theorem positionViewReturnSourceRevert {frame : Frame} {evm : EVM.State}
    {postCredit postPending fee : UInt256}
    (hc : frame.locals.get? "postSlashCredit" = some (.int postCredit.toNat))
    (hp : frame.locals.get? "postSlashPendingFee" = some (.int postPending.toNat))
    (hf : frame.locals.get? "fee" = some (.int fee.toNat))
    (hbad : ¬ (fee.toNat ≤ (low128 postCredit).toNat ∧ fee.toNat ≤ (low128 postPending).toNat)) :
    ExecBlock config frame evm (positionViewFunction.body.drop 12) .reverted := by
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  change evalExprs? config frame evm
    [.inRange packedUInt128Int (.binary .sub (.cast (.var "postSlashCredit") (.elem (.int packedUInt128Int))) (.var "fee")),
     .inRange packedUInt128Int (.binary .sub (.cast (.var "postSlashPendingFee") (.elem (.int packedUInt128Int))) (.var "fee")),
     .var "fee"] = _
  by_cases hcredit : fee.toNat ≤ (low128 postCredit).toNat
  · have hpending : (low128 postPending).toNat < fee.toNat := by
      by_contra hn
      exact hbad ⟨hcredit, by omega⟩
    have hcs := evalCheckedSub128 (evalCast128 (evalWordLocal (cfg := config) (evm := evm) hc))
      (evalWordLocal hf) (low128_lt _) hcredit
    have hps := evalCheckedSubUnderflow (cfg := config) (evm := evm) ⟨128, by decide⟩
      (evalCast128 (evalWordLocal hp)) (evalWordLocal hf) hpending
    simp only [packedUInt128Int] at hcs hps ⊢
    simp only [evalExprs?, hcs, hps, bind, EvalResult.bind]
  · have hcs := evalCheckedSubUnderflow (cfg := config) (evm := evm) ⟨128, by decide⟩
      (evalCast128 (evalWordLocal hc)) (evalWordLocal hf) (Nat.lt_of_not_ge hcredit)
    simp only [packedUInt128Int] at hcs ⊢
    simp only [evalExprs?, hcs, bind, EvalResult.bind]

end Benchmarks.Midnight

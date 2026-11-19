import Benchmarks.Midnight.TakeConsumptionValues

/-! Checked accumulation and the selected offer cap in the source semantics. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeConsumptionStep (increment cap : Expr) : List Stmt :=
  [.assign .localVar { base := "newConsumed" }
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage takeConsumedRef) increment)),
   .require (.binary .le (.var "newConsumed") cap)]

theorem evalTakeConsumptionCap {cfg : Config} {frame : Frame} {evm : State}
    {value cap : UInt256} {expr : Expr}
    (hv : frame.locals.get? "newConsumed" = some (.int value.toNat))
    (hc : evalExpr? cfg frame evm expr = .ok (.int cap.toNat)) :
    evalExpr? cfg frame evm (.binary .le (.var "newConsumed") expr) =
      .ok (.bool (decide (value.toNat ≤ cap.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalWordLocal hv, hc]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_le]

theorem takeConsumptionStepSource {frame : Frame} {evm : State}
    {old increment cap : UInt256} {incExpr capExpr : Expr} {previous : Value}
    (hn : frame.locals.get? "newConsumed" = some previous)
    (ho : evalExpr? config frame evm (.storage takeConsumedRef) = .ok (.int old.toNat))
    (hi : evalExpr? config frame evm incExpr = .ok (.int increment.toNat))
    (hc : evalExpr? config (wordLocal frame "newConsumed" (old + increment)) evm capExpr =
      .ok (.int cap.toNat))
    (hsafe : old.toNat + increment.toNat ≤ cap.toNat) :
    ExecBlock config frame evm (takeConsumptionStep incExpr capExpr)
      (.ok (wordLocal frame "newConsumed" (old + increment)) evm) := by
  have hfit : old.toNat + increment.toNat < UInt256.size :=
    lt_of_le_of_lt hsafe cap.val.isLt
  have hadd : (old + increment).toNat = old.toNat + increment.toNat :=
    addWord_toNat old increment hfit
  have hle : (old + increment).toNat ≤ cap.toNat := by
    rw [hadd]
    exact hsafe
  exact ExecBlock.consNormal (execLocalAssign hn (checkedAddSourceOk ho hi hfit))
    (ExecBlock.consNormal (ExecStmt.requireTrue (by
      simpa only [decide_eq_true hle] using evalTakeConsumptionCap (wordLocal_get ..) hc))
      ExecBlock.nil)

theorem takeConsumptionStepRevert {frame : Frame} {evm : State}
    {old increment cap : UInt256} {incExpr capExpr : Expr} {previous : Value}
    (hn : frame.locals.get? "newConsumed" = some previous)
    (ho : evalExpr? config frame evm (.storage takeConsumedRef) = .ok (.int old.toNat))
    (hi : evalExpr? config frame evm incExpr = .ok (.int increment.toNat))
    (hc : evalExpr? config (wordLocal frame "newConsumed" (old + increment)) evm capExpr =
      .ok (.int cap.toNat))
    (hbad : ¬ old.toNat + increment.toNat ≤ cap.toNat) :
    ExecBlock config frame evm (takeConsumptionStep incExpr capExpr) .reverted := by
  by_cases hfit : old.toNat + increment.toNat < UInt256.size
  · have hadd : (old + increment).toNat = old.toNat + increment.toNat :=
      addWord_toNat old increment hfit
    have hgt : ¬ (old + increment).toNat ≤ cap.toNat := by rwa [hadd]
    exact ExecBlock.consNormal (execLocalAssign hn (checkedAddSourceOk ho hi hfit))
      (ExecBlock.consRevert (ExecStmt.requireFalse (by
        simpa only [decide_eq_false hgt] using evalTakeConsumptionCap (wordLocal_get ..) hc)))
  · exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (checkedAddSourceOverflow ho hi (by omega)))

end Benchmarks.Midnight

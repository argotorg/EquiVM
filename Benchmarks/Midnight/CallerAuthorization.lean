import Benchmarks.Midnight.Authorization

/-! Caller-or-delegate authorization for an arbitrary source expression. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def callerOrDelegateGuard (userExpr : Expr) : Expr :=
  .binary .or (.binary .eq userExpr (.env .caller))
    (.storage { base := "isAuthorized", steps := [.mindex userExpr, .mindex (.env .caller)] })

-- GENERALIZES evalOnBehalfGuard to callers whose account has a different local name.
theorem evalCallerOrDelegate {frame : Frame} (evm : EVM.State) (user : UInt256) (expr : Expr)
    (hcanon : user.toNat < EVM.addressModulus) (hcontract : frame.contract = contract)
    (hbase : frame.locals.get? "isAuthorized" = none)
    (hget : evalExpr? config frame evm expr = .ok (.address (AccountAddress.ofNat user.toNat))) :
    evalExpr? config frame evm (callerOrDelegateGuard expr) =
      .ok (.bool (decide (onBehalfAllowed evm user))) := by
  have heq : evalExpr? config frame evm (.binary .eq expr (.env .caller)) =
      .ok (.bool (decide (user = solcSourceWord evm.executionEnv))) := by
    rw [evalExpr_binary_nonshort (by decide : BinaryOp.eq ≠ .and)
      (by decide : BinaryOp.eq ≠ .or), hget]
    simp only [evalExpr?, envValue, bind, pure, EvalResult.bind,
      evalBinaryOp?, Reasoning.VyperDispatch.value_address_beq]
    have hh : (AccountAddress.ofNat user.toNat = evm.executionEnv.source) ↔
        user = solcSourceWord evm.executionEnv := by
      rw [eq_comm, sourceAddress_eq_iff evm.executionEnv user hcanon, eq_comm]
    simp only [hh]
  have hread := evalAuthorization (evm := evm) user (solcSourceWord evm.executionEnv)
    expr (.env .caller) hcanon (solcSourceWord_canonical _) hcontract hbase hget
    (by simp only [evalExpr?, envValue, solcSource_ofNat, pure])
  change evalExpr? config frame evm (.binary .or _ _) = _
  rw [evalExpr?, heq]
  by_cases hself : user = solcSourceWord evm.executionEnv
  · simp [hself, onBehalfAllowed, EvalResult.bind, bind, pure]
  · simp [hself, onBehalfAllowed, EvalResult.bind, bind, pure, hread]

end Benchmarks.Midnight

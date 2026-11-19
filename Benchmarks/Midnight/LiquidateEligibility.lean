import Benchmarks.Midnight.LiquidateLoopSourceEntry
import Benchmarks.Midnight.LockSource

/-! The transient lock and maturity-or-health condition controlling liquidation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def LiquidateEligible (I : ExecutionEnv) (m : MarketData)
    (lock mode originalDebt maxDebt : UInt256) : Prop :=
  lock = ⟨0⟩ ∧ if mode = ⟨0⟩ then maxDebt.toNat < originalDebt.toNat
    else m.maturity.toNat < (UInt256.ofNat I.header.timestamp).toNat

instance (I : ExecutionEnv) (m : MarketData) (lock mode originalDebt maxDebt : UInt256) :
    Decidable (LiquidateEligible I m lock mode originalDebt maxDebt) := by
  unfold LiquidateEligible
  infer_instance

def liquidateEligibilityExpr : Expr :=
  .binary .and (.unary .not (.var "__c11"))
    (.ite (.var "postMaturityMode")
      (.binary .gt (.env .timestamp) (.field (.var "market") "maturity"))
      (.binary .gt (.var "originalDebt") (.var "maxDebt")))

theorem callLiquidationLocked {frame : Frame} {evm : State} {id user : UInt256}
    {args : List Expr} {name : Ident} (hc : frame.contract = contract)
    (ha : evalExprs? config frame evm args =
      .ok [wordBytes32Value id, .address (AccountAddress.ofNat user.toNat)])
    (hcanon : user.toNat < EVM.addressModulus) :
    ExecStmt config frame evm (.internalCall "liquidationLocked_body" args name)
      (.ok { frame with locals := (frame.locals.insert name
        (lockValue evm liquidationLockBase id user)) } evm) := by
  apply internalCallFunctionReturn (callee := liquidationLockedFunction)
    (locals := lockBodyArguments id user)
    (value := some [lockValue evm liquidationLockBase id user]) ha
  · rw [hc]; rfl
  · rfl
  · rw [hc]
    exact liquidationLockedInternalReturns evm frame.immutables id user hcanon

theorem evalLiquidateEligibility {frame : Frame} {evm : State} {m : MarketData}
    {lock mode originalDebt maxDebt : UInt256}
    (hl : frame.locals.get? "__c11" = some (wordToElem .bool lock))
    (hmode : frame.locals.get? "postMaturityMode" = some (wordToElem .bool mode))
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (ho : frame.locals.get? "originalDebt" = some (.int originalDebt.toNat))
    (hd : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat)) :
    evalExpr? config frame evm liquidateEligibilityExpr =
      .ok (.bool (decide (LiquidateEligible evm.executionEnv m lock mode originalDebt maxDebt))) := by
  have hmaturity := evalMarketMaturity (cfg := config) (evm := evm) hm
  by_cases hlock : lock = ⟨0⟩ <;> by_cases hpost : mode = ⟨0⟩ <;>
    simp only [liquidateEligibilityExpr, evalExpr?, hl, hmode, ho, hd, hmaturity,
      wordToElemBool, hlock, hpost, decide_true, decide_false,
      EvalResult.ofOption, bind, pure, EvalResult.bind, evalUnaryOp?, evalBinaryOp?, envValue,
      LiquidateEligible, ite_true, ite_false, Bool.not_true, Bool.not_false, Int.ofNat_lt,
      Int.ofNat_eq_natCast, true_and, false_and]

end Benchmarks.Midnight

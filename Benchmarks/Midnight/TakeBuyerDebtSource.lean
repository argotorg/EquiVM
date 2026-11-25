import Benchmarks.Midnight.NamedPositionAssign
import Benchmarks.Midnight.TakeCreditChangesSource
import Benchmarks.Midnight.ToUint128Source

variable {fork : Ethereum.Fork}

/-! The buyer's debt repayment is bounded by the saved uint128 debt. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyerRepayment (units debt : UInt256) : UInt256 :=
  UInt256.sub units (zeroFloorSubWord units debt)

-- LIBRARY CANDIDATE: removing the saturating excess leaves at most the debt.
theorem takeBuyerRepayment_bounds (units debt : UInt256) :
    (zeroFloorSubWord units debt).toNat ≤ units.toNat ∧
      (takeBuyerRepayment units debt).toNat ≤ debt.toNat := by
  have hi : (zeroFloorSubWord units debt).toNat ≤ units.toNat := by
    rw [zeroFloorSubWord_toNat]
    omega
  refine ⟨hi, ?_⟩
  rw [takeBuyerRepayment, usub_toNat hi, zeroFloorSubWord_toNat]
  omega

def takeBuyerDebtFrame (frame : Frame) (units debt : UInt256) : Frame :=
  wordLocal frame "__c21" (takeBuyerRepayment units debt)

def takeBuyerDebtState (evm : State) (id buyer units : UInt256) : State :=
  storeLow128 evm (positionSlot id buyer + ⟨2⟩)
    (UInt256.sub (low128 (healthPositionWord evm id buyer))
      (takeBuyerRepayment units (low128 (healthPositionWord evm id buyer))))

theorem takeBuyerDebt_shape : takeTransition.body.drop 46 =
    takeTransition.body[46]! :: takeTransition.body[47]! :: takeTransition.body.drop 48 := rfl

theorem takeBuyerRepayCall {frame : Frame} {evm : State} {units debt : UInt256}
    (hc : frame.contract = contract)
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hi : frame.locals.get? "buyerCreditIncrease" =
      some (.int (zeroFloorSubWord units debt).toNat))
    (hd : debt.toNat < 2^128) :
    ExecStmt fork config frame evm takeTransition.body[46]!
      (.ok (takeBuyerDebtFrame frame units debt) evm) := by
  have hb := takeBuyerRepayment_bounds units debt
  apply callToUint128 hc
  · simp only [evalExprs?, evalExpr_uint256_sub (evalWordLocal hu) (evalWordLocal hi) hb.1,
      bind, pure, EvalResult.bind]
    rfl
  · exact Nat.lt_of_le_of_lt hb.2 hd

theorem takeBuyerDebtWrite {frame : Frame} {evm : State} {id buyer units : UInt256}
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hc : buyer.toNat < EVM.addressModulus)
    (hr : frame.locals.get? "__c21" =
      some (.int (takeBuyerRepayment units (low128 (healthPositionWord evm id buyer))).toNat))
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config frame evm takeTransition.body[47]!
      (.ok frame (takeBuyerDebtState evm id buyer units)) :=
  ExecStmt.assign (Or.inr hperm)
    (evalCheckedSub128 (evalNamedPositionDebt hc hp) (evalWordLocal hr) (low128_lt _)
      (takeBuyerRepayment_bounds units (low128 (healthPositionWord evm id buyer))).2)
    (assignNamedPositionDebt _ hc hp)

theorem takeBuyerDebtWriteStatic {frame : Frame} {evm : State} {id buyer units : UInt256}
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hc : buyer.toNat < EVM.addressModulus)
    (hr : frame.locals.get? "__c21" =
      some (.int (takeBuyerRepayment units (low128 (healthPositionWord evm id buyer))).toNat))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt fork config frame evm takeTransition.body[47]! .staticViolation :=
  ExecStmt.assignStatic
    (evalCheckedSub128 (evalNamedPositionDebt hc hp) (evalWordLocal hr) (low128_lt _)
      (takeBuyerRepayment_bounds units (low128 (healthPositionWord evm id buyer))).2)
    (assignNamedPositionDebt _ hc hp) hperm

end Benchmarks.Midnight

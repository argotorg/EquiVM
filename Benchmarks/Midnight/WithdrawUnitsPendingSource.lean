import Benchmarks.Midnight.WithdrawUnitsSourceFrame
import Benchmarks.Midnight.WithdrawUnitsPendingTrace
import Benchmarks.Midnight.ToUint128Source

/-! Source execution of withdrawal's conditional pending-fee reduction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawUnitsPendingFrame (frame : Frame) (decrease : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal frame "__c2" decrease) "__c3" decrease)
    "pendingFeeDecrease" decrease

def withdrawUnitsPendingArgs : List Expr :=
  [.storage { base := "_position", steps := [.field "pendingFee"] }, .var "units",
    .storage { base := "_position", steps := [.field "credit"] }]

theorem withdrawUnitsPendingArgs_eval {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {receiver : AccountAddress}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus) :
    evalExprs? config frame evm withdrawUnitsPendingArgs =
      .ok [.int (positionFieldWord evm id user 1).toNat, .int units.toNat,
        .int (positionFieldWord evm id user 0).toNat] := by
  have hp := evalPositionAliasField (evm := evm) 1 hcanon hf.position
  have hc := evalPositionAliasField (evm := evm) 0 hcanon hf.position
  simpa only [withdrawUnitsPendingArgs, evalExprs?, evalWordLocal hf.units,
    EvalResult.bind, bind, pure] using
    (show evalExprs? config frame evm
        [.storage { base := "_position", steps := [.field (positionFieldName 1)] }, .var "units",
         .storage { base := "_position", steps := [.field (positionFieldName 0)] }] = _ by
      simp only [evalExprs?, hp, hc, evalWordLocal hf.units, EvalResult.bind, bind, pure])

theorem withdrawUnitsCreditGuard {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {receiver : AccountAddress}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus) :
    evalExpr? config frame evm (.binary .gt
      (.storage { base := "_position", steps := [.field "credit"] }) (.intLit 0)) =
      .ok (.bool (decide (0 < (positionFieldWord evm id user 0).toNat))) := by
  have hc := evalPositionAliasField (evm := evm) 0 hcanon hf.position
  change evalExpr? config frame evm
    (.storage { base := "_position", steps := [.field "credit"] }) = _ at hc
  rw [evalExpr_binary_nonshort (by decide) (by decide), hc]
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, Int.natCast_pos]

theorem withdrawUnitsPendingReturns {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {receiver : AccountAddress}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus)
    (hzero : frame.locals.get? "pendingFeeDecrease" = some (.int 0))
    (hpos : 0 < (positionFieldWord evm id user 0).toNat)
    (hsafe : WithdrawPendingSafe (EVM.storageLoad evm evm.executionEnv.codeOwner
      (positionSlot id user)) units)
    (hperm : evm.executionEnv.perm = true) :
    let decrease := mulDivUp (positionFieldWord evm id user 1) units
      (positionFieldWord evm id user 0)
    ExecStmt config frame evm (withdrawTransition.body[9]!)
      (.ok (withdrawUnitsPendingFrame frame decrease)
        (storeHigh128 evm (positionSlot id user)
          (UInt256.sub (positionFieldWord evm id user 1) decrease))) := by
  let decrease := mulDivUp (positionFieldWord evm id user 1) units
    (positionFieldWord evm id user 0)
  change MulDivUpSafe (positionFieldWord evm id user 1) units
      (positionFieldWord evm id user 0) ∧ decrease.toNat < 2^128 ∧
        decrease.toNat ≤ (positionFieldWord evm id user 1).toNat at hsafe
  apply ExecStmt.iteTrue ((withdrawUnitsCreditGuard hf hcanon).trans
    (by rw [decide_eq_true hpos]))
  apply ExecBlock.consNormal (callMulDivUp hf.contract (withdrawUnitsPendingArgs_eval hf hcanon)
    hsafe.1 (name := "__c2"))
  have hf1 := hf.insert "__c2" (.int decrease.toNat) (by decide)
  have hf2 := hf1.insert "__c3" (.int decrease.toNat) (by decide)
  have hf3 := hf2.insert "pendingFeeDecrease" (.int decrease.toNat) (by decide)
  have hargs : evalExprs? config (wordLocal frame "__c2" decrease) evm [.var "__c2"] =
      .ok [.int decrease.toNat] := by
    simp only [evalExprs?, evalWordLocal (wordLocal_get ..), EvalResult.bind, bind, pure]
  apply ExecBlock.consNormal (callToUint128 hf1.contract hargs hsafe.2.1 (name := "__c3"))
  refine ExecBlock.consNormal
    (execLocalAssign (old := .int 0) (value := .int decrease.toNat) ?_ ?_) ?_
  · change (wordLocal (wordLocal frame "__c2" decrease) "__c3" decrease).locals.get?
      "pendingFeeDecrease" = _
    rw [wordLocal_get_ne _ _ _ _ (by decide), wordLocal_get_ne _ _ _ _ (by decide), hzero]
  · exact evalWordLocal (wordLocal_get ..)
  · exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
      (evalCheckedSub128 (evalPositionAliasField 1 hcanon hf3.position)
        (evalWordLocal (wordLocal_get ..)) (positionFieldWord_lt evm id user 1) hsafe.2.2)
      (assignPositionAliasField 1 _ hcanon hf3.position)) ExecBlock.nil

theorem withdrawUnitsPendingZero {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {receiver : AccountAddress}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus)
    (hzero : (positionFieldWord evm id user 0).toNat = 0) :
    ExecStmt config frame evm (withdrawTransition.body[9]!) (.ok frame evm) := by
  exact ExecStmt.iteFalse ((withdrawUnitsCreditGuard hf hcanon).trans
    (by rw [hzero]; rfl)) ExecBlock.nil

theorem withdrawUnitsPendingReverts {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {receiver : AccountAddress}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus)
    (hzero : frame.locals.get? "pendingFeeDecrease" = some (.int 0))
    (hpos : 0 < (positionFieldWord evm id user 0).toNat)
    (hbad : ¬ WithdrawPendingSafe (EVM.storageLoad evm evm.executionEnv.codeOwner
      (positionSlot id user)) units) :
    ExecStmt config frame evm (withdrawTransition.body[9]!) .reverted := by
  let decrease := mulDivUp (positionFieldWord evm id user 1) units
    (positionFieldWord evm id user 0)
  change ¬ (MulDivUpSafe (positionFieldWord evm id user 1) units
      (positionFieldWord evm id user 0) ∧ decrease.toNat < 2^128 ∧
        decrease.toNat ≤ (positionFieldWord evm id user 1).toNat) at hbad
  apply ExecStmt.iteTrue ((withdrawUnitsCreditGuard hf hcanon).trans
    (by rw [decide_eq_true hpos]))
  by_cases hmul : MulDivUpSafe (positionFieldWord evm id user 1) units
      (positionFieldWord evm id user 0)
  · apply ExecBlock.consNormal (callMulDivUp hf.contract
      (withdrawUnitsPendingArgs_eval hf hcanon) hmul (name := "__c2"))
    have hf1 := hf.insert "__c2" (.int decrease.toNat) (by decide)
    have hargs : evalExprs? config (wordLocal frame "__c2" decrease) evm [.var "__c2"] =
        .ok [.int decrease.toNat] := by
      simp only [evalExprs?, evalWordLocal (wordLocal_get ..), EvalResult.bind, bind, pure]
    by_cases h128 : decrease.toNat < 2^128
    · apply ExecBlock.consNormal (callToUint128 hf1.contract hargs h128 (name := "__c3"))
      have hf2 := hf1.insert "__c3" (.int decrease.toNat) (by decide)
      have hf3 := hf2.insert "pendingFeeDecrease" (.int decrease.toNat) (by decide)
      have hz : (wordLocal (wordLocal frame "__c2" decrease) "__c3" decrease).locals.get?
          "pendingFeeDecrease" = some (.int 0) := by
        rw [wordLocal_get_ne _ _ _ _ (by decide), wordLocal_get_ne _ _ _ _ (by decide), hzero]
      apply ExecBlock.consNormal (execLocalAssign hz (evalWordLocal (wordLocal_get ..)))
      have hlt : (positionFieldWord evm id user 1).toNat < decrease.toNat := by
        by_contra hn
        exact hbad ⟨hmul, h128, by omega⟩
      exact ExecBlock.consRevert (ExecStmt.assignExprRevert
        (evalCheckedSubUnderflow ⟨128, by decide⟩
          (evalPositionAliasField 1 hcanon hf3.position)
          (evalWordLocal (wordLocal_get ..)) hlt))
    · exact ExecBlock.consRevert (callToUint128Revert hf1.contract hargs
        (Nat.le_of_not_lt h128))
  · exact ExecBlock.consRevert (callMulDivUpRevert hf.contract
      (withdrawUnitsPendingArgs_eval hf hcanon) hmul)

end Benchmarks.Midnight

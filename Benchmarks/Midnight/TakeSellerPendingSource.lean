import Benchmarks.Midnight.TakeBuyerPendingSource
import Benchmarks.Midnight.MulDivUpBounded

/-! The proportional seller pending-fee reduction fits in uint128. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSellerPendingValue (credit pending decrease : UInt256) : UInt256 :=
  if credit = ⟨0⟩ then ⟨0⟩ else mulDivUp pending decrease credit

def takeSellerPendingInit (frame : Frame) : Frame :=
  wordLocal frame "sellerPendingFeeDecrease" ⟨0⟩

def takeSellerPendingActiveFrame (frame : Frame) (value : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (takeSellerPendingInit frame) "decrease" value)
    "checkedDecrease" value) "sellerPendingFeeDecrease" value

def takeSellerPendingFrame (frame : Frame) (credit pending decrease : UInt256) : Frame :=
  if credit = ⟨0⟩ then takeSellerPendingInit frame else
    takeSellerPendingActiveFrame frame (mulDivUp pending decrease credit)

def takeSellerPendingArgs : List Expr :=
  [.storage { base := "sellerPos", steps := [.field "pendingFee"] }, .var "sellerCreditDecrease",
    .storage { base := "sellerPos", steps := [.field "credit"] }]

def takeSellerPendingCondition : Expr :=
  .binary .gt (.storage { base := "sellerPos", steps := [.field "credit"] }) (.intLit 0)

def takeSellerPendingStmt : Stmt :=
  .ite takeSellerPendingCondition
    [.internalCall "UtilsLib_mulDivUp" takeSellerPendingArgs "decrease",
      .internalCall "UtilsLib_toUint128" [.var "decrease"] "checkedDecrease",
      .assign .localVar { base := "sellerPendingFeeDecrease" } (.var "checkedDecrease")] []

theorem takeSellerPending_shape : takeTransition.body.drop 40 =
    .letDecl "sellerPendingFeeDecrease"
      (some (.elem (.int (.uint ⟨128, by decide⟩)))) (.intLit 0) ::
      takeSellerPendingStmt :: takeTransition.body.drop 42 := rfl

theorem takeSellerPendingValue_lt {credit pending decrease : UInt256}
    (hc : credit.toNat < 2^128) (hp : pending.toNat < 2^128) (hd : decrease.toNat ≤ credit.toNat) :
    (takeSellerPendingValue credit pending decrease).toNat < 2^128 := by
  unfold takeSellerPendingValue
  split
  · decide
  · rename_i hn
    have hpos := Nat.pos_of_ne_zero (fun h ↦ hn (uint256_toNat_eq_zero h))
    exact (mulDivUp_le_left (mulDivUpSafe_uint128 hp hc hd hpos) hd).trans_lt hp

theorem evalTakeSellerPendingArgs {frame : Frame} {evm : State} {id seller decrease : UInt256}
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hd : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hcanon : seller.toNat < EVM.addressModulus) :
    evalExprs? config frame evm takeSellerPendingArgs =
      .ok [.int (positionFieldWord evm id seller 1).toNat, .int decrease.toNat,
        .int (positionFieldWord evm id seller 0).toNat] := by
  have he0 := evalNamedPositionField (evm := evm) 0 hcanon hp
  have he1 := evalNamedPositionField (evm := evm) 1 hcanon hp
  change evalExpr? config frame evm (.storage { base := "sellerPos", steps := [.field "credit"] }) =
    .ok (.int (positionFieldWord evm id seller 0).toNat) at he0
  change evalExpr? config frame evm
    (.storage { base := "sellerPos", steps := [.field "pendingFee"] }) =
      .ok (.int (positionFieldWord evm id seller 1).toNat) at he1
  simp only [takeSellerPendingArgs, evalExprs?, he0, he1, evalWordLocal hd,
    bind, pure, EvalResult.bind]

theorem evalTakeSellerPendingCondition {frame : Frame} {evm : State} {id seller : UInt256}
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hcanon : seller.toNat < EVM.addressModulus) :
    evalExpr? config frame evm takeSellerPendingCondition =
      .ok (.bool (decide (0 < (positionFieldWord evm id seller 0).toNat))) := by
  have he := evalNamedPositionField (evm := evm) 0 hcanon hp
  change evalExpr? config frame evm (.storage { base := "sellerPos", steps := [.field "credit"] }) =
    .ok (.int (positionFieldWord evm id seller 0).toNat) at he
  rw [takeSellerPendingCondition, evalExpr_binary_nonshort (by decide) (by decide), he]
  simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?, Int.natCast_pos]

theorem takeSellerPendingSource {frame : Frame} {evm : State} {id seller decrease : UInt256}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hd : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hcanon : seller.toNat < EVM.addressModulus)
    (hle : decrease.toNat ≤ (positionFieldWord evm id seller 0).toNat) :
    ABlock config evm frame (takeTransition.body.drop 40)
      (takeSellerPendingFrame frame (positionFieldWord evm id seller 0)
        (positionFieldWord evm id seller 1) decrease) (takeTransition.body.drop 42) := by
  have hp1 : (takeSellerPendingInit frame).locals.get? "sellerPos" =
      some (.storageRef (positionRef id seller) positionType) :=
    (store_get_ne _ _ (by decide)).trans hp
  have hd1 : (takeSellerPendingInit frame).locals.get? "sellerCreditDecrease" =
      some (.int decrease.toNat) := (store_get_ne _ _ (by decide)).trans hd
  have he := evalTakeSellerPendingCondition (evm := evm) hp1 hcanon
  have hinit : ExecStmt config frame evm takeTransition.body[40]!
      (.ok (takeSellerPendingInit frame) evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  rw [takeSellerPending_shape]
  refine ⟨fun h ↦ ExecBlock.consNormal hinit (ExecBlock.consNormal ?_ h)⟩
  by_cases hz : positionFieldWord evm id seller 0 = ⟨0⟩
  · simp only [takeSellerPendingFrame, if_pos hz]
    exact ExecStmt.iteFalse (he.trans (by rw [hz]; rfl)) ExecBlock.nil
  · have hpos := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    have hsafe := mulDivUpSafe_uint128 (positionFieldWord_lt evm id seller 1)
      (positionFieldWord_lt evm id seller 0) hle hpos
    have hsmall := (mulDivUp_le_left hsafe hle).trans_lt (positionFieldWord_lt evm id seller 1)
    simp only [takeSellerPendingFrame, if_neg hz]
    apply ExecStmt.iteTrue (he.trans (by rw [decide_eq_true hpos]))
    apply ExecBlock.consNormal (callMulDivUp (frame := takeSellerPendingInit frame) hc
      (evalTakeSellerPendingArgs hp1 hd1 hcanon) hsafe)
    have hargs : evalExprs? config (wordLocal (takeSellerPendingInit frame) "decrease"
        (mulDivUp (positionFieldWord evm id seller 1) decrease (positionFieldWord evm id seller 0)))
        evm [.var "decrease"] = .ok [.int
          (mulDivUp (positionFieldWord evm id seller 1) decrease
            (positionFieldWord evm id seller 0)).toNat] := by
      simp only [evalExprs?, evalWordLocal (wordLocal_get ..), bind, pure, EvalResult.bind]
    apply ExecBlock.consNormal (callToUint128 (frame := wordLocal (takeSellerPendingInit frame)
      "decrease" (mulDivUp (positionFieldWord evm id seller 1) decrease
        (positionFieldWord evm id seller 0))) hc hargs hsmall)
    refine ExecBlock.consNormal (execLocalAssign (old := .int 0) ?_ ?_) ExecBlock.nil
    · exact (store_get_ne _ _ (by decide)).trans
        ((store_get_ne _ _ (by decide)).trans (store_get_self ..))
    · exact evalWordLocal (wordLocal_get ..)

theorem TakeSourceFrame.sellerPending {frame : Frame} {offer : OfferData}
    {id units taker credit pending decrease : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeSellerPendingFrame frame credit pending decrease) offer id units taker
      receiver callback ratifierData data := by
  unfold takeSellerPendingFrame
  split
  · exact hf.insert "sellerPendingFeeDecrease" _ (by decide)
  · exact (((hf.insert "sellerPendingFeeDecrease" _ (by decide)).insert "decrease" _
      (by decide)).insert "checkedDecrease" _ (by decide)).insert "sellerPendingFeeDecrease" _
      (by decide)

end Benchmarks.Midnight

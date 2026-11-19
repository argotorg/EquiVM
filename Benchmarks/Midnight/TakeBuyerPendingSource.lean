import Benchmarks.Midnight.TakeCreditChangesSource
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.TakeOfferGuardsSource

/-! The buyer's pending fee includes two checked products and a checked narrowing cast. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takePendingScale : UInt256 := UInt256.ofNat 1000000000000000000

def takeBuyerPendingValue (rate time increase : UInt256) : UInt256 :=
  mulDivDown increase (UInt256.mul rate time) takePendingScale

def TakeBuyerPendingSafe (rate time increase : UInt256) : Prop :=
  rate.toNat * time.toNat < UInt256.size ∧
    increase.toNat * (UInt256.mul rate time).toNat < UInt256.size ∧
    (takeBuyerPendingValue rate time increase).toNat < 2^128

def takePendingRateExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .mul
    (.storage { base := "_marketState", steps := [.field "continuousFee"] })
    (.var "timeToMaturity"))

def takeBuyerPendingArgs : List Expr :=
  [.var "buyerCreditIncrease", takePendingRateExpr, .intLit 1000000000000000000]

def takeBuyerPendingFrame (frame : Frame) (rate time increase : UInt256) : Frame :=
  wordLocal (wordLocal frame "__c15" (takeBuyerPendingValue rate time increase))
    "buyerPendingFeeIncrease" (takeBuyerPendingValue rate time increase)

theorem takeBuyerPending_shape : takeTransition.body.drop 38 =
    .internalCall "UtilsLib_mulDivDown" takeBuyerPendingArgs "__c15" ::
    .internalCall "UtilsLib_toUint128" [.var "__c15"] "buyerPendingFeeIncrease" ::
      takeTransition.body.drop 40 := rfl

theorem evalTakeBuyerPendingArgs {frame : Frame} {evm : State} {id time increase : UInt256}
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hfit : (marketContinuousFee (marketFeeWord evm id)).toNat * time.toNat < UInt256.size) :
    evalExprs? config frame evm takeBuyerPendingArgs =
      .ok [.int increase.toNat,
        .int (UInt256.mul (marketContinuousFee (marketFeeWord evm id)) time).toNat,
        .int takePendingScale.toNat] := by
  have he : evalExpr? config frame evm takePendingRateExpr =
      .ok (.int (UInt256.mul (marketContinuousFee (marketFeeWord evm id)) time).toNat) :=
    checkedMulSourceOk (evalMarketAliasContinuousFee hm) (evalWordLocal ht) hfit
  simp only [takeBuyerPendingArgs, evalExprs?, evalWordLocal hi, he, evalExpr?, bind,
    pure, EvalResult.bind]
  rfl

theorem takeBuyerPendingSource {frame : Frame} {evm : State} {id time increase : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hs : TakeBuyerPendingSafe (marketContinuousFee (marketFeeWord evm id)) time increase) :
    ABlock config evm frame (takeTransition.body.drop 38)
      (takeBuyerPendingFrame frame (marketContinuousFee (marketFeeWord evm id)) time increase)
      (takeTransition.body.drop 40) := by
  rw [takeBuyerPending_shape]
  refine ⟨fun h ↦ ExecBlock.consNormal
    (callMulDivDown hc (evalTakeBuyerPendingArgs hm ht hi hs.1) hs.2.1 (by decide))
    (ExecBlock.consNormal (callToUint128 hc ?_ hs.2.2) h)⟩
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, collapseReturns, store_get_self,
    EvalResult.ofOption, bind, pure, EvalResult.bind]
  rfl

theorem takeBuyerPendingSourceRevert {frame : Frame} {evm : State} {id time increase : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hs : ¬ TakeBuyerPendingSafe (marketContinuousFee (marketFeeWord evm id)) time increase) :
    ExecBlock config frame evm (takeTransition.body.drop 38) .reverted := by
  rw [takeBuyerPending_shape]
  by_cases hfit : (marketContinuousFee (marketFeeWord evm id)).toNat * time.toNat < UInt256.size
  · have hargs := evalTakeBuyerPendingArgs hm ht hi hfit
    by_cases hprod : increase.toNat *
        (UInt256.mul (marketContinuousFee (marketFeeWord evm id)) time).toNat < UInt256.size
    · have hlarge : 2^128 ≤
          (takeBuyerPendingValue (marketContinuousFee (marketFeeWord evm id)) time increase).toNat
          :=
        Nat.le_of_not_gt (fun h ↦ hs ⟨hfit, hprod, h⟩)
      apply ExecBlock.consNormal (callMulDivDown hc hargs hprod (by decide))
      apply ExecBlock.consRevert
      apply callToUint128Revert (frame := wordLocal frame "__c15"
        (takeBuyerPendingValue (marketContinuousFee (marketFeeWord evm id)) time increase))
        hc _ hlarge
      simp only [evalExprs?, evalWordLocal (wordLocal_get ..), bind, pure, EvalResult.bind]
    · exact ExecBlock.consRevert (callMulDivDownRevert hc hargs (fun h ↦ hprod h.1))
  · have he : evalExpr? config frame evm takePendingRateExpr = .revert :=
      checkedMulSourceOverflow (evalMarketAliasContinuousFee hm) (evalWordLocal ht)
        (Nat.le_of_not_gt hfit)
    apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert _)
    simp only [takeBuyerPendingArgs, evalExprs?, evalWordLocal hi, he, bind, EvalResult.bind]

theorem TakeSourceFrame.buyerPending {frame : Frame} {offer : OfferData}
    {id units taker rate time increase : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeBuyerPendingFrame frame rate time increase) offer id units taker receiver
      callback ratifierData data :=
  (hf.insert "__c15" _ (by decide)).insert "buyerPendingFeeIncrease" _ (by decide)

end Benchmarks.Midnight

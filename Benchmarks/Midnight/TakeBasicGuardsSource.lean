import Benchmarks.Midnight.OfferSourceValues
import Benchmarks.Midnight.TakeCapsGuard
import Benchmarks.Midnight.MarketLossStorage

variable {fork : Ethereum.Fork}

/-! The source market alias, saturated-loss check, and mutually exclusive offer caps. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeMarketAliasFrame (frame : Frame) (id : UInt256) : Frame :=
  { frame with locals := (frame.locals.insert "_marketState"
      (.storageRef (marketStateRef id) marketStateType)) }

theorem takeMarketAliasPrefix {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker : UInt256} {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    ABlock fork config evm frame (takeTransition.body.drop 5) (takeMarketAliasFrame frame id)
      (takeTransition.body.drop 6) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  apply resolveBytes32Mapping
  · exact hf.marketState
  · exact hf.idValue
  · rw [hf.contract]
    rfl

def takeLossGuard : Expr :=
  .binary .lt (.storage { base := "_marketState", steps := [.field "lossFactor"] })
    (.intLit (2^128 - 1))

def takeCapsGuard : Expr :=
  .binary .ne (.binary .eq (.field (.var "offer") "maxAssets") (.intLit 0))
    (.binary .eq (.field (.var "offer") "maxUnits") (.intLit 0))

theorem evalTakeLossGuard {frame : Frame} {evm : State} {id : UInt256}
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType)) :
    evalExpr? config frame evm takeLossGuard =
      .ok (.bool (decide ((marketLossWord evm id).toNat < 2^128 - 1))) := by
  unfold takeLossGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalMarketAliasLoss hm]
  simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
  norm_num

theorem evalTakeCapsGuard {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm takeCapsGuard = .ok (.bool (decide (TakeCapsValid offer))) := by
  unfold takeCapsGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide),
    evalExpr_binary_nonshort (by decide : BinaryOp.eq ≠ .and) (by decide : BinaryOp.eq ≠ .or),
    evalOfferMaxAssets ho]
  rw [evalExpr_binary_nonshort (by decide : BinaryOp.eq ≠ .and) (by decide : BinaryOp.eq ≠ .or),
    evalOfferMaxUnits ho]
  have hz (word : UInt256) : word.toNat = 0 ↔ word = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩
  simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?,
    Reasoning.VyperDispatch.value_int_beq, Int.natCast_eq_zero, hz]
  by_cases ha : offer.maxAssets = ⟨0⟩ <;> by_cases hu : offer.maxUnits = ⟨0⟩ <;>
    simp [TakeCapsValid, ha, hu]

theorem takeLossRevert {frame : Frame} {evm : State} {id : UInt256}
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hbad : ¬ (marketLossWord evm id).toNat < 2^128 - 1) :
    ExecBlock fork config frame evm (takeTransition.body.drop 6) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse ((evalTakeLossGuard hm).trans
    (by rw [decide_eq_false hbad])))

theorem takeCapsRevert {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hbad : ¬ TakeCapsValid offer) :
    ExecBlock fork config frame evm (takeTransition.body.drop 7) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse ((evalTakeCapsGuard ho).trans
    (by rw [decide_eq_false hbad])))

theorem takeLossCapsSource {frame : Frame} {evm : State} {offer : OfferData} {id : UInt256}
    {result : ExecResult}
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hl : (marketLossWord evm id).toNat < 2^128 - 1) (hc : TakeCapsValid offer)
    (htail : ExecBlock fork config frame evm (takeTransition.body.drop 8) result) :
    ExecBlock fork config frame evm (takeTransition.body.drop 6) result :=
  ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeLossGuard hm).trans
    (by rw [decide_eq_true hl])))
    (ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeCapsGuard ho).trans
      (by rw [decide_eq_true hc]))) htail)

end Benchmarks.Midnight

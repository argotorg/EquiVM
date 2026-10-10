import Benchmarks.UniswapV4PoolManager.PoolSwapStoreSource
import Benchmarks.UniswapV4PoolManager.PoolSwapDeltaSource
import Benchmarks.UniswapV4PoolManager.PoolSwapLoopLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapReturnValues (delta fee amount : UInt256) (r : PoolSwapResultWords) : List Value :=
  [.int (EVM.signed delta), .int (Int.ofNat amount.toNat), .int (Int.ofNat fee.toNat), poolSwapResultValue r]

def poolSwapFinishResult (f : Frame) (evm : State) (id packed : UInt256)
    (s : PoolSwapStepWords) (r : PoolSwapResultWords) (p : PoolSwapParamsWords)
    (remaining calculated fee amount : UInt256) : ExecResult :=
  let cf := poolSwapCalculatedFirst p.zeroForOne p.amountSpecified
  if evm.executionEnv.perm = false then .staticViolation else
  if poolSwapDeltaFits cf p.amountSpecified remaining calculated then
    .returned (poolSwapDeltaFrame (poolSwapSlot0Frame f packed r) cf p.amountSpecified remaining calculated)
      (poolSwapFinishPost evm id packed s r p.zeroForOne)
      (some (poolSwapReturnValues (poolSwapDeltaWord cf p.amountSpecified remaining calculated) fee amount r))
  else .reverted

theorem poolSwapFunction_finish : poolSwapFunction.body.drop 29 =
    (poolSwapFunction.body.drop 29).take 5 ++ [poolSwapFunction.body[34]!, poolSwapFunction.body[35]!] := rfl

theorem poolSwapReturnSource {f : Frame} {evm : State} {delta fee amount : UInt256} {r : PoolSwapResultWords}
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hf : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (ha : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat)))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) :
    ExecBlock config f evm [poolSwapFunction.body[35]!]
      (.returned f evm (some (poolSwapReturnValues delta fee amount r))) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  change evalExprs? config f evm [.var "swapDelta", .var "amountToProtocol", .var "swapFee", .var "result"] = _
  simp only [poolSwapReturnValues, evalExprs?, evalLocalValue hd, evalLocalValue ha,
    evalLocalValue hf, evalLocalValue hr, bind, EvalResult.bind, pure]

theorem poolSwapFinishSource {f : Frame} {evm : State} {id packed remaining calculated fee protocol amount : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords} {old : Value}
    (h : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (hslot : f.locals.get? "slot0Start" = some (wordBytes32Value packed))
    (hdelta : f.locals.get? "swapDelta" = some old)
    (hp : r.price.toNat < 2^160) (hl : r.liquidity.toNat < 2^128) :
    ExecBlock config f evm (poolSwapFunction.body.drop 29)
      (poolSwapFinishResult f evm id packed s r p remaining calculated fee amount) := by
  rw [poolSwapFunction_finish]
  let f1 := poolSwapSlot0Frame f packed r
  let post := poolSwapFinishPost evm id packed s r p.zeroForOne
  let cf := poolSwapCalculatedFirst p.zeroForOne p.amountSpecified
  have hstore := poolSwapStoreSource (evm := evm) h.contract h.self h.step h.result h.direction hslot hp hl
  dsimp only [poolSwapFinishResult]
  by_cases hperm : evm.executionEnv.perm = false
  · rw [if_pos hperm] at hstore ⊢
    exact execBlock_append_term hstore (by intros; intro he; cases he)
  · rw [if_neg hperm] at hstore ⊢
    have hget := poolSwapSlot0Frame_get f packed r
    have hd := poolSwapDeltaSource (f := f1) (evm := post) h.contract
      ((hget "params" (by decide) (by decide)).trans h.params)
      ((hget "amountSpecifiedRemaining" (by decide) (by decide)).trans h.remaining)
      ((hget "amountCalculated" (by decide) (by decide)).trans h.calculated)
      ((hget "zeroForOne" (by decide) (by decide)).trans h.direction)
      ((hget "swapDelta" (by decide) (by decide)).trans hdelta)
    dsimp only at hd
    by_cases hf : poolSwapDeltaFits cf p.amountSpecified remaining calculated
    · rw [if_pos hf] at hd ⊢
      have hget2 := poolSwapDeltaFrame_get f1 cf p.amountSpecified remaining calculated
      have hreturn := poolSwapReturnSource (evm := post) (poolSwapDeltaFrame_delta f1 cf p.amountSpecified remaining calculated)
        ((hget2 "swapFee" (by cases cf <;> decide) (by cases cf <;> decide) (by cases cf <;> decide) (by decide)).trans
          ((hget "swapFee" (by decide) (by decide)).trans h.fee))
        ((hget2 "amountToProtocol" (by cases cf <;> decide) (by cases cf <;> decide) (by cases cf <;> decide) (by decide)).trans
          ((hget "amountToProtocol" (by decide) (by decide)).trans h.amount))
        ((hget2 "result" (by cases cf <;> decide) (by cases cf <;> decide) (by cases cf <;> decide) (by decide)).trans
          ((hget "result" (by decide) (by decide)).trans h.result))
      exact execBlock_append hstore (ExecBlock.consNormal hd hreturn)
    · rw [if_neg hf] at hd ⊢
      exact execBlock_append hstore (ExecBlock.consRevert hd)

end Benchmarks.UniswapV4PoolManager

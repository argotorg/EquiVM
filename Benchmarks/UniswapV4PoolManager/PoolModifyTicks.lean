import Benchmarks.UniswapV4PoolManager.PoolModifyTwoTicks
import Benchmarks.UniswapV4PoolManager.PoolModifyTickFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyTicksBlock : List Stmt :=
  (poolModifyTickBlock false ++ poolModifyTickBlock true) ++
    [poolModifyLimitsStmt, poolModifyFlipStmt false, poolModifyFlipStmt true]
theorem poolModifyTicksStmt : poolModifyFunction.body[7]! =
    .ite (.binary .ne (.var "liquidityDelta") (.intLit 0)) poolModifyTicksBlock [] := rfl

def poolModifyTicksActiveResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  continueBlockResult (fun f1 post => poolModifyTickFinishResult f1 post id p
    (tickFlipped (poolModifyLowerPacked evm id p) p.delta)
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
    (tickFlipped (poolModifyUpperPacked evm id p) p.delta)
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta)))
    (poolModifyTwoTicksResult f evm id p)
def poolModifyTicksResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  if p.delta ≠ 0 then poolModifyTicksActiveResult f evm id p else .ok f evm
def poolModifyTicksState (evm : State) (id : UInt256) (p : PoolModifyParams) : Value :=
  if p.delta ≠ 0 then poolModifyTwoTicksState evm id p else poolModifyStateValue false ⟨0⟩ false ⟨0⟩

theorem poolModifyTicks {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p)
    (hs : f.locals.get? "state" = some (poolModifyStateValue false ⟨0⟩ false ⟨0⟩))
    (ht : poolTicksValid p.lower p.upper) :
    ExecStmt config f evm poolModifyFunction.body[7]! (poolModifyTicksResult f evm id p) := by
  rw [poolModifyTicksStmt]
  have he : evalExpr? config f evm (.binary .ne (.var "liquidityDelta") (.intLit 0)) =
      .ok (.bool (decide (p.delta ≠ 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hc.liquidityDelta]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?, BEq.beq, Value.int.injEq, decide_not]
  by_cases hd : p.delta ≠ 0
  · rw [poolModifyTicksResult, if_pos hd]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hd] using he)
    have hpre := poolModifyTwoTicks (evm := evm) hc.contract hc.self hc.lower hc.upper hc.liquidityDelta hs
    apply execBlock_continue hpre
    intro f1 post hpost
    exact poolModifyTickFinish (evm := post) (poolModifyTwoTicksResult_context hc hpost)
      (poolModifyTwoTicksResult_state hpost) ht
  · rw [poolModifyTicksResult, if_neg hd]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hd] using he) ExecBlock.nil

theorem poolModifyTicksResult_context {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} (hc : PoolModifyContext f id p)
    (h : poolModifyTicksResult f evm id p = .ok f' post) : PoolModifyContext f' id p := by
  unfold poolModifyTicksResult at h
  split_ifs at h with hd
  · obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
    exact poolModifyTickFinishResult_context (poolModifyTwoTicksResult_context hc hlo) hup
  · cases h
    exact hc

theorem poolModifyTicksResult_state {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams}
    (hs : f.locals.get? "state" = some (poolModifyStateValue false ⟨0⟩ false ⟨0⟩))
    (h : poolModifyTicksResult f evm id p = .ok f' post) :
    f'.locals.get? "state" = some (poolModifyTicksState evm id p) := by
  unfold poolModifyTicksResult at h
  split_ifs at h with hd
  · rw [poolModifyTicksState, if_pos hd]
    obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
    exact (poolModifyTickFinishResult_get hup "state" (by decide)
      (by intro upper; cases upper <;> decide) (by intro upper; cases upper <;> decide)).trans
      (poolModifyTwoTicksResult_state hlo)
  · cases h
    simpa only [poolModifyTicksState, if_neg hd] using hs

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV3.Pool.UpdatePositionClearTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionFinalFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  if a.delta < 0 then updatePositionClearDoneFrame v a evm true
  else updatePositionPositionFrame v a evm

def updatePositionFinalState (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : EVM.State :=
  if a.delta < 0 then updatePositionClearAfter v a evm true
  else updatePositionPositionState v a evm

def updatePositionTailMemory (mem : ByteArray) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) : ByteArray :=
  if a.delta < 0 then
    updatePositionClearMemory (updatePositionClearMemory mem v a evm false) v a evm true
  else mem

theorem updatePositionTailX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (updatePositionPositionState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨19527⟩ (updatePositionPositionWords v a evm ++ R)
      mem aw rdata σ k C) (ha : a.Fits) (hm : HeapMemory mem aw p) (hov : R.length + 18 ≤ 1024) :
    (ExecStmt config (updatePositionPositionFrame v a evm) (updatePositionPositionState v a evm)
      updatePositionFunction.body[12]! .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config (updatePositionPositionFrame v a evm) (updatePositionPositionState v a evm)
      updatePositionFunction.body[12]!
      (.ok (updatePositionFinalFrame v a evm) (updatePositionFinalState v a evm)) ∧
      ∃ σ' k' C', SourceState s0 ee σ' (updatePositionFinalState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨19573⟩ (updatePositionPositionWords v a evm ++ R)
        (updatePositionTailMemory mem v a evm) aw rdata σ' k' C' ∧
      HeapMemory (updatePositionTailMemory mem v a evm) aw p) := by
  obtain ⟨k1, C1, r1⟩ := updatePositionNegativeX (v := v) a evm rd ha (by omega)
  by_cases hn : a.delta < 0
  · rw [if_pos hn] at r1
    have hg : evalExpr? config (updatePositionPositionFrame v a evm)
        (updatePositionPositionState v a evm) (.binary .lt (.var "liquidityDelta") (.intLit 0)) =
        .ok (.bool true) := by rw [evalUpdatePositionNegative, decide_eq_true hn]
    rcases updatePositionClearX (v := v) a evm false hs r1 ha hm hov with
      ⟨hb, hr⟩ | ⟨hb0, σ2, k2, C2, hs2, r2, hm2⟩
    · exact Or.inl ⟨ExecStmt.iteTrue hg (ExecBlock.consStatic hb), hr⟩
    · rcases updatePositionClearX (v := v) a evm true hs2 r2 ha hm2 hov with
        ⟨hb, hr⟩ | ⟨hb1, σ3, k3, C3, hs3, r3, hm3⟩
      · exact Or.inl ⟨ExecStmt.iteTrue hg (ExecBlock.consNormal hb0 (ExecBlock.consStatic hb)), hr⟩
      · simp only [updatePositionFinalFrame, updatePositionFinalState, updatePositionTailMemory,
          if_pos hn]
        exact Or.inr ⟨ExecStmt.iteTrue hg (ExecBlock.consNormal hb0
          (ExecBlock.consNormal hb1 ExecBlock.nil)), σ3, k3, C3, hs3, r3, hm3⟩
  · rw [if_neg hn] at r1
    simp only [updatePositionFinalFrame, updatePositionFinalState, updatePositionTailMemory,
      if_neg hn]
    exact Or.inr ⟨ExecStmt.iteFalse (by rw [evalUpdatePositionNegative, decide_eq_false hn])
      ExecBlock.nil, σ, k1, C1, hs, r1, hm⟩

theorem updatePositionReturnSource (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) :
    ExecStmt config (updatePositionFinalFrame v a evm) evm' (.return [.var "position"])
      (.returned (updatePositionFinalFrame v a evm) evm' (some [updatePositionKeyValue a])) := by
  have hk : evalExpr? config (updatePositionFinalFrame v a evm) evm' (.var "position") =
      .ok (updatePositionKeyValue a) := by
    apply evalExpr_var_get
    unfold updatePositionFinalFrame
    split_ifs <;> update_position_clear_get
  exact ExecStmt.return (by simp only [evalExprs?, hk, bind, EvalResult.bind, pure])

end Benchmarks.UniswapV3.Pool

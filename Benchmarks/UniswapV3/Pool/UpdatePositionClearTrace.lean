import Benchmarks.UniswapV3.Pool.UpdatePositionClearModel
import Benchmarks.UniswapV3.Pool.UpdatePositionClearEntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionClearMemory (mem : ByteArray) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool) : ByteArray :=
  if updatePositionFlag v a evm upper then
    twoWordHashMem (EVM.wordOfInt (if upper then a.upper else a.lower)) ⟨5⟩ mem
  else mem

theorem updatePositionClearX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (hs : SourceState s0 ee σ (updatePositionClearBefore v a evm upper))
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionClearEntryPC upper)
      (updatePositionPositionWords v a evm ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hov : R.length + 18 ≤ 1024) :
    (ExecStmt config (updatePositionClearInputFrame v a evm upper)
      (updatePositionClearBefore v a evm upper) (updatePositionClearStmt upper) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config (updatePositionClearInputFrame v a evm upper)
      (updatePositionClearBefore v a evm upper) (updatePositionClearStmt upper)
      (.ok (updatePositionClearDoneFrame v a evm upper) (updatePositionClearAfter v a evm upper)) ∧
      ∃ σ' k' C', SourceState s0 ee σ' (updatePositionClearAfter v a evm upper) ∧
      RD (deployedRuntime v) ee g s0 (updatePositionClearReturnPC upper)
        (updatePositionPositionWords v a evm ++ R) (updatePositionClearMemory mem v a evm upper)
        aw rdata σ' k' C' ∧ HeapMemory (updatePositionClearMemory mem v a evm upper) aw p) := by
  obtain ⟨k1, C1, r1⟩ := updatePositionClearGuardX (v := v) a evm upper rd (by omega)
  cases hf : updatePositionFlag v a evm upper
  · simp only [hf, Bool.false_eq_true, if_false] at r1
    refine Or.inr ⟨?_, σ, k1, C1, ?_, ?_, ?_⟩
    · simp only [updatePositionClearDoneFrame, updatePositionClearAfter, hf,
        Bool.false_eq_true, if_false]
      exact ExecStmt.iteFalse (by rw [evalUpdatePositionClearGuard, hf]) ExecBlock.nil
    · simpa only [updatePositionClearAfter, hf, Bool.false_eq_true, if_false] using hs
    · simpa only [updatePositionClearMemory, hf, Bool.false_eq_true, if_false] using r1
    · simpa only [updatePositionClearMemory, hf, Bool.false_eq_true, if_false] using hm
  · simp only [hf, if_true] at r1
    obtain ⟨_, _, r2⟩ := updatePositionClearCallEntryX (v := v) a evm upper r1 (by omega)
    have ht : -(2 ^ 23 : Int) ≤ (if upper then a.upper else a.lower) ∧
        (if upper then a.upper else a.lower) < 2 ^ 23 := by
      cases upper
      · exact ha.1
      · exact ha.2.1
    rcases tickClearInternalX (v := v) (if upper then a.upper else a.lower)
      (updatePositionClearInputFrame v a evm upper) (updatePositionClearBefore v a evm upper)
      (updatePositionClearExprs upper) (if upper then "__c10" else "__c9")
      (updatePositionClearInputFrame_eq v a evm upper)
      (evalUpdatePositionClearExprs v a evm _ upper) hs r2 ht hm
      (by cases upper <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest)
      (by unfold updatePositionPositionWords; rw [updatePositionChangedWords_eq]
          change R.length + 12 + 6 ≤ 1024; omega) with
      ⟨hb, hr⟩ | ⟨hb, k3, C3, hs3, r3, hm3⟩
    · exact Or.inl ⟨ExecStmt.iteTrue (by rw [evalUpdatePositionClearGuard, hf])
        (ExecBlock.consStatic hb), hr⟩
    · refine Or.inr ⟨?_, tickClearMap σ ee (if upper then a.upper else a.lower),
        k3, C3, ?_, ?_, ?_⟩
      · simp only [updatePositionClearDoneFrame, updatePositionClearAfter, hf, if_true]
        exact ExecStmt.iteTrue (by rw [evalUpdatePositionClearGuard, hf])
          (ExecBlock.consNormal hb ExecBlock.nil)
      · simpa only [updatePositionClearAfter, hf, if_true] using hs3
      · simpa only [updatePositionClearMemory, hf, if_true] using r3
      · simpa only [updatePositionClearMemory, hf, if_true] using hm3

end Benchmarks.UniswapV3.Pool

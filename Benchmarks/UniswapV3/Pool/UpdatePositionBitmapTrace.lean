import Benchmarks.UniswapV3.Pool.UpdatePositionBitmapEntryTrace
import Benchmarks.UniswapV3.Pool.UpdatePositionBitmapSource
import Benchmarks.UniswapV3.Pool.BitmapFlipInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionBitmapMemory (mem : ByteArray) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool) : ByteArray :=
  if updatePositionFlipped v a evm upper then
    bitmapFlipMemory mem (if upper then a.upper else a.lower) (positionTick v.tickSpacing)
  else mem

theorem updatePositionBitmapX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (hs : SourceState s0 ee σ (updatePositionBitmapBefore v a evm upper))
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionBitmapEntryPC upper)
      (updatePositionBitmapEntryWords v a evm upper ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hov : R.length + 24 ≤ 1024) :
    (ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapStmt upper) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapStmt upper) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapStmt upper)
      (.ok (updatePositionBitmapDoneFrame v a evm upper) (updatePositionBitmapAfter v a evm upper)) ∧
      ∃ σ' k' C', SourceState s0 ee σ' (updatePositionBitmapAfter v a evm upper) ∧
      RD (deployedRuntime v) ee g s0 (updatePositionBitmapReturnPC upper)
        (updatePositionBitmapWords v a evm ++ R)
        (updatePositionBitmapMemory mem v a evm upper) aw rdata σ' k' C' ∧
      HeapMemory (updatePositionBitmapMemory mem v a evm upper) aw p) := by
  obtain ⟨k1, C1, r1⟩ := updatePositionBitmapGuardX (v := v) a evm upper rd (by omega)
  cases hf : updatePositionFlipped v a evm upper
  · simp only [hf, Bool.false_eq_true, if_false] at r1
    refine Or.inr (Or.inr ⟨updatePositionBitmapSkip v a evm upper hf, σ, k1, C1, ?_, ?_, ?_⟩)
    · simpa only [updatePositionBitmapAfter, hf, Bool.false_eq_true, if_false] using hs
    · simpa only [updatePositionBitmapMemory, hf, Bool.false_eq_true, if_false] using r1
    · simpa only [updatePositionBitmapMemory, hf, Bool.false_eq_true, if_false] using hm
  · simp only [hf, if_true] at r1
    obtain ⟨_, _, r2⟩ := updatePositionBitmapCallEntryX (v := v) a evm upper r1 (by omega)
    have ht : -(2 ^ 23 : Int) ≤ (if upper then a.upper else a.lower) ∧
        (if upper then a.upper else a.lower) < 2 ^ 23 := by
      cases upper
      · exact ha.1
      · exact ha.2.1
    have hsp : -(2 ^ 23 : Int) ≤ positionTick v.tickSpacing ∧
        positionTick v.tickSpacing < 2 ^ 23 := normalizeSint_bounds ⟨24, by decide⟩ _
    rcases bitmapFlipInternalX (v := v) (if upper then a.upper else a.lower)
      (positionTick v.tickSpacing) (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapExprs upper)
      (if upper then "__c6" else "__c5") (updatePositionBitmapInputFrame_eq v a evm upper)
      (evalUpdatePositionBitmapExprs v a evm _ upper) hs r2 ht hsp
      (positionTickWord_eq v.tickSpacing) hm
      (by cases upper <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest)
      (by change R.length + 13 + 11 ≤ 1024; omega) with
      ⟨hb, hr⟩ | ⟨hb, hr⟩ | ⟨hb, k3, C3, hs3, r3, hm3⟩
    · exact Or.inl ⟨updatePositionBitmapReverts v a evm upper hf hb, hr⟩
    · exact Or.inr (Or.inl ⟨updatePositionBitmapStatic v a evm upper hf hb, hr⟩)
    · refine Or.inr (Or.inr ⟨updatePositionBitmapSuccess v a evm upper hf hb,
        bitmapFlippedMap σ ee
          (bitmapWordPos ((if upper then a.upper else a.lower).tdiv (positionTick v.tickSpacing)))
          (bitmapFlipMask (if upper then a.upper else a.lower) (positionTick v.tickSpacing)),
        k3, C3, ?_, ?_, ?_⟩)
      · simpa only [updatePositionBitmapAfter, updatePositionBitmapApply, hf, if_true] using hs3
      · simpa only [updatePositionBitmapMemory, hf, if_true] using r3
      · simpa only [updatePositionBitmapMemory, hf, if_true] using hm3

end Benchmarks.UniswapV3.Pool

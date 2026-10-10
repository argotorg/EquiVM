import Benchmarks.UniswapV3.Pool.UpdatePositionPositionSource
import Benchmarks.UniswapV3.Pool.UpdatePositionFeeTrace
import Benchmarks.UniswapV3.Pool.PositionUpdateInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionPositionMemory (mem : ByteArray) (p : UInt256) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) : ByteArray :=
  wordArrayAllocMem mem p (positionSnapshotWords (updatePositionKey a)
    (updatePositionChangedState v a evm).accountMap (updatePositionChangedState v a evm).executionEnv)

theorem updatePositionPositionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (updatePositionChangedState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨19510⟩
      (updatePositionInside v a evm true :: updatePositionInside v a evm false ::
        ⟨0⟩ :: ⟨0⟩ :: updatePositionChangedWords v a evm ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 160 ≤ 2 ^ 200)
    (hov : R.length + 37 ≤ 1024) :
    (ExecStmt config (updatePositionFee1Frame v a evm) (updatePositionChangedState v a evm)
      (.internalCall "Position_update" updatePositionPositionExprs "__c8") .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config (updatePositionFee1Frame v a evm) (updatePositionChangedState v a evm)
      (.internalCall "Position_update" updatePositionPositionExprs "__c8") .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config (updatePositionFee1Frame v a evm) (updatePositionChangedState v a evm)
      (.internalCall "Position_update" updatePositionPositionExprs "__c8")
      (.ok (updatePositionPositionFrame v a evm) (updatePositionPositionState v a evm)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (updatePositionPositionState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨19527⟩ (updatePositionPositionWords v a evm ++ R)
        (updatePositionPositionMemory mem p v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (updatePositionPositionMemory mem p v a evm) aw' (p + ⟨160⟩)) := by
  obtain ⟨_, _, r1⟩ := updatePositionPositionEntryX (v := v) a evm rd (by omega)
  rcases positionUpdateInternalX (v := v) (updatePositionPositionArgs v a evm)
    (updatePositionFee1Frame v a evm) (updatePositionChangedState v a evm)
    updatePositionPositionExprs "__c8" (updatePositionFee1Frame_eq v a evm)
    (evalUpdatePositionPositionExprs v a evm _) hs r1 ha.2.2.1 hm hb
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by rw [updatePositionChangedWords_eq]; change R.length + 12 + 25 ≤ 1024; omega) with
    ⟨hs', hr⟩ | ⟨hs', hr⟩ | ⟨hsrc, σ', aw', k', C', hs', r', hm'⟩
  · exact Or.inl ⟨hs', hr⟩
  · exact Or.inr (Or.inl ⟨hs', hr⟩)
  · refine Or.inr (Or.inr ⟨hsrc, σ', aw', k', C', hs', ?_, ?_⟩)
    · simpa only [updatePositionPositionWords, List.cons_append, updatePositionPositionMemory,
        updatePositionPositionArgs, hs.accounts, hs.env] using r'
    · simpa only [updatePositionPositionMemory, updatePositionPositionArgs,
        hs.accounts, hs.env] using hm'

end Benchmarks.UniswapV3.Pool

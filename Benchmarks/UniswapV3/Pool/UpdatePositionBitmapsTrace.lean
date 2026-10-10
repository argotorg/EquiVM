import Benchmarks.UniswapV3.Pool.UpdatePositionBitmapTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionBitmapsBody : List Stmt :=
  [updatePositionBitmapStmt false, updatePositionBitmapStmt true]

def updatePositionBitmapsMemory (mem : ByteArray) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) : ByteArray :=
  updatePositionBitmapMemory (updatePositionBitmapMemory mem v a evm false) v a evm true

def updatePositionUpdatedWords (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : List UInt256 := (updatePositionBitmapWords v a evm).drop 3

theorem updatePositionBitmapsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (updatePositionTickAfter v a evm true))
    (rd : RD (deployedRuntime v) ee g s0 ⟨19386⟩
      ((updatePositionFlipped v a evm true).toUInt256 ::
        updatePositionTickSavedWords v a evm true ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hov : R.length + 24 ≤ 1024) :
    (ExecBlock config (updatePositionUpperFrame v a evm) (updatePositionTickAfter v a evm true)
      updatePositionBitmapsBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config (updatePositionUpperFrame v a evm) (updatePositionTickAfter v a evm true)
      updatePositionBitmapsBody .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (ExecBlock config (updatePositionUpperFrame v a evm) (updatePositionTickAfter v a evm true)
      updatePositionBitmapsBody
      (.ok (updatePositionBitmapDoneFrame v a evm true) (updatePositionBitmapAfter v a evm true)) ∧
      ∃ σ' k' C', SourceState s0 ee σ' (updatePositionBitmapAfter v a evm true) ∧
      RD (deployedRuntime v) ee g s0 ⟨19492⟩ (updatePositionUpdatedWords v a evm ++ R)
        (updatePositionBitmapsMemory mem v a evm) aw rdata σ' k' C' ∧
      HeapMemory (updatePositionBitmapsMemory mem v a evm) aw p) := by
  rcases updatePositionBitmapX (v := v) a evm false hs rd ha hm hov with
    ⟨hb, hr⟩ | ⟨hb, hr⟩ | ⟨hb0, σ1, k1, C1, hs1, r1, hm1⟩
  · exact Or.inl ⟨ExecBlock.consRevert hb, hr⟩
  · exact Or.inr (Or.inl ⟨ExecBlock.consStatic hb, hr⟩)
  · rcases updatePositionBitmapX (v := v) a evm true hs1 r1 ha hm1 hov with
      ⟨hb, hr⟩ | ⟨hb, hr⟩ | ⟨hb1, σ2, k2, C2, hs2, r2, hm2⟩
    · exact Or.inl ⟨ExecBlock.consNormal hb0 (ExecBlock.consRevert hb), hr⟩
    · exact Or.inr (Or.inl ⟨ExecBlock.consNormal hb0 (ExecBlock.consStatic hb), hr⟩)
    · have r3 := uniswapV3Pool_block_19488 (immWords := wordsOf (immStore v))
        (by change R.length + 10 + 3 ≤ 1024; omega) r2
      refine Or.inr (Or.inr ⟨ExecBlock.consNormal hb0 (ExecBlock.consNormal hb1 ExecBlock.nil),
        σ2, k2 + 4, C2 + 7, hs2, ?_, hm2⟩)
      exact r3

end Benchmarks.UniswapV3.Pool

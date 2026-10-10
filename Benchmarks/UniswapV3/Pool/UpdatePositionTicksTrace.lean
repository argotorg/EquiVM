import Benchmarks.UniswapV3.Pool.UpdatePositionTickTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionTicksBody : List Stmt := updatePositionTickBody false ++ updatePositionTickBody true

def updatePositionTicksMemory (mem : ByteArray) (a : UpdatePositionArgs) : ByteArray :=
  twoWordHashMem (EVM.wordOfInt a.upper) ⟨5⟩ (twoWordHashMem (EVM.wordOfInt a.lower) ⟨5⟩ mem)

theorem updatePositionTicksX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19273⟩
      (updatePositionTickEntryWords v a evm false ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hov : R.length + 38 ≤ 1024) :
    (ExecBlock config (updatePositionOracleFrame (immStore v) a evm) evm
      updatePositionTicksBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config (updatePositionOracleFrame (immStore v) a evm) evm
      updatePositionTicksBody .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (ExecBlock config (updatePositionOracleFrame (immStore v) a evm) evm updatePositionTicksBody
      (.ok (updatePositionUpperFrame v a evm) (updatePositionTickAfter v a evm true)) ∧
      ∃ σ' k' C', SourceState s0 ee σ' (updatePositionTickAfter v a evm true) ∧
      RD (deployedRuntime v) ee g s0 ⟨19386⟩
        ((updatePositionFlipped v a evm true).toUInt256 ::
          updatePositionTickSavedWords v a evm true ++ R)
        (updatePositionTicksMemory mem a) aw rdata σ' k' C' ∧
      HeapMemory (updatePositionTicksMemory mem a) aw p) := by
  rcases updatePositionTickX (v := v) a evm false hs rd ha hm hov with
    ⟨hb, hr⟩ | ⟨hb, hr⟩ | ⟨hb0, σ1, k1, C1, hs1, r1⟩
  · exact Or.inl ⟨execBlock_append_term hb (by intro _ _ h; cases h), hr⟩
  · exact Or.inr (Or.inl ⟨execBlock_append_term hb (by intro _ _ h; cases h), hr⟩)
  · have hm1 := HeapMemory.twoWordHash hm (EVM.wordOfInt a.lower) ⟨5⟩
    rcases updatePositionTickX (v := v) a evm true hs1 r1 ha hm1 hov with
      ⟨hb, hr⟩ | ⟨hb, hr⟩ | ⟨hb1, σ2, k2, C2, hs2, r2⟩
    · exact Or.inl ⟨execBlock_append_ok hb0 hb, hr⟩
    · exact Or.inr (Or.inl ⟨execBlock_append_ok hb0 hb, hr⟩)
    · exact Or.inr (Or.inr ⟨execBlock_append_ok hb0 hb1, σ2, k2, C2, hs2, r2,
        HeapMemory.twoWordHash hm1 (EVM.wordOfInt a.upper) ⟨5⟩⟩)

end Benchmarks.UniswapV3.Pool

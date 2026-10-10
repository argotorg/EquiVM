import Benchmarks.UniswapV3.Pool.UpdatePositionTickEntryTrace
import Benchmarks.UniswapV3.Pool.UpdatePositionTickSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem updatePositionTickX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (hs : SourceState s0 ee σ (updatePositionTickBefore v a evm upper))
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionTickEntryPC upper)
      (updatePositionTickEntryWords v a evm upper ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hov : R.length + 38 ≤ 1024) :
    (ExecBlock config (updatePositionTickInputFrame v a evm upper)
      (updatePositionTickBefore v a evm upper) (updatePositionTickBody upper) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config (updatePositionTickInputFrame v a evm upper)
      (updatePositionTickBefore v a evm upper) (updatePositionTickBody upper) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecBlock config (updatePositionTickInputFrame v a evm upper)
      (updatePositionTickBefore v a evm upper) (updatePositionTickBody upper)
      (.ok (updatePositionTickDoneFrame v a evm upper) (updatePositionTickAfter v a evm upper)) ∧
      ∃ σ' k' C', SourceState s0 ee σ' (updatePositionTickAfter v a evm upper) ∧
      RD (deployedRuntime v) ee g s0 (updatePositionTickReturnPC upper)
        ((updatePositionFlipped v a evm upper).toUInt256 ::
          updatePositionTickSavedWords v a evm upper ++ R)
        (twoWordHashMem (EVM.wordOfInt (if upper then a.upper else a.lower)) ⟨5⟩ mem)
        aw rdata σ' k' C') := by
  obtain ⟨_, _, r1⟩ := updatePositionTickEntryX (v := v) a evm upper rd (by omega)
  have hc := tickUpdateMaskedX (v := v) (updatePositionTickArgs v a evm upper)
    (updatePositionTickBefore v a evm upper) (UInt256.ofNat evm.executionEnv.header.timestamp)
    v.maxLiquidityPerTick hs r1 (updatePositionTickArgs_fits v a evm upper ha) rfl rfl hm
    (by cases upper <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest)
    (by change R.length + 13 + 25 ≤ 1024; omega)
  rcases hc with ⟨hr, hv⟩ | ⟨hv, hc⟩
  · exact Or.inl ⟨ExecBlock.consRevert (updatePositionTickCallReverts v a evm upper
      (tickUpdateLiquidityReverts (immStore v) _ _ hv)), hr⟩
  · rcases hc with ⟨hr, hmax⟩ | ⟨hmax, hc⟩
    · exact Or.inl ⟨ExecBlock.consRevert (updatePositionTickCallReverts v a evm upper
        (tickUpdateMaxReverts (immStore v) _ _ hv hmax)), hr⟩
    · rcases hc with ⟨hr, hp⟩ | ⟨_, hc⟩
      · exact Or.inr (Or.inl ⟨ExecBlock.consStatic (updatePositionTickCallStatic v a evm upper
          (tickUpdateStatic (immStore v) _ _ hv hmax (by rw [hs.env]; exact hp))), hr⟩)
      · rcases hc with ⟨hr, hn⟩ | ⟨hn, σ', k', C', hs', r'⟩
        · exact Or.inl ⟨ExecBlock.consRevert (updatePositionTickCallReverts v a evm upper
            (tickUpdateNetReverts (immStore v) _ _ ha.2.2.1.1 ha.2.2.1.2 hv hmax hn)), hr⟩
        · exact Or.inr (Or.inr ⟨updatePositionTickSource v a evm upper ha hv hmax hn,
            σ', k', C', hs', r'⟩)

end Benchmarks.UniswapV3.Pool

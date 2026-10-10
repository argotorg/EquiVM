import Benchmarks.UniswapV3.Pool.TickUpdateNetMathTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (tickUpdateGrossState a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨21236⟩
      (EVM.wordOfInt (tickUpdateNetResult a evm a.upper) ::
        tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k C)
    (hn : safeCast128Valid (tickUpdateNetResult a evm a.upper)) (hp : ee.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 21 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (tickUpdateFinalState a evm) ∧
      RD (deployedRuntime v) ee g s0 ret ((tickUpdateFlipped a evm).toUInt256 :: R)
        mem aw rdata σ' k' C' := by
  have hcast : UInt256.signextend (UInt256.ofNat 15)
      (EVM.wordOfInt (tickUpdateNetResult a evm a.upper)) =
      EVM.wordOfInt (tickUpdateNetResult a evm a.upper) := by
    rw [signextend_wordOfInt ⟨128, by decide⟩ _ _ (by decide) (by decide), hn]
  obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21236 (immWords := wordsOf (immStore v))
    hov hp hret rd
  have hs' := SourceState.tickLiquidity hs a.tick true
    (EVM.wordOfInt (tickUpdateNetResult a evm a.upper))
  refine ⟨_, kf, Cf, hs', ?_⟩
  simpa only [uniswapV3Pool_block_21236_stack, hcast, solcMask128, solcShift128,
    tickLiquidityMap, protocolFeeUpdateWord, if_true, uint128Word, u256_land_comm, u256_mul_comm]
    using rf

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.PoolLiquidityStore
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_053

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem poolLiquidityStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw value old : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16721⟩ (value :: old :: R) mem aw rdata σ k C)
    (hperm : ee.perm = true) (hov : R.length + 7 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (storePoolLiquidity evm value) ∧
      RD (deployedRuntime v) ee g s0 ⟨16801⟩ R mem aw rdata σ' k' C' := by
  have hs' := hs.readModifyWrite ⟨4⟩ (fun word ↦ protocolFeeUpdateWord false word value)
  obtain ⟨k', C', rr⟩ := uniswapV3Pool_block_16721 (immWords := wordsOf (immStore v)) hov hperm
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16721_stack, solcMask128] at rr
  simp only [protocolFeeUpdateWord, Bool.false_eq_true, if_false, uint128Word,
    u256_land_comm (solcSlotWord σ ee ⟨4⟩)] at hs'
  exact ⟨_, _, _, hs', rr⟩

end Benchmarks.UniswapV3.Pool

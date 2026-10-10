import Benchmarks.UniswapV3.Pool.BitmapPositionWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem bitmapPositionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨17590⟩
      (EVM.wordOfInt tick :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (bitmapPositionBitRaw tick :: EVM.wordOfInt (bitmapWordPos tick) :: R)
      mem aw rdata σ k' C' := by
  have rn := uniswapV3Pool_block_17590 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  have rm := RD.smod rn
    (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
      (⟨17605⟩ : UInt256), UInt8.ofNat 7, .SMOD, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rout := uniswapV3Pool_block_17606 (immWords := wordsOf (immStore v))
    (by evm_ov) hret rm
  simp only [uniswapV3Pool_block_17606_stack, bitmapPositionBitRemainder,
    bitmapPositionWordShift] at rout
  exact ⟨_, _, rout⟩

end Benchmarks.UniswapV3.Pool

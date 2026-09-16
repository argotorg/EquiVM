import Examples.UniswapV2Pair.MintInternalMintRuntime
import Examples.UniswapV2Pair.Invalid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000


set_option maxHeartbeats 1000000 in
theorem RD.uniswapMintProportionalMul0Entry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 : UInt256}
    (rd3762 : RD uniswapV2PairBytecode ee g s0 ⟨3762⟩
      (totalSupply :: feeOn :: amount1 :: amount0 :: balance1 :: balance0 ::
        reserve1 :: reserve0 :: R) mem aw rdata acc k C)
    (hclean : UInt256.land reserve0 reserve112Mask = reserve0)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨6780⟩
      (totalSupply :: amount0 :: ⟨3791⟩ :: reserve0 :: ⟨3838⟩ :: totalSupply ::
        feeOn :: amount1 :: amount0 :: balance1 :: balance0 :: reserve1 :: reserve0 :: R)
      mem aw rdata acc k' C' := by
  have rd := evm_run rd3762 with [
    jumpdest, push2 ⟨3838⟩, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub,
    dup10, and, push2 ⟨3791⟩, dup7, dup5, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from rfl, hclean,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide] at rd
  exact ⟨_, _, rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapMintProportionalMul1Entry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 : UInt256}
    {liquidity0 : UInt256}
    (rd3800 : RD uniswapV2PairBytecode ee g s0 ⟨3800⟩
      (liquidity0 :: ⟨3838⟩ :: totalSupply :: feeOn :: amount1 :: amount0 ::
        balance1 :: balance0 :: reserve1 :: reserve0 :: R) mem aw rdata acc k C)
    (hclean : UInt256.land reserve1 reserve112Mask = reserve1)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨6780⟩
      (totalSupply :: amount1 :: ⟨3825⟩ :: reserve1 :: liquidity0 :: ⟨3838⟩ ::
        totalSupply :: feeOn :: amount1 :: amount0 :: balance1 :: balance0 ::
        reserve1 :: reserve0 :: R) mem aw rdata acc k' C' := by
  have rd := evm_run rd3800 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup10, and,
    push2 ⟨3825⟩, dup7, dup6, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from rfl, hclean,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide] at rd
  exact ⟨_, _, rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩


set_option maxHeartbeats 1000000 in
theorem RD.uniswapMintProportionalDiv0Guard
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {product reserve : UInt256}
    (rd : RD uniswapV2PairBytecode ee g s0 ⟨3791⟩
      (product :: reserve :: R) mem aw rdata acc k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨3796⟩
      (⟨3798⟩ :: reserve :: product :: reserve :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, dup2, push2 ⟨3798⟩]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapMintProportionalDiv1Guard
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {product reserve : UInt256}
    (rd : RD uniswapV2PairBytecode ee g s0 ⟨3825⟩
      (product :: reserve :: R) mem aw rdata acc k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨3830⟩
      (⟨3832⟩ :: reserve :: product :: reserve :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, dup2, push2 ⟨3832⟩]⟩

end UniswapV2Pair

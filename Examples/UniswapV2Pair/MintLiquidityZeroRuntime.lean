import Examples.UniswapV2Pair.MintRuntimeAfterFee
import Examples.UniswapV2Pair.ErrorStringCopyRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 5000000 in
theorem uniswapMintRuntimeLiquidityZeroReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3841 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hliqZero : liquidity = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hgt : UInt256.gt liquidity (⟨0⟩ : UInt256) = ⟨0⟩ := by
    rw [hliqZero]
    decide
  have rd3849pre := evm_run rd3841 with [
    jumpdest, push1 ⟨0⟩, dup10, gt, push2 ⟨3904⟩]
  rw [hgt] at rd3849pre
  have rd3850 := evm_run rd3849pre with [jumpiNT (by decide)]
  exact RD.solcErrorString40CopyReverts (source := ⟨8741⟩) rd3850
    (by constructor <;> native_decide) (by native_decide) hmem hmem64 (by evm_ov)

end UniswapV2Pair

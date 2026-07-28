import Examples.UniswapV2Pair.MintRuntimeAfterFee

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
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (aw := feeToStaticcallActiveWords)
      (by rw [hmem]; decide) (by native_decide) hmem64
  have rd3853 := evm_run rd3850 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov)]
  have rd3860 := rd3853.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  let mem0 : ByteArray := (UInt256.toByteArray solcErrorStringSelector).write 0 mem 128 32
  have hmem0 : mem0.size = 164 := by
    unfold mem0
    exact toByteArray_write32_size_of_le mem solcErrorStringSelector 128 164 164 hmem
      (by rw [hmem]; omega) (by decide)
  have rd3862 := evm_run rd3860 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 mem0 feeToStaticcallActiveWords (by native_decide)
      mem_cost (by unfold mem0 solcErrorStringSelector; rfl) (by native_decide) (by evm_ov)]
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 132 32
  have hmem1 : mem1.size = 164 := by
    unfold mem1
    exact toByteArray_write32_size_of_le mem0 (⟨32⟩ : UInt256) 132 164 164 hmem0
      (by rw [hmem0]; omega) (by decide)
  have rd3875pre := evm_run rd3862 with [
    push1 ⟨4⟩, add, dup1, dup1, push1 ⟨32⟩, add, dup3, dup2, sub, dup3,
    raw mstore 0 mem1 feeToStaticcallActiveWords (by native_decide)
      mem_cost (by unfold mem1; rfl) (by native_decide) (by evm_ov)]
  let mem2 : ByteArray := (UInt256.toByteArray (⟨40⟩ : UInt256)).write 0 mem1 164 32
  have hmem2 : mem2.size = 196 := by
    unfold mem2
    exact toByteArray_write32_size_of_le mem1 (⟨40⟩ : UInt256) 164 164 196 hmem1
      (by rw [hmem1]) (by decide)
  have rd3882 := evm_run rd3875pre with [
    push1 ⟨40⟩, dup2,
    raw mstore 3 mem2 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by unfold mem2; rfl) (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, dup1]
  have rd3886 := evm_run rd3882 with [push2 ⟨8741⟩]
  let mem3 : ByteArray := uniswapV2PairBytecode.write 8741 mem2 196 40
  have hmem3 : mem3.size = 236 := by
    unfold mem3
    simpa [hmem2] using
      write_end_size_from uniswapV2PairBytecode mem2 8741 40 (by decide) (by native_decide)
  have hread64_mem0 : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold mem0
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
    exact hmem64
  have hread64_mem1 : mem1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold mem1
    rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [hmem0]; omega) (by omega)]
    exact hread64_mem0
  have hread64_mem2 : mem2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold mem2
    rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size]) (by rw [hmem1])
      (by omega)]
    exact hread64_mem1
  have hread64_mem3 : mem3.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold mem3
    simpa [hmem2] using
      (write_read_below_end_from uniswapV2PairBytecode mem2 8741 40 64
        (by decide) (by native_decide) (by rw [hmem2]; omega)).trans hread64_mem2
  have hmload64_mem3 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem3.size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 8) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadWordValue_of_readWithPadding (by rw [hmem3]; decide) (by native_decide)
      hread64_mem3
  have rd3890 := evm_run rd3886 with [
    push1 ⟨40⟩, swap2,
    raw codecopy 3 mem3 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by unfold mem3; rfl) (by native_decide) (by evm_ov)]
  exact evm_run rd3890 with [
    push1 ⟨64⟩, add, swap2, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64_mem3 (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 3 (by native_decide) mem_cost (by evm_ov)]

end UniswapV2Pair

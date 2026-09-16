import Examples.UniswapV2Pair.MintLiquidityFinalizeRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only proportional-liquidity branch from pc3762 through the fee-off final return. -/
theorem uniswapMintRuntimeProportionalLiquidityUpdateElapsedZeroFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner σPacked ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0
      hmulFit1 hreserve0Nonzero hreserve1Nonzero
  exact uniswapMintRuntimeLiquidityMintUpdateElapsedZeroFeeOffReturns
    (liquidity := liquidity)
    (by simpa [hliquidity] using rd3841)
    hliqNonzero hperm htotalFit hbalanceFit hfit0 hfit1 helapsed0 hfeeOff hmem hmem64

set_option maxHeartbeats 1000000 in
/- Runtime-only proportional-liquidity branch from pc3762 through the fee-on final return. -/
theorem uniswapMintRuntimeProportionalLiquidityUpdateElapsedZeroFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σPacked ⟨11⟩
          (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
              reserve112Mask))) ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0
      hmulFit1 hreserve0Nonzero hreserve1Nonzero
  exact uniswapMintRuntimeLiquidityMintUpdateElapsedZeroFeeOnReturns
    (liquidity := liquidity)
    (by simpa [hliquidity] using rd3841)
    hliqNonzero hperm htotalFit hbalanceFit hfit0 hfit1 helapsed0 hfeeOn
    hfitKLast hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintRuntimeAfterMintFeeProportionalUpdateFirstBoundReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfail0 : reserve112Mask.toNat < balance0.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotal htotalNonzero
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0
      hmulFit1 hreserve0Nonzero hreserve1Nonzero
  let mintMem := uniswapInternalMintLogMem liquidity
    (uniswapInternalMintBalanceHashMem toWord
      (uniswapInternalMintBalanceHashMem toWord mem))
  obtain ⟨_, _, rd3914⟩ :=
    uniswapMintRuntimeLiquidityMintReturn
      (by simpa [hliquidity] using rd3841)
      hliqNonzero hperm htotalFit hbalanceFit
      (uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 toWord
        (by rw [hmem]; omega) hmem64)
      (uniswapInternalMintSuccessMem_mload64_of_ge160 toWord liquidity
        (by rw [hmem]; omega) hmem64)
  have hmintMemSize : mintMem.size = 164 := by
    simpa [mintMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega)
  have hmintMem64 : mintMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mintMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega) hmem64
  obtain ⟨_, _, rd6959⟩ := uniswapMintRuntimeUpdateEntry
    (by simpa [mintMem] using rd3914)
  exact RD.uniswapUpdateOverflowGuardFirstReverts
    (by simpa [feeToStaticcallActiveWords] using rd6959)
    hfail0 hmintMemSize hmintMem64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintRuntimeAfterMintFeeProportionalUpdateSecondBoundReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfail1 : reserve112Mask.toNat < balance1.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotal htotalNonzero
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0
      hmulFit1 hreserve0Nonzero hreserve1Nonzero
  let mintMem := uniswapInternalMintLogMem liquidity
    (uniswapInternalMintBalanceHashMem toWord
      (uniswapInternalMintBalanceHashMem toWord mem))
  obtain ⟨_, _, rd3914⟩ :=
    uniswapMintRuntimeLiquidityMintReturn
      (by simpa [hliquidity] using rd3841)
      hliqNonzero hperm htotalFit hbalanceFit
      (uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 toWord
        (by rw [hmem]; omega) hmem64)
      (uniswapInternalMintSuccessMem_mload64_of_ge160 toWord liquidity
        (by rw [hmem]; omega) hmem64)
  have hmintMemSize : mintMem.size = 164 := by
    simpa [mintMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega)
  have hmintMem64 : mintMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mintMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega) hmem64
  obtain ⟨_, _, rd6959⟩ := uniswapMintRuntimeUpdateEntry
    (by simpa [mintMem] using rd3914)
  exact RD.uniswapUpdateOverflowGuardSecondReverts
    (by simpa [feeToStaticcallActiveWords] using rd6959)
    hfit0 hfail1 hmintMemSize hmintMem64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only post-`_mintFee` proportional-liquidity path through the fee-off final return. -/
theorem uniswapMintRuntimeAfterMintFeeProportionalFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner σPacked ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotal htotalNonzero
  exact uniswapMintRuntimeProportionalLiquidityUpdateElapsedZeroFeeOffReturns
    (liquidity := liquidity) rd3762 hclean0 hclean1 hmulFit0 hmulFit1
    hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm htotalFit
    hbalanceFit hfit0 hfit1 helapsed0 hfeeOff hmem hmem64

set_option maxHeartbeats 1000000 in
/- Runtime-only post-`_mintFee` proportional-liquidity path through the cumulative `_update`,
fee-off handling, final `Mint`, unlock, and ABI return. -/
theorem uniswapMintRuntimeAfterMintFeeProportionalUpdateCumulativeFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsedNe :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask ≠ ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, uniswapUpdateCumulativeReturnMapWith
        σAfterMint I balance0 balance1 reserve0 reserve1)
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotal htotalNonzero
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0
      hmulFit1 hreserve0Nonzero hreserve1Nonzero
  let mintMem := uniswapInternalMintLogMem liquidity
    (uniswapInternalMintBalanceHashMem toWord
      (uniswapInternalMintBalanceHashMem toWord mem))
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord
        (uniswapInternalMintBalanceHashMem toWord mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
  obtain ⟨_, _, rd3914⟩ :=
    uniswapMintRuntimeLiquidityMintReturn
      (by simpa [hliquidity] using rd3841)
      hliqNonzero hperm htotalFit hbalanceFit
      (uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 toWord
        (by rw [hmem]; omega) hmem64)
      (uniswapInternalMintSuccessMem_mload64_of_ge160 toWord liquidity
        (by rw [hmem]; omega) hmem64)
  have hmintMemSize : mintMem.size = 164 := by
    simpa [mintMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega)
  have hmintMem64 : mintMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mintMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega) hmem64
  exact uniswapMintRuntimeAfterInternalMintUpdateCumulativeFeeOffReturns
    (σMint := σAfterMint) (mem := mintMem) (liquidity := liquidity)
    (by simpa [σAfterMint, mintMem] using rd3914)
    hfit0 hfit1
    (by simpa [σAfterMint] using helapsedNe)
    (by rwa [hclean0])
    (by rwa [hclean1])
    hfeeOff
    (by rw [hmintMemSize]; omega)
    (by rw [hmintMemSize]; omega)
    hmintMem64 hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only post-`_mintFee` proportional-liquidity path through the cumulative `_update`
path, fee-on `kLast` update, final `Mint`, unlock, and ABI return. -/
theorem uniswapMintRuntimeAfterMintFeeProportionalUpdateCumulativeFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsedNe :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask ≠ ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      (UInt256.land
            (uniswapSlotWord ⟨8⟩
              (uniswapUpdateCumulativePackedMapWith
                σAfterMint I balance0 balance1 reserve0 reserve1) I)
            reserve112Mask).toNat *
          (UInt256.land
            (UInt256.div
              (uniswapSlotWord ⟨8⟩
                (uniswapUpdateCumulativePackedMapWith
                  σAfterMint I balance0 balance1 reserve0 reserve1) I)
              reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (uniswapUpdateCumulativePackedMapWith
            σAfterMint I balance0 balance1 reserve0 reserve1) ⟨11⟩
          (UInt256.mul
            (UInt256.land
              (uniswapSlotWord ⟨8⟩
                (uniswapUpdateCumulativePackedMapWith
                  σAfterMint I balance0 balance1 reserve0 reserve1) I)
              reserve112Mask)
            (UInt256.land
              (UInt256.div
                (uniswapSlotWord ⟨8⟩
                  (uniswapUpdateCumulativePackedMapWith
                    σAfterMint I balance0 balance1 reserve0 reserve1) I)
                reserve112Shift)
              reserve112Mask))) ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotal htotalNonzero
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0
      hmulFit1 hreserve0Nonzero hreserve1Nonzero
  let mintMem := uniswapInternalMintLogMem liquidity
    (uniswapInternalMintBalanceHashMem toWord
      (uniswapInternalMintBalanceHashMem toWord mem))
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord
        (uniswapInternalMintBalanceHashMem toWord mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
  obtain ⟨_, _, rd3914⟩ :=
    uniswapMintRuntimeLiquidityMintReturn
      (by simpa [hliquidity] using rd3841)
      hliqNonzero hperm htotalFit hbalanceFit
      (uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 toWord
        (by rw [hmem]; omega) hmem64)
      (uniswapInternalMintSuccessMem_mload64_of_ge160 toWord liquidity
        (by rw [hmem]; omega) hmem64)
  have hmintMemSize : mintMem.size = 164 := by
    simpa [mintMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega)
  have hmintMem64 : mintMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mintMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 toWord liquidity
        (mem := mem) (by rw [hmem]; omega) hmem64
  exact uniswapMintRuntimeAfterInternalMintUpdateCumulativeFeeOnReturns
    (σMint := σAfterMint) (mem := mintMem) (liquidity := liquidity)
    (by simpa [σAfterMint, mintMem] using rd3914)
    hfit0 hfit1
    (by simpa [σAfterMint] using helapsedNe)
    (by rwa [hclean0])
    (by rwa [hclean1])
    hfeeOn
    (by simpa [σAfterMint] using hfitKLast)
    (by rw [hmintMemSize]; omega)
    (by rw [hmintMemSize]; omega)
    hmintMem64 hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only post-`_mintFee` proportional-liquidity path through the fee-on final return. -/
theorem uniswapMintRuntimeAfterMintFeeProportionalFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σPacked ⟨11⟩
          (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
              reserve112Mask))) ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotal htotalNonzero
  exact uniswapMintRuntimeProportionalLiquidityUpdateElapsedZeroFeeOnReturns
    (liquidity := liquidity) rd3762 hclean0 hclean1 hmulFit0 hmulFit1
    hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm htotalFit
    hbalanceFit hfit0 hfit1 helapsed0 hfeeOn hfitKLast hmem hmem64

set_option maxHeartbeats 1000000 in
/- Runtime-only post-`_mintFee` initial-liquidity path: zero total supply and a small sqrt
result must revert when subtracting `MINIMUM_LIQUIDITY`. -/
theorem uniswapMintRuntimeAfterMintFeeInitialSmallRootReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hsmall : (UInt256.mul amount0 amount1).toNat ≤ 3)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd3713⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyZero rd3701 htotalZero
  exact uniswapMintRuntimeInitialLiquiditySmallRootReverts rd3713 hfit hsmall hmem hmem64

set_option maxHeartbeats 1000000 in
/- Runtime-only post-`_mintFee` initial-liquidity path: zero total supply and a large sqrt
argument enter the sqrt loop. -/
theorem uniswapMintRuntimeAfterMintFeeInitialLargeRootLoopEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hlarge : 3 < (UInt256.mul amount0 amount1).toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [UInt256.div (UInt256.mul amount0 amount1) ⟨2⟩ + ⟨1⟩,
        UInt256.mul amount0 amount1, UInt256.mul amount0 amount1, ⟨2531⟩, ⟨1000⟩,
        ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd3713⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyZero rd3701 htotalZero
  exact uniswapMintRuntimeInitialLiquidityLargeRootLoopEntry rd3713 hfit hlarge

end UniswapV2Pair

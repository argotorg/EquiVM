import Examples.UniswapV2Pair.MintRuntimeAfterFee
import Examples.UniswapV2Pair.SyncCumulative

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintSyncLogMem_size_192_of_160
    (packed : UInt256) {mem : ByteArray} (hmem : mem.size = 160) :
    (uniswapSyncLogMem packed mem).size = 192 := by
  unfold uniswapSyncLogMem uniswapSyncLogReserve0Mem
  have hreserve0 :
      ((UInt256.toByteArray (uniswapSyncReserve0Word packed)).write 0 mem 128 32).size =
        160 := by
    exact toByteArray_write32_size_of_le mem (uniswapSyncReserve0Word packed) 128 160 160
      hmem (by rw [hmem]; omega) (by omega)
  exact toByteArray_write32_size_of_ge
    ((UInt256.toByteArray (uniswapSyncReserve0Word packed)).write 0 mem 128 32)
    (uniswapSyncReserve1Word packed) 160 160 192 hreserve0 (by omega)
    (lt_usize _ (by norm_num)) (by omega)

theorem uniswapMintSyncLogMem_read64_of_160
    (packed : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapSyncLogMem packed mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact uniswapSyncLogMem_read64 packed mem (by rw [hmem]; omega) hmem64

theorem uniswapMintSyncLogMem_mload64_of_160
    (packed : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapSyncLogMem packed mem).size
        ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapSyncLogMem packed mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapMintSyncLogMem_size_192_of_160 packed hmem]; decide)
    (by native_decide)
    (uniswapMintSyncLogMem_read64_of_160 packed hmem hmem64)

theorem uniswapMintSyncLogMem_size_192_of_size_le
    (packed : UInt256) {mem : ByteArray}
    (hlo : 128 ≤ mem.size) (hhi : mem.size ≤ 192) :
    (uniswapSyncLogMem packed mem).size = 192 := by
  unfold uniswapSyncLogMem uniswapSyncLogReserve0Mem
  have hreserve0 :
      ((UInt256.toByteArray (uniswapSyncReserve0Word packed)).write 0 mem 128 32).size =
        max mem.size 160 := by
    exact toByteArray_write32_size_of_le mem (uniswapSyncReserve0Word packed) 128 mem.size
      (max mem.size 160) rfl (by omega) (by omega)
  exact toByteArray_write32_size_of_le
    ((UInt256.toByteArray (uniswapSyncReserve0Word packed)).write 0 mem 128 32)
    (uniswapSyncReserve1Word packed) 160 (max mem.size 160) 192 hreserve0
    (by rw [hreserve0]; omega) (by omega)

theorem uniswapMintSyncLogMem_read64_of_size_le
    (packed : UInt256) {mem : ByteArray}
    (hlo : 128 ≤ mem.size)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapSyncLogMem packed mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact uniswapSyncLogMem_read64 packed mem hlo hmem64

theorem uniswapMintSyncLogMem_mload64_of_size_le
    (packed : UInt256) {mem : ByteArray}
    (hlo : 128 ≤ mem.size) (hhi : mem.size ≤ 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapSyncLogMem packed mem).size
        ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapSyncLogMem packed mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapMintSyncLogMem_size_192_of_size_le packed hlo hhi]; decide)
    (by native_decide)
    (uniswapMintSyncLogMem_read64_of_size_le packed hlo hmem64)

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from `_mint(to, liquidity)` return through elapsed-zero `_update`,
`Sync`, fee-off handling, final `Mint`, unlock, and ABI return. -/
theorem uniswapMintRuntimeAfterInternalMintUpdateElapsedZeroFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σMint : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3914 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σMint) k C)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmemLo : 128 ≤ mem.size)
    (hmemHi : mem.size ≤ 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner σPacked ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
    (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σMint ⟨8⟩ packed
  obtain ⟨_, _, rd6959⟩ := uniswapMintRuntimeUpdateEntry rd3914
  obtain ⟨_, _, rd7339⟩ :=
    uniswapMintRuntimeUpdateElapsedZeroStore rd6959 hfit0 hfit1 helapsed0 hperm
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by omega) (by native_decide) hmem64
  obtain ⟨_, _, rd3926⟩ :=
    uniswapMintRuntimeUpdateEmitSyncReturn
      (packed := packed)
      (elapsed := uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I)
      (timestamp := uniswapUpdateTimestampWord I)
      (reserve1 := reserve1) (reserve0 := reserve0) (balance1 := balance1)
      (balance0 := balance0) (mem := mem) (aw := feeToStaticcallActiveWords)
      (awLoad := feeToStaticcallActiveWords) (awLog := feeToStaticcallActiveWords)
      (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
      (mcostLoadLog := 0) (mcostLog := 0)
      (by
        simpa [packed, σPacked, uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
          uniswapSlotWord] using rd7339)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      hmload64
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (uniswapMintSyncLogMem_mload64_of_size_le packed hmemLo hmemHi hmem64)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide) hperm
  exact uniswapMintRuntimeAfterUpdateFeeOffReturns rd3926 hfeeOff
    (uniswapMintSyncLogMem_size_192_of_size_le packed hmemLo hmemHi)
    (uniswapMintSyncLogMem_read64_of_size_le packed hmemLo hmem64) hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from `_mint(to, liquidity)` return through elapsed-zero `_update`,
`Sync`, fee-on `kLast` update, final `Mint`, unlock, and ABI return. -/
theorem uniswapMintRuntimeAfterInternalMintUpdateElapsedZeroFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σMint : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3914 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σMint) k C)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmemLo : 128 ≤ mem.size)
    (hmemHi : mem.size ≤ 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σPacked ⟨11⟩
          (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
              reserve112Mask))) ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
    (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σMint ⟨8⟩ packed
  obtain ⟨_, _, rd6959⟩ := uniswapMintRuntimeUpdateEntry rd3914
  obtain ⟨_, _, rd7339⟩ :=
    uniswapMintRuntimeUpdateElapsedZeroStore rd6959 hfit0 hfit1 helapsed0 hperm
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by omega) (by native_decide) hmem64
  obtain ⟨_, _, rd3926⟩ :=
    uniswapMintRuntimeUpdateEmitSyncReturn
      (packed := packed)
      (elapsed := uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I)
      (timestamp := uniswapUpdateTimestampWord I)
      (reserve1 := reserve1) (reserve0 := reserve0) (balance1 := balance1)
      (balance0 := balance0) (mem := mem) (aw := feeToStaticcallActiveWords)
      (awLoad := feeToStaticcallActiveWords) (awLog := feeToStaticcallActiveWords)
      (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
      (mcostLoadLog := 0) (mcostLog := 0)
      (by
        simpa [packed, σPacked, uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
          uniswapSlotWord] using rd7339)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      hmload64
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (uniswapMintSyncLogMem_mload64_of_size_le packed hmemLo hmemHi hmem64)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide) hperm
  exact uniswapMintRuntimeAfterUpdateFeeOnReturns rd3926 hfeeOn
    (by simpa [packed, σPacked] using hfitKLast)
    (uniswapMintSyncLogMem_size_192_of_size_le packed hmemLo hmemHi)
    (uniswapMintSyncLogMem_read64_of_size_le packed hmemLo hmem64) hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from `_mint(to, liquidity)` return through the cumulative `_update`
path, fee-off handling, final `Mint`, unlock, and ABI return. -/
theorem uniswapMintRuntimeAfterInternalMintUpdateCumulativeFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σMint : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3914 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σMint) k C)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsedNe :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I)
        reserve32Mask ≠ ⟨0⟩)
    (hreserve0Nonzero : UInt256.land reserve0 reserve112Mask ≠ ⟨0⟩)
    (hreserve1Nonzero : UInt256.land reserve1 reserve112Mask ≠ ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmemLo : 128 ≤ mem.size)
    (hmemHi : mem.size ≤ 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, uniswapUpdateCumulativeReturnMapWith σMint I balance0 balance1 reserve0 reserve1)
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd6959⟩ := uniswapMintRuntimeUpdateEntry rd3914
  obtain ⟨_, _, rd7060⟩ := RD.uniswapUpdateOverflowGuardOk rd6959 hfit0 hfit1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7241⟩ :=
    RD.uniswapUpdateCumulativesAndJump
      (by
        simpa [uniswapUpdateReserve0Word, uniswapUpdateReserve1Word] using rd7060)
      (by
        simpa [uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using helapsedNe)
      hreserve0Nonzero
      hreserve1Nonzero
      hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7339⟩ :=
    RD.uniswapUpdateStorePackedReserves
      (by
        simpa [uniswapUpdatePrice0CumulativeMapWith, uniswapUpdatePrice1CumulativeMapWith,
          uniswapUpdateCumulativePackedWordWith, uniswapUpdateCumulativePackedMapWith,
          uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using
          rd7241)
      hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by omega) (by native_decide) hmem64
  obtain ⟨_, _, rd3926⟩ :=
    uniswapMintRuntimeUpdateEmitSyncReturn
      (packed :=
        uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
      (elapsed := uniswapUpdateElapsedFromStorage σMint I)
      (timestamp := uniswapUpdateTimestampWord I)
      (reserve1 := reserve1)
      (reserve0 := reserve0)
      (balance1 := balance1) (balance0 := balance0) (mem := mem)
      (aw := feeToStaticcallActiveWords)
      (awLoad := feeToStaticcallActiveWords) (awLog := feeToStaticcallActiveWords)
      (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
      (mcostLoadLog := 0) (mcostLog := 0)
      (by
        simpa [uniswapUpdatePrice0CumulativeMapWith, uniswapUpdatePrice1CumulativeMapWith,
          uniswapUpdateCumulativePackedWordWith, uniswapUpdateCumulativePackedMapWith,
          uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using
          rd7339)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      hmload64
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (uniswapMintSyncLogMem_mload64_of_size_le
        (uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
        hmemLo hmemHi hmem64)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide) hperm
  simpa [uniswapUpdateCumulativeReturnMapWith] using
    uniswapMintRuntimeAfterUpdateFeeOffReturns rd3926 hfeeOff
      (uniswapMintSyncLogMem_size_192_of_size_le
        (uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
        hmemLo hmemHi)
      (uniswapMintSyncLogMem_read64_of_size_le
        (uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
        hmemLo hmem64)
      hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from `_mint(to, liquidity)` return through the cumulative `_update`
path, fee-on `kLast` update, final `Mint`, unlock, and ABI return. -/
theorem uniswapMintRuntimeAfterInternalMintUpdateCumulativeFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σMint : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3914 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σMint) k C)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsedNe :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I)
        reserve32Mask ≠ ⟨0⟩)
    (hreserve0Nonzero : UInt256.land reserve0 reserve112Mask ≠ ⟨0⟩)
    (hreserve1Nonzero : UInt256.land reserve1 reserve112Mask ≠ ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      (UInt256.land (uniswapSlotWord ⟨8⟩
          (uniswapUpdateCumulativePackedMapWith σMint I balance0 balance1 reserve0 reserve1) I)
          reserve112Mask).toNat *
          (UInt256.land
            (UInt256.div (uniswapSlotWord ⟨8⟩
              (uniswapUpdateCumulativePackedMapWith
                σMint I balance0 balance1 reserve0 reserve1) I)
              reserve112Shift) reserve112Mask).toNat <
        UInt256.size)
    (hmemLo : 128 ≤ mem.size)
    (hmemHi : mem.size ≤ 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (uniswapUpdateCumulativePackedMapWith σMint I balance0 balance1 reserve0 reserve1)
          ⟨11⟩
          (UInt256.mul
            (UInt256.land
              (uniswapSlotWord ⟨8⟩
                (uniswapUpdateCumulativePackedMapWith
                  σMint I balance0 balance1 reserve0 reserve1) I)
              reserve112Mask)
            (UInt256.land
              (UInt256.div
                (uniswapSlotWord ⟨8⟩
                  (uniswapUpdateCumulativePackedMapWith
                    σMint I balance0 balance1 reserve0 reserve1) I)
                reserve112Shift)
              reserve112Mask))) ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd6959⟩ := uniswapMintRuntimeUpdateEntry rd3914
  obtain ⟨_, _, rd7060⟩ := RD.uniswapUpdateOverflowGuardOk rd6959 hfit0 hfit1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7241⟩ :=
    RD.uniswapUpdateCumulativesAndJump
      (by
        simpa [uniswapUpdateReserve0Word, uniswapUpdateReserve1Word] using rd7060)
      (by
        simpa [uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using helapsedNe)
      hreserve0Nonzero
      hreserve1Nonzero
      hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7339⟩ :=
    RD.uniswapUpdateStorePackedReserves
      (by
        simpa [uniswapUpdatePrice0CumulativeMapWith, uniswapUpdatePrice1CumulativeMapWith,
          uniswapUpdateCumulativePackedWordWith, uniswapUpdateCumulativePackedMapWith,
          uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using
          rd7241)
      hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by omega) (by native_decide) hmem64
  obtain ⟨_, _, rd3926⟩ :=
    uniswapMintRuntimeUpdateEmitSyncReturn
      (packed :=
        uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
      (elapsed := uniswapUpdateElapsedFromStorage σMint I)
      (timestamp := uniswapUpdateTimestampWord I)
      (reserve1 := reserve1)
      (reserve0 := reserve0)
      (balance1 := balance1) (balance0 := balance0) (mem := mem)
      (aw := feeToStaticcallActiveWords)
      (awLoad := feeToStaticcallActiveWords) (awLog := feeToStaticcallActiveWords)
      (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
      (mcostLoadLog := 0) (mcostLog := 0)
      (by
        simpa [uniswapUpdatePrice0CumulativeMapWith, uniswapUpdatePrice1CumulativeMapWith,
          uniswapUpdateCumulativePackedWordWith, uniswapUpdateCumulativePackedMapWith,
          uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using
          rd7339)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      hmload64
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (uniswapMintSyncLogMem_mload64_of_size_le
        (uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
        hmemLo hmemHi hmem64)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide) hperm
  simpa [uniswapUpdateCumulativePackedMapWith, uniswapUpdateCumulativePackedWordWith] using
    uniswapMintRuntimeAfterUpdateFeeOnReturns rd3926 hfeeOn
      (by
        simpa [uniswapUpdateCumulativePackedMapWith,
          uniswapUpdateCumulativePackedWordWith] using
          hfitKLast)
      (uniswapMintSyncLogMem_size_192_of_size_le
        (uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
        hmemLo hmemHi)
      (uniswapMintSyncLogMem_read64_of_size_le
        (uniswapUpdateCumulativePackedWordWith σMint I balance0 balance1 reserve0 reserve1)
        hmemLo hmem64)
      hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only common Mint branch from the successful `liquidity > 0` check through
`_mint(to, liquidity)`, elapsed-zero `_update`, fee-off handling, final `Mint`, unlock, and ABI
return. -/
theorem uniswapMintRuntimeLiquidityMintUpdateElapsedZeroFeeOffReturns
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
    uniswapMintRuntimeLiquidityMintReturn rd3841 hliqNonzero hperm htotalFit hbalanceFit
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
  exact uniswapMintRuntimeAfterInternalMintUpdateElapsedZeroFeeOffReturns
    (σMint := σAfterMint) (mem := mintMem)
    (by simpa [σAfterMint, mintMem] using rd3914)
    hfit0 hfit1 (by simpa [σAfterMint] using helapsed0) hfeeOff
    (by rw [hmintMemSize]; omega) (by rw [hmintMemSize]; omega) hmintMem64 hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only common Mint branch from the successful `liquidity > 0` check through
`_mint(to, liquidity)`, elapsed-zero `_update`, fee-on `kLast`, final `Mint`, unlock, and ABI
return. -/
theorem uniswapMintRuntimeLiquidityMintUpdateElapsedZeroFeeOnReturns
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
    uniswapMintRuntimeLiquidityMintReturn rd3841 hliqNonzero hperm htotalFit hbalanceFit
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
  exact uniswapMintRuntimeAfterInternalMintUpdateElapsedZeroFeeOnReturns
    (σMint := σAfterMint) (mem := mintMem)
    (by simpa [σAfterMint, mintMem] using rd3914)
    hfit0 hfit1 (by simpa [σAfterMint] using helapsed0) hfeeOn
    (by simpa [σAfterMint] using hfitKLast)
    (by rw [hmintMemSize]; omega) (by rw [hmintMemSize]; omega) hmintMem64 hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch after `sqrt` through the fee-off final return. -/
theorem uniswapMintRuntimeInitialLiquidityAfterRootUpdateElapsedZeroFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (htotalFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let minimumMem :=
      uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
        (uniswapInternalMintBalanceHashMem ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
    let σAfterMinimum :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord minimumMem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner σPacked ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  let σAfterMinimum :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeInitialLiquidityAfterRootEntry rd2531 hliquidity hrootGeMin hperm
      htotalFitMin hbalanceFitMin hmem hmem64
  have hminimumMemSize : minimumMem.size = 164 := by
    simpa [minimumMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega)
  have hminimumMem64 : minimumMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [minimumMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega) hmem64
  exact uniswapMintRuntimeLiquidityMintUpdateElapsedZeroFeeOffReturns
    (σFee := σAfterMinimum) (mem := minimumMem) (totalSupply := ⟨0⟩)
    rd3841 hliqNonzero hperm htotalFit hbalanceFit hfit0 hfit1 helapsed0 hfeeOff
    hminimumMemSize hminimumMem64

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch after `sqrt` through the fee-on final return. -/
theorem uniswapMintRuntimeInitialLiquidityAfterRootUpdateElapsedZeroFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (htotalFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let minimumMem :=
      uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
        (uniswapInternalMintBalanceHashMem ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
    let σAfterMinimum :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord minimumMem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
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
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  let σAfterMinimum :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeInitialLiquidityAfterRootEntry rd2531 hliquidity hrootGeMin hperm
      htotalFitMin hbalanceFitMin hmem hmem64
  have hminimumMemSize : minimumMem.size = 164 := by
    simpa [minimumMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega)
  have hminimumMem64 : minimumMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [minimumMem] using
      uniswapInternalMintSuccessMem_read64_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega) hmem64
  exact uniswapMintRuntimeLiquidityMintUpdateElapsedZeroFeeOnReturns
    (σFee := σAfterMinimum) (mem := minimumMem) (totalSupply := ⟨0⟩)
    rd3841 hliqNonzero hperm htotalFit hbalanceFit hfit0 hfit1 helapsed0 hfeeOn hfitKLast
    hminimumMemSize hminimumMem64

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch: one sqrt-loop iteration with the Mint continuation
stack shape. -/
theorem uniswapMintRuntimeInitialLiquidityLoopStep
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {x z y feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8067 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [x, z, y, ⟨2531⟩, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hlt : x.toNat < z.toNat)
    (hx : x ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [UInt256.div (UInt256.div y x + x) ⟨2⟩, x, y, ⟨2531⟩, ⟨1000⟩, ⟨3742⟩,
        ⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapSqrtRuntimeLoopStep rd8067 hlt hx
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch from a sqrt-loop exit through the fee-off final return. -/
theorem uniswapMintRuntimeInitialLiquidityLoopExitUpdateElapsedZeroFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {x root y feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord
      sel : UInt256}
    (rd8067 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [x, root, y, ⟨2531⟩, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hnlt : ¬ x.toNat < root.toNat)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (htotalFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let minimumMem :=
      uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
        (uniswapInternalMintBalanceHashMem ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
    let σAfterMinimum :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord minimumMem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
    let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
    let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner σPacked ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd2531⟩ :=
    uniswapSqrtRuntimeLoopExit rd8067 hnlt (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact uniswapMintRuntimeInitialLiquidityAfterRootUpdateElapsedZeroFeeOffReturns
    rd2531 hliquidity hrootGeMin hliqNonzero hperm htotalFitMin hbalanceFitMin
    htotalFit hbalanceFit hfit0 hfit1 helapsed0 hfeeOff hmem hmem64

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch from a sqrt-loop exit through the fee-on final return. -/
theorem uniswapMintRuntimeInitialLiquidityLoopExitUpdateElapsedZeroFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {x root y feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord
      sel : UInt256}
    (rd8067 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [x, root, y, ⟨2531⟩, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hnlt : ¬ x.toNat < root.toNat)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (htotalFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let minimumMem :=
      uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
        (uniswapInternalMintBalanceHashMem ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
    let σAfterMinimum :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
    let σAfterMint :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (uniswapInternalMintBalanceHashMem toWord minimumMem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
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
  obtain ⟨_, _, rd2531⟩ :=
    uniswapSqrtRuntimeLoopExit rd8067 hnlt (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact uniswapMintRuntimeInitialLiquidityAfterRootUpdateElapsedZeroFeeOnReturns
    rd2531 hliquidity hrootGeMin hliqNonzero hperm htotalFitMin hbalanceFitMin
    htotalFit hbalanceFit hfit0 hfit1 helapsed0 hfeeOn hfitKLast hmem hmem64

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

import Examples.UniswapV2Pair.MintRuntimeAfterFeeProportional

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix: setup for the internal `_update(balance0, balance1, _reserve0,
_reserve1)` routine after `_mint(to, liquidity)` returns. -/
theorem uniswapMintRuntimeUpdateEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3914 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨6959⟩
      [reserve1, reserve0, balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  exact ⟨_, _, evm_run rd3914 with [
    jumpdest, push2 ⟨3926⟩, dup7, dup7, dup11, dup11, push2 ⟨6959⟩,
    jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint `_update` elapsed-zero path through the packed reserve `SSTORE`, stopping
before `Sync` event emission. -/
theorem uniswapMintRuntimeUpdateElapsedZeroStore
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σMint : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd6959 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨6959⟩
      [reserve1, reserve0, balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σMint k C)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I) reserve32Mask =
        ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨7339⟩
      [reserve112Shift, reserve112Mask,
        uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0,
        uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I,
        uniswapUpdateTimestampWord I,
        reserve1, reserve0, balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata
      (sstoreAccountMap I.codeOwner σMint ⟨8⟩
        (uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0)) k' C' := by
  obtain ⟨_, _, rd7060⟩ := RD.uniswapUpdateOverflowGuardOk rd6959 hfit0 hfit1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7241⟩ := RD.uniswapUpdateElapsedZeroSkipsCumulatives rd7060
    (by
      simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord]
        using helapsed0)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7339⟩ := RD.uniswapUpdateStorePackedReserves
    (by
      simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
    hperm
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using rd7339⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint `_update` suffix: emit `Sync` and return from `_update` to pc 3926.  The
memory hypotheses are explicit because callers may enter `_update` with different memory shapes. -/
theorem uniswapMintRuntimeUpdateEmitSyncReturn
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {packed elapsed timestamp reserve1 reserve0 balance1 balance0 totalSupply feeOn amount1
      amount0 liquidity toWord sel : UInt256}
    {mem rdata : ByteArray} {aw awLoad awLog : UInt256}
    {mcostLoad mcostStore0 mcostStore1 mcostLoadLog mcostLog : ℕ}
    {σUpd : AccountMap}
    (rd7339 : RD uniswapV2PairBytecode ee g s0 ⟨7339⟩
      [reserve112Shift, reserve112Mask, packed, elapsed, timestamp, reserve1, reserve0,
        balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0, balance1,
        balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σUpd k C)
    (hmcLoad : Cₘ (M aw ⟨64⟩ ⟨32⟩) - Cₘ aw = mcostLoad)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat 64 32) = awLoad)
    (hmcStore0 : Cₘ (M awLoad ⟨128⟩ ⟨32⟩) - Cₘ awLoad = mcostStore0)
    (hawStore0 : UInt256.ofNat (MachineState.M awLoad.toNat 128 32) = awLog)
    (hmcStore1 : Cₘ (M awLog (⟨128⟩ + ⟨32⟩) ⟨32⟩) - Cₘ awLog = mcostStore1)
    (hawStore1 :
      UInt256.ofNat (MachineState.M awLog.toNat (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) 32) =
        awLog)
    (hmcLoadLog : Cₘ (M awLog ⟨64⟩ ⟨32⟩) - Cₘ awLog = mcostLoadLog)
    (hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapSyncLogMem packed mem).size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((uniswapSyncLogMem packed mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hawLoadLog : UInt256.ofNat (MachineState.M awLog.toNat 64 32) = awLog)
    (hmcLog : Cₘ (M awLog ⟨128⟩ (⟨64⟩ + UInt256.sub ⟨128⟩ ⟨128⟩)) - Cₘ awLog = mcostLog)
    (hawLog : UInt256.ofNat
      (MachineState.M awLog.toNat 128
        (((⟨64⟩ : UInt256) + UInt256.sub ⟨128⟩ ⟨128⟩).toNat)) = awLog)
    (hperm : ee.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      (uniswapSyncLogMem packed mem) awLog rdata σUpd k' C' := by
  exact RD.uniswapUpdateEmitSyncAndJump
    (packed := packed) (elapsed := elapsed) (timestamp := timestamp) (reserve1 := reserve1)
    (reserve0 := reserve0) (balance1 := balance1) (balance0 := balance0) (ret := ⟨3926⟩)
    (R := [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
      liquidity, toWord, ⟨861⟩, sel])
    rd7339 hmcLoad hmload64 hawLoad hmcStore0 hawStore0 hmcStore1 hawStore1 hmcLoadLog
    hmload64Log hawLoadLog hmcLog hawLog hperm (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update`: when `feeOn` is false, skip the `kLast` update. -/
theorem uniswapMintRuntimeAfterUpdateFeeOff
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σUpd : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σUpd k C)
    (hfeeOff : feeOn = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σUpd k' C' := by
  have rd3932pre := evm_run rd3926 with [jumpdest, dup2, iszero, push2 ⟨3974⟩]
  rw [hfeeOff, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3932pre
  have rd3974 := evm_run rd3932pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, by simpa [hfeeOff] using rd3974⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update`: when `feeOn` is true, update `kLast` from the
freshly packed reserves in slot 8 and rejoin at pc 3974. -/
theorem uniswapMintRuntimeAfterUpdateFeeOn
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σUpd : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σUpd k C)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfit :
      (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hperm : I.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata
      (sstoreAccountMap I.codeOwner σUpd ⟨11⟩
        (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask)
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
            reserve112Mask))) k' C' := by
  let slot8 := uniswapSlotWord ⟨8⟩ σUpd I
  let packedReserve0 := UInt256.land slot8 reserve112Mask
  let packedReserve1 := UInt256.land (UInt256.div slot8 reserve112Shift) reserve112Mask
  have rd3932pre := evm_run rd3926 with [jumpdest, dup2, iszero, push2 ⟨3974⟩]
  rw [isZero_eq_zero_of_ne hfeeOn] at rd3932pre
  have rd3933 := evm_run rd3932pre with [jumpiNT (by native_decide)]
  have rd3935pre := evm_run rd3933 with [push1 ⟨8⟩]
  obtain ⟨k3936, C3936, rd3936₀⟩ := rd3935pre.sload (by native_decide) (by evm_ov)
  have rd3936 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3936⟩
      [slot8, totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1,
        reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σUpd k3936 C3936 := by
    simpa [slot8, uniswapSlotWord] using rd3936₀
  have rd6780pre := evm_run rd3936 with [
    push2 ⟨3970⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup1, dup3,
    and, swap2, push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, and, push4 ⟨0xffffffff⟩,
    push2 ⟨6780⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from by rfl,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide]
    at rd6780pre
  have rd6780 := by
    simpa [slot8, packedReserve0, packedReserve1] using
      rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3970⟩ := RD.uniswapSafeMathMulSuccess
    (a := packedReserve0) (b := packedReserve1) rd6780
    (by simpa [packedReserve0, packedReserve1, slot8] using hfit) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3973 := evm_run rd3970 with [jumpdest, push1 ⟨11⟩]
  obtain ⟨_, _, rd3974⟩ := rd3973.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [slot8, packedReserve0, packedReserve1] using rd3974⟩

abbrev uniswapMintTopic : UInt256 :=
  ⟨0x4c209b5fc8ad50758f13e2e1088ba56a560dff690a1c6fef26394f4c03821c4f⟩

abbrev uniswapMintLogMem
    (amount0 amount1 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray amount1).write 0
    ((UInt256.toByteArray amount0).write 0 mem 128 32) 160 32

abbrev uniswapMintReturnMem
    (liquidity amount0 amount1 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray liquidity).write 0 (uniswapMintLogMem amount0 amount1 mem) 128 32


end UniswapV2Pair

import Examples.UniswapV2Pair.SwapDecoderPrefix
import Examples.UniswapV2Pair.MemorySteps
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000


theorem swapRuntimeWords_eq {I : ExecutionEnv}
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I) :
    swapRuntimeDataSizeWord I = swapDataSizeWord I ∧
    (swapRuntimePayloadPtr I).toNat = 4 + swapDataOffset I + 32 := by
  have hoff : swapDataOffset I ≤ 4294967296 := by simpa [solcLegacyMaxU32] using Nat.le_of_not_gt hoffMax
  have hcap : 4 + 4294967296 + 32 < UInt256.size := by native_decide
  have h4 : ((⟨4⟩ : UInt256) + swapDataOffsetWord I).toNat = 4 + swapDataOffset I := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 by rfl,
      Nat.mod_eq_of_lt (by change 4 + swapDataOffset I < UInt256.size; omega)]
  refine ⟨?_, ?_⟩
  · unfold swapRuntimeDataSizeWord swapDataSizeWord
    rw [h4]
  · unfold swapRuntimePayloadPtr
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by rfl, h4, Nat.mod_eq_of_lt (by omega)]
    omega

theorem swapRuntimePayloadGuard_ok {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size) (hsz : 4 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : 4 + swapDataOffset I + 32 + swapDataSize I ≤ I.calldata.size) :
    UInt256.gt (swapRuntimePayloadPtr I + UInt256.mul (swapRuntimeDataSizeWord I) ⟨1⟩)
      (swapRuntimeCalldataEnd I) = ⟨0⟩ ∧
    UInt256.gt (swapRuntimeDataSizeWord I) ⟨4294967296⟩ = ⟨0⟩ := by
  obtain ⟨hlen, hptr⟩ := swapRuntimeWords_eq hoffMax
  have hoff : swapDataOffset I ≤ 4294967296 := by simpa [solcLegacyMaxU32] using Nat.le_of_not_gt hoffMax
  have hlenB : swapDataSize I ≤ 4294967296 := by simpa [solcLegacyMaxU32] using Nat.le_of_not_gt hlenMax
  have hcap : 4 + 4294967296 + 32 + 4294967296 < UInt256.size := by native_decide
  have hmul : (UInt256.mul (swapRuntimeDataSizeWord I) ⟨1⟩).toNat = swapDataSize I := by
    rw [u256_mul_toNat, hlen, show (⟨1⟩ : UInt256).toNat = 1 by rfl, Nat.mul_one,
      Nat.mod_eq_of_lt (show (swapDataSizeWord I).toNat < UInt256.size from (swapDataSizeWord I).val.isLt)]
  have hsum : (swapRuntimePayloadPtr I + UInt256.mul (swapRuntimeDataSizeWord I) ⟨1⟩).toNat =
      4 + swapDataOffset I + 32 + swapDataSize I := by
    rw [uadd_toNat, hptr, hmul, Nat.mod_eq_of_lt (by omega)]
  have hend : swapRuntimeCalldataEnd I = UInt256.ofNat I.calldata.size :=
    uadd_word_usub_ofNat_word (n := I.calldata.size) (c := ⟨4⟩) hsz hsize
  refine ⟨ugt_zero ?_, ugt_zero ?_⟩
  · rw [hsum, hend, UInt256.toNat_ofNat_of_lt hsize]
    exact hpayload
  · rw [hlen]
    exact hlenB


set_option maxHeartbeats 1000000 in
theorem uniswapSwapDecodeRuntimeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : 4 + swapDataOffset I + 32 + swapDataSize I ≤ I.calldata.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1475⟩
      [swapDataSizeWord I, swapRuntimePayloadPtr I, swapToMaskedWord I,
        swapAmount1OutWord I, swapAmount0OutWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd541⟩ := uniswapSwapDecodeToPayloadGuard hsize hsz132 hoffMax hlenWord hreach
  obtain ⟨hgtPayload, hgtLen⟩ := swapRuntimePayloadGuard_ok hsize (by omega) hoffMax hlenMax hpayload
  dsimp only [swapPayloadGuardStack] at rd541
  rw [hgtPayload] at rd541
  have rd547 := rd541.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd549 := evm_run rd547 with [dup4, gt]
  rw [hgtLen] at rd549
  have rd554 := evm_run rd549 with [or, iszero, push2 ⟨559⟩]
  have rd559 := evm_run rd554 with [jumpiT (by native_decide) (by jump_dest)]
  have rd1475 := evm_run rd559 with [jumpdest, pop, swap1, swap3, pop, swap1, pop, push2 ⟨1475⟩, jump (by jump_dest)]
  rw [(swapRuntimeWords_eq hoffMax).1] at rd1475
  rw [u256_land_comm (swapToWord I) solcAddrMask] at rd1475
  exact ⟨_, _, rd1475⟩

end UniswapV2Pair

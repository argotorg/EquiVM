import Examples.UniswapV2Pair.SwapABI
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

abbrev swapRuntimeDataSizeWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata ((⟨4⟩ : UInt256) + swapDataOffsetWord I).toNat
abbrev swapRuntimePayloadPtr (I : ExecutionEnv) : UInt256 :=
  ⟨32⟩ + ((⟨4⟩ : UInt256) + swapDataOffsetWord I)
abbrev swapRuntimeCalldataEnd (I : ExecutionEnv) : UInt256 :=
  ⟨4⟩ + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩
abbrev swapPayloadGuardStack (I : ExecutionEnv) (sel : UInt256) : List UInt256 :=
  [UInt256.gt (swapRuntimePayloadPtr I + UInt256.mul (swapRuntimeDataSizeWord I) ⟨1⟩) (swapRuntimeCalldataEnd I),
    ⟨132⟩, swapRuntimeDataSizeWord I, swapRuntimePayloadPtr I, ⟨4⟩, swapRuntimeCalldataEnd I,
    UInt256.land (swapToWord I) solcAddrMask, swapAmount1OutWord I, swapAmount0OutWord I, ⟨570⟩, sel]

theorem uniswapSwapDecodeToPayloadGuard {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨541⟩
      (swapPayloadGuardStack I sel) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz132) hsize
  obtain ⟨_, _, rd452⟩ := RD.solcExternalStaticArgsLenOk
    (code := uniswapV2PairBytecode) (entry := ⟨430⟩) (ret := ⟨570⟩)
    (decoded := ⟨452⟩) (need := ⟨128⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hlt
  have rd490 := evm_run rd452 with [
    jumpdest, dup2, calldataload, swap2, push1 ⟨32⟩, dup2, add, calldataload,
    swap2, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, push1 ⟨64⟩,
    dup4, add, calldataload, and, swap2, swap1, dup2, add, swap1, push1 ⟨128⟩,
    dup2, add, push1 ⟨96⟩, dup3, add, calldataload]
  have hoffPass :
      UInt256.gt
        (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))
        ⟨4294967296⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    simpa [swapDataOffset, swapDataOffsetWord, calldataWord,
      show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide] using hoffLe
  have rd496 := rd490.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd497 := rd496.dup2 (by native_decide) (by evm_ov)
  have rd498₀ := rd497.gt (by native_decide) (by evm_ov)
  have rd498 := rd498₀
  rw [hoffPass] at rd498
  have rd499₀ := rd498.iszero (by native_decide) (by evm_ov)
  have rd499 := rd499₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd499
  have rd502 := rd499.push2 ⟨507⟩ (by native_decide) (by evm_ov)
  have rd507 := rd502.jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by evm_ov)
  have rd516 := evm_run rd507 with [
    jumpdest, dup3, add, dup4, push1 ⟨32⟩, dup3, add, gt]
  have hgtLen :
      UInt256.gt
        (((⟨4⟩ : UInt256) +
            uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩)
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) =
        ⟨0⟩ := by
    apply ugt_zero
    have hoffWord :
        (uInt256OfByteArray
          (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat =
          swapDataOffset I := by
      simp [swapDataOffset, swapDataOffsetWord, calldataWord,
        show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    have hleft1 :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hleft :
        ((((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩).toNat) = 4 + swapDataOffset I + 32 := by
      rw [uadd_toNat, hleft1, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 + 32 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hright :
        (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
          I.calldata.size := by
      have hword :
          (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
            UInt256.ofNat I.calldata.size :=
        uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
          (by
            rw [show ((⟨4⟩ : UInt256).toNat) = 4 from by decide]
            omega)
          hsize
      rw [hword, ulit_toNat' I.calldata.size hsize]
    rw [hleft, hright]
    exact hlenWord
  have rd516' := rd516
  rw [hgtLen] at rd516'
  have rd517₀ := rd516'.iszero (by native_decide) (by evm_ov)
  have rd517 := rd517₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd517
  have rd520 := rd517.push2 ⟨525⟩ (by native_decide) (by evm_ov)
  have rd525 := rd520.jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by evm_ov)
  have rd540 := evm_run rd525 with [
    jumpdest, dup1, calldataload, swap1, push1 ⟨32⟩, add, swap2, dup5,
    push1 ⟨1⟩, dup4, mul, dup5, add, gt]
  exact ⟨_, _, rd540⟩

end UniswapV2Pair

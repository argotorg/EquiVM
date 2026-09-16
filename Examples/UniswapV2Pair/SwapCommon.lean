import Examples.UniswapV2Pair.SwapDecoderPrefix
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
namespace UniswapV2Pair

theorem uniswapSwapX_shortHead {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 132)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := uniswapV2PairBytecode) (entry := ⟨430⟩) (ret := ⟨570⟩)
    (decoded := ⟨452⟩) (need := ⟨128⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem uniswapSwapX_offsetHuge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoff : solcLegacyMaxU32 < swapDataOffset I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
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
  have hgt :
      UInt256.gt
        (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))
        ⟨4294967296⟩ = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hoff' : 4294967296 < swapDataOffset I := by
      simpa [solcLegacyMaxU32] using hoff
    simpa [swapDataOffset, swapDataOffsetWord, calldataWord,
      show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide] using hoff'
  have rd496 := rd490.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd497 := rd496.dup2 (by native_decide) (by evm_ov)
  have rd498₀ := rd497.gt (by native_decide) (by evm_ov)
  have rd498 := rd498₀
  rw [hgt] at rd498
  have rd499₀ := rd498.iszero (by native_decide) (by evm_ov)
  have rd499 := rd499₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd499
  have rd502 := rd499.push2 ⟨507⟩ (by native_decide) (by evm_ov)
  have rd503 := rd502.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd505 := rd503.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd506 := rd505.dup1 (by native_decide) (by evm_ov)
  exact rd506.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem uniswapSwapX_lengthShort {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenShort : I.calldata.size < 4 + swapDataOffset I + 32)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
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
        ⟨1⟩ := by
    apply ugt_one
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
    exact hlenShort
  have rd516' := rd516
  rw [hgtLen] at rd516'
  have rd517₀ := rd516'.iszero (by native_decide) (by evm_ov)
  have rd517 := rd517₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd517
  have rd520 := rd517.push2 ⟨525⟩ (by native_decide) (by evm_ov)
  have rd521 := rd520.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd523 := rd521.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd524 := rd523.dup1 (by native_decide) (by evm_ov)
  exact rd524.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem uniswapSwapX_lengthHuge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd540⟩ := uniswapSwapDecodeToPayloadGuard hsize hsz132 hoffMax hlenWord hreach
  dsimp only [swapPayloadGuardStack, swapRuntimeDataSizeWord, swapRuntimePayloadPtr,
    swapRuntimeCalldataEnd, swapDataOffsetWord, swapToWord, swapAmount1OutWord, swapAmount0OutWord, calldataWord] at rd540
  have rd546 := rd540.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd547 := rd546.dup4 (by native_decide) (by evm_ov)
  have rd548₀ := rd547.gt (by native_decide) (by evm_ov)
  have hgtHuge :
      UInt256.gt
        (uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
            32))
        ⟨4294967296⟩ = ⟨1⟩ := by
    apply ugt_one
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
    have hlenOffset :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hread :
        (uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
            32)).toNat = swapDataSize I := by
      simp [swapDataSize, swapDataSizeWord, calldataWord, hlenOffset]
    rw [hread]
    simpa [solcLegacyMaxU32] using hlenHuge
  have rd548 := rd548₀
  rw [show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 by rfl] at hgtHuge
  rw [hgtHuge] at rd548
  have rd549 := RD.or rd548 (by native_decide) (by evm_ov)
  have rd550₀ := rd549.iszero (by native_decide) (by evm_ov)
  have rd550 := rd550₀
  rw [isZero_eq_zero_of_ne (swapU256_lor_one_ne_zero_left _)] at rd550
  have rd553 := rd550.push2 ⟨559⟩ (by native_decide) (by evm_ov)
  have rd554 := rd553.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd556 := rd554.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd557 := rd556.dup1 (by native_decide) (by evm_ov)
  exact rd557.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem uniswapSwapX_payloadShort {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd540⟩ := uniswapSwapDecodeToPayloadGuard hsize hsz132 hoffMax hlenWord hreach
  dsimp only [swapPayloadGuardStack, swapRuntimeDataSizeWord, swapRuntimePayloadPtr,
    swapRuntimeCalldataEnd, swapDataOffsetWord, swapToWord, swapAmount1OutWord, swapAmount0OutWord, calldataWord] at rd540
  have hgtPayload :
      UInt256.gt
        (((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                (((⟨4⟩ : UInt256) +
                  uInt256OfByteArray
                    (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
                32))
            ⟨1⟩)
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) =
        ⟨1⟩ := by
    apply ugt_one
    have hpayloadNat := swapPayloadShort_lt (I := I) hpayload
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
    have hlenLe : swapDataSize I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataSize I := by
        simpa [solcLegacyMaxU32] using hlenMax
      omega
    have hlenOffset :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hbase :
        (((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))).toNat) =
          4 + swapDataOffset I + 32 := by
      rw [uadd_toNat, hlenOffset, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [Nat.mod_eq_of_lt (by
        have hcap : 32 + (4 + 4294967296) < UInt256.size := by norm_num [UInt256.size]
        omega)]
      omega
    have hread :
        (uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
            32)).toNat = swapDataSize I := by
      simp [swapDataSize, swapDataSizeWord, calldataWord, hlenOffset]
    have hmul :
        (UInt256.mul
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray
                  (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
              32))
          ⟨1⟩).toNat = swapDataSize I := by
      rw [u256_mul_toNat, hread, show (⟨1⟩ : UInt256).toNat = 1 from by decide]
      rw [Nat.mul_one, Nat.mod_eq_of_lt]
      have hcap : 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hleft :
        ((((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                (((⟨4⟩ : UInt256) +
                  uInt256OfByteArray
                    (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
                32))
            ⟨1⟩).toNat) = 4 + swapDataOffset I + 32 + swapDataSize I := by
      rw [uadd_toNat, hbase, hmul]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 + 32 + 4294967296 < UInt256.size := by
        norm_num [UInt256.size]
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
    exact hpayloadNat
  have rd540' := rd540
  rw [show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 by rfl] at hgtPayload
  rw [hgtPayload] at rd540'
  have rd546 := rd540'.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd547 := rd546.dup4 (by native_decide) (by evm_ov)
  have rd548 := rd547.gt (by native_decide) (by evm_ov)
  have rd549 := RD.or rd548 (by native_decide) (by evm_ov)
  have rd550₀ := rd549.iszero (by native_decide) (by evm_ov)
  have rd550 := rd550₀
  rw [isZero_eq_zero_of_ne (swapU256_lor_one_ne_zero_right _)] at rd550
  have rd553 := rd550.push2 ⟨559⟩ (by native_decide) (by evm_ov)
  have rd554 := rd553.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd556 := rd554.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd557 := rd556.dup1 (by native_decide) (by evm_ov)
  exact rd557.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem uniswapSwapBodyCoreDecodeFailed_headShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_head_short (I := I) hsz4 hshort
  exact (uniswapSwapX_shortHead (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_headShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hshort : I.calldata.size < 132)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_headShort hcode hsize hsz4 hshort hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_offsetHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size) (hoff : solcLegacyMaxU32 < swapDataOffset I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_offset_huge (I := I) hsz132 hoff
  exact (uniswapSwapX_offsetHuge (g := Sat256.ofUInt256 g)
      hsize hsz132 hoff hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_offsetHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoff : solcLegacyMaxU32 < swapDataOffset I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_offsetHuge hcode hsize hsz132 hoff hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_lengthShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenShort : I.calldata.size < 4 + swapDataOffset I + 32)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_length_short (I := I) hsz132 hoffMax hlenShort
  exact (uniswapSwapX_lengthShort (g := Sat256.ofUInt256 g)
      hsize hsz132 hoffMax hlenShort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_lengthShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenShort : I.calldata.size < 4 + swapDataOffset I + 32)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_lengthShort hcode hsize hsz132 hoffMax hlenShort
    hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_lengthHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_length_huge (I := I) hsz132 hoffMax hlenWord hlenHuge
  exact (uniswapSwapX_lengthHuge (g := Sat256.ofUInt256 g)
      hsize hsz132 hoffMax hlenWord hlenHuge hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_lengthHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_lengthHuge hcode hsize hsz132 hoffMax hlenWord
    hlenHuge hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_payloadShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_payload_short (I := I) hsz132 hoffMax hlenWord
    hlenMax hpayload
  exact (uniswapSwapX_payloadShort (g := Sat256.ofUInt256 g)
      hsize hsz132 hoffMax hlenWord hlenMax hpayload hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_payloadShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_payloadShort hcode hsize hsz132 hoffMax hlenWord
    hlenMax hpayload hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

end UniswapV2Pair

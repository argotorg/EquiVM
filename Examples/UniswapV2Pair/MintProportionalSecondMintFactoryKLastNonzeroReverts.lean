import Examples.UniswapV2Pair.MintProportionalSecondMintFactoryReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastNonzeroSecondMintTotalSupplyOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σCleared σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 : typedCallViaEVM config
      (uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (EVM.address
        (uniswapAddressAtSlot
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
      "balanceOf" 0
      [.address
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
      (true, evm0S, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcleared : sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩ = σCleared)
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σCleared I = totalSupply)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hcase :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩ ∧
      mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
      totalSupply ≠ ⟨0⟩ ∧
      amount0.toNat * totalSupply.toNat < UInt256.size ∧
      amount1.toNat * totalSupply.toNat < UInt256.size ∧
      reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
      liquidity =
        minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) ∧
      liquidity ≠ ⟨0⟩ ∧
      UInt256.size ≤ mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFeeS)
        liquidity ∧
      UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σCleared I).toNat + liquidity.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with
    ⟨hfeeToZero, hkLastNonzero, htotalNonzero, hmulFit0, hmulFit1,
      hreserve0Nonzero, hreserve1Nonzero, hliquidity, hliqNonzero, hsourceOverflow,
      hruntimeOverflow⟩
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hPostCleared : accountMapEquiv σCleared evmAfterFee.accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩ hPostAccountsFee
    simpa [evmAfterFee, ← hcleared, mintFeeKLastClearedState, henvFeeI,
      storageStore_accountMap] using hstore
  have henvCleared : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
  have htotalEq : mintFunctionTotalSupplyWord evmAfterFee = totalSupply := by
    have hword := mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPostCleared
      henvCleared
    simpa [htotalSlot] using hword
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve1]
      dsimp [reserve1Word]
      exact reserve112Word_lt _)
  obtain ⟨k3701, C3701, rd3701Raw⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero hperm
      hkLastNonzero
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σCleared) k3701 C3701 := by
    simpa [hruntimeReserve0, hruntimeReserve1, hcleared] using rd3701Raw
  obtain ⟨k3762, C3762, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotalSlot htotalNonzero
  have hmem :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).size = 164 :=
    feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool false])
  have hreserve0Eq' : uniswapReserve0Word evmL = reserve0 := by
    simpa [evmL, evmS] using hreserve0Eq
  have hreserve1Eq' : uniswapReserve1Word evmL = reserve1 := by
    simpa [evmL, evmS] using hreserve1Eq
  have hamount0Eq' : mintAmount0Word evmL balance0 = amount0 := by
    simpa [evmL, evmS] using hamount0Eq
  have hamount1Eq' : mintAmount1Word evmL balance1 = amount1 := by
    simpa [evmL, evmS] using hamount1Eq
  exact uniswapMintProportionalSecondMintTotalSupplyOverflowFromAfterFeeCase
    nextFrame.locals (AccountAddress.ofNat (mintToWord I).toNat)
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
    hdec1 hle0Source hle1Source
    (by
      simpa [nextFrame, evmL, evmS, evmAfterFee, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
          balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
          hfeeToAddr hkLastSource)
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hamount0Eq', mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hamount1Eq', mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hreserve0Eq'] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hreserve1Eq'] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    htotalEq htotalNonzero hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero
    (by simpa using hliquidity) hliqNonzero
    (by simpa [evmAfterFee] using hsourceOverflow) rd3762 hclean0 hclean1
    hruntimeOverflow hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastNonzeroSecondMintBalanceOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σCleared σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 : typedCallViaEVM config
      (uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (EVM.address
        (uniswapAddressAtSlot
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
      "balanceOf" 0
      [.address
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
      (true, evm0S, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcleared : sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩ = σCleared)
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σCleared I = totalSupply)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hcase :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩ ∧
      mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
      totalSupply ≠ ⟨0⟩ ∧
      amount0.toNat * totalSupply.toNat < UInt256.size ∧
      amount1.toNat * totalSupply.toNat < UInt256.size ∧
      reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
      liquidity =
        minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) ∧
      liquidity ≠ ⟨0⟩ ∧
      mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFeeS) liquidity <
        UInt256.size ∧
      UInt256.size ≤
        mintFunctionToBalanceNewNat (mintFeeKLastClearedState evmFeeS)
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity ∧
      (uniswapSlotWord ⟨0⟩ σCleared I).toNat + liquidity.toNat < UInt256.size ∧
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σCleared I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (feeToStaticcallMem
              (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
              outFee))).toNat + liquidity.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with
    ⟨hfeeToZero, hkLastNonzero, htotalNonzero, hmulFit0, hmulFit1,
      hreserve0Nonzero, hreserve1Nonzero, hliquidity, hliqNonzero, hfitSupplySource,
      hsourceOverflow, hruntimeSupplyFit, hruntimeOverflow⟩
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hPostCleared : accountMapEquiv σCleared evmAfterFee.accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩ hPostAccountsFee
    simpa [evmAfterFee, ← hcleared, mintFeeKLastClearedState, henvFeeI,
      storageStore_accountMap] using hstore
  have henvCleared : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
  have htotalEq : mintFunctionTotalSupplyWord evmAfterFee = totalSupply := by
    have hword := mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPostCleared
      henvCleared
    simpa [htotalSlot] using hword
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve1]
      dsimp [reserve1Word]
      exact reserve112Word_lt _)
  obtain ⟨k3701, C3701, rd3701Raw⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero hperm
      hkLastNonzero
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σCleared) k3701 C3701 := by
    simpa [hruntimeReserve0, hruntimeReserve1, hcleared] using rd3701Raw
  obtain ⟨k3762, C3762, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotalSlot htotalNonzero
  have hmem :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).size = 164 :=
    feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool false])
  have hreserve0Eq' : uniswapReserve0Word evmL = reserve0 := by
    simpa [evmL, evmS] using hreserve0Eq
  have hreserve1Eq' : uniswapReserve1Word evmL = reserve1 := by
    simpa [evmL, evmS] using hreserve1Eq
  have hamount0Eq' : mintAmount0Word evmL balance0 = amount0 := by
    simpa [evmL, evmS] using hamount0Eq
  have hamount1Eq' : mintAmount1Word evmL balance1 = amount1 := by
    simpa [evmL, evmS] using hamount1Eq
  exact uniswapMintProportionalSecondMintBalanceOverflowFromAfterFeeCase
    nextFrame.locals (AccountAddress.ofNat (mintToWord I).toNat)
    hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
    hdec1 hle0Source hle1Source
    (by
      simpa [nextFrame, evmL, evmS, evmAfterFee, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
          balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
          hfeeToAddr hkLastSource)
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hamount0Eq', mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hamount1Eq', mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hreserve0Eq'] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hreserve1Eq'] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    htotalEq htotalNonzero hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero
    (by simpa using hliquidity) hliqNonzero
    (by simpa [evmAfterFee] using hfitSupplySource)
    (by simpa [evmAfterFee] using hsourceOverflow) rd3762 hclean0 hclean1
    hruntimeSupplyFit hruntimeOverflow hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastNonzeroUpdateBoundFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σCleared σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 : typedCallViaEVM config
      (uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (EVM.address
        (uniswapAddressAtSlot
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
      "balanceOf" 0
      [.address
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
      (true, evm0S, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcleared : sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩ = σCleared)
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σCleared I = totalSupply)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hcase :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩ ∧
      mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
      totalSupply ≠ ⟨0⟩ ∧
      amount0.toNat * totalSupply.toNat < UInt256.size ∧
      amount1.toNat * totalSupply.toNat < UInt256.size ∧
      reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
      liquidity =
        minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) ∧
      liquidity ≠ ⟨0⟩ ∧
      mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFeeS) liquidity <
        UInt256.size ∧
      mintFunctionToBalanceNewNat (mintFeeKLastClearedState evmFeeS)
        (AccountAddress.ofNat (mintToWord I).toNat) liquidity < UInt256.size ∧
      (uniswapSlotWord ⟨0⟩ σCleared I).toNat + liquidity.toNat < UInt256.size ∧
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σCleared I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (feeToStaticcallMem
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            outFee))).toNat + liquidity.toNat < UInt256.size ∧
      (reserve112Mask.toNat < balance0.toNat ∨
        balance0.toNat ≤ reserve112Mask.toNat ∧ reserve112Mask.toNat < balance1.toNat)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with
    ⟨hfeeToZero, hkLastNonzero, htotalNonzero, hmulFit0, hmulFit1,
      hreserve0Nonzero, hreserve1Nonzero, hliquidity, hliqNonzero, hfitSupplySource,
      hfitBalanceSource, hruntimeSupplyFit, hruntimeBalanceFit, hupdateBound⟩
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hPostCleared : accountMapEquiv σCleared evmAfterFee.accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩ hPostAccountsFee
    simpa [evmAfterFee, ← hcleared, mintFeeKLastClearedState, henvFeeI,
      storageStore_accountMap] using hstore
  have henvCleared : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
  have htotalEq : mintFunctionTotalSupplyWord evmAfterFee = totalSupply := by
    have hword := mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPostCleared
      henvCleared
    simpa [htotalSlot] using hword
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve1]
      dsimp [reserve1Word]
      exact reserve112Word_lt _)
  obtain ⟨k3701, C3701, rd3701Raw⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero hperm
      hkLastNonzero
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σCleared) k3701 C3701 := by
    simpa [hruntimeReserve0, hruntimeReserve1, hcleared] using rd3701Raw
  have hmem :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).size = 164 :=
    feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool false])
  have hreserve0Eq' : uniswapReserve0Word evmL = reserve0 := by
    simpa [evmL, evmS] using hreserve0Eq
  have hreserve1Eq' : uniswapReserve1Word evmL = reserve1 := by
    simpa [evmL, evmS] using hreserve1Eq
  have hamount0Eq' : mintAmount0Word evmL balance0 = amount0 := by
    simpa [evmL, evmS] using hamount0Eq
  have hamount1Eq' : mintAmount1Word evmL balance1 = amount1 := by
    simpa [evmL, evmS] using hamount1Eq
  have hfee :
      ExecStmt config
        { contract := contract,
          locals :=
            mintAmountStore (uniswapLockEnteredState evmS) I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmAfterFee) := by
    simpa [nextFrame, evmL, evmS, evmAfterFee, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbase :
      nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false
  have hto :
      nextFrame.locals.get? "to" = some (.address (AccountAddress.ofNat (mintToWord I).toNat)) := by
    simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false
  have hamount0 :
      nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, hamount0Eq', mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false
  have hamount1 :
      nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, hamount1Eq', mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false
  have hbalance0 :
      nextFrame.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 false
  have hbalance1 :
      nextFrame.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 false
  have hreserve0 :
      nextFrame.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    simpa [nextFrame, evmL, evmS, hreserve0Eq'] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false
  have hreserve1 :
      nextFrame.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    simpa [nextFrame, evmL, evmS, hreserve1Eq'] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false
  rcases hupdateBound with hfail0 | ⟨hfit0, hfail1⟩
  · exact uniswapMintProportionalUpdateFirstBoundFromAfterFeeCase
      nextFrame.locals (AccountAddress.ofNat (mintToWord I).toNat)
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
      hdec1 hle0Source hle1Source hfee hbase hto hamount0 hamount1 hbalance0 hbalance1
      hreserve0 hreserve1 htotalEq htotalSlot htotalNonzero hmulFit0 hmulFit1
      hreserve0Nonzero hreserve1Nonzero (by simpa using hliquidity) hliqNonzero
      (by simpa [evmAfterFee] using hfitSupplySource)
      (by simpa [evmAfterFee] using hfitBalanceSource) hperm rd3701 hclean0 hclean1
      hruntimeSupplyFit hruntimeBalanceFit hfail0 hmem hmem64
  · exact uniswapMintProportionalUpdateSecondBoundFromAfterFeeCase
      nextFrame.locals (AccountAddress.ofNat (mintToWord I).toNat)
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
      hdec1 hle0Source hle1Source hfee hbase hto hamount0 hamount1 hbalance0 hbalance1
      hreserve0 hreserve1 htotalEq htotalSlot htotalNonzero hmulFit0 hmulFit1
      hreserve0Nonzero hreserve1Nonzero (by simpa using hliquidity) hliqNonzero
      (by simpa [evmAfterFee] using hfitSupplySource)
      (by simpa [evmAfterFee] using hfitBalanceSource) hperm rd3701 hclean0 hclean1
      hruntimeSupplyFit hruntimeBalanceFit hfit0 hfail1 hmem hmem64

end UniswapV2Pair

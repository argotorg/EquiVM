import Examples.UniswapV2Pair.MintInitialCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialSmallRootRevertsFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (feeTo : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
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
    (hperm : I.perm = true)
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
    (hsmall :
      (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
            solcAddrMask =
          ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
        uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
        amount0.toNat * amount1.toNat < UInt256.size ∧
        (UInt256.mul amount0 amount1).toNat ≤ 3) ∨
      (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
            solcAddrMask ≠
          ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
        uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
        amount0.toNat * amount1.toNat < UInt256.size ∧
        (UInt256.mul amount0 amount1).toNat ≤ 3) ∨
      (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
            solcAddrMask =
          ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
        uniswapSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I =
          ⟨0⟩ ∧
        amount0.toNat * amount1.toNat < UInt256.size ∧
        (UInt256.mul amount0 amount1).toNat ≤ 3)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
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
  rcases hsmall with hsmallOff | hsmallRest
  · rcases hsmallOff with ⟨hfeeToZero, hkLastZero, htotalZero, hfit, hsmall⟩
    have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
      rw [hfeeToEq]
      exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
        (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
    have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
      rw [hkLastEq, hkLastZero]
      rfl
    have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
      rw [htotalEq, htotalZero]
    have hfitSource :
        mintAmountProductNat
            (mintAmount0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0)
            (mintAmount1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1) <
          UInt256.size := by
      simpa [mintAmountProductNat, hamount0Eq, hamount1Eq] using hfit
    have hsmallSource :
        (mintAmountProductWord
            (mintAmount0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0)
            (mintAmount1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1)).toNat ≤
          3 := by
      rw [mintAmountProductWord_eq_mul _ _ hfitSource]
      simpa [hamount0Eq, hamount1Eq] using hsmall
    obtain ⟨_, _, rd3701⟩ :=
      uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
        rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero
        hkLastZero
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (mintStore I)
          mintTransition.body .reverted := by
      exact ExecFuncBody.execBlockRevert
        (uniswapMintInitialSmallRootReverts_feeOff_kLastZero
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) evm0S evm1S evmFeeS I
          feeTo (by simp only [initState]; exact hwv) hunlockedSolm hguard0 hguard1
          hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
          hfeeToAddr hkLastSource htotalSource hfitSource hsmallSource)
    exact (uniswapMintRuntimeAfterMintFeeInitialSmallRootReverts
        rd3701 htotalZero hfit hsmall hmem hmem64)
      |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
  · rcases hsmallRest with hsmallOn | hsmallOffCleared
    · rcases hsmallOn with ⟨hfeeToNonzero, hkLastZero, htotalZero, hfit, hsmall⟩
      have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
        rw [hfeeToEq]
        exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
          (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToNonzero
      have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
        rw [hkLastEq, hkLastZero]
        rfl
      have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
        rw [htotalEq, htotalZero]
      have hfitSource :
          mintAmountProductNat
              (mintAmount0Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0)
              (mintAmount1Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1) <
            UInt256.size := by
        simpa [mintAmountProductNat, hamount0Eq, hamount1Eq] using hfit
      have hsmallSource :
          (mintAmountProductWord
              (mintAmount0Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0)
              (mintAmount1Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1)).toNat ≤
            3 := by
        rw [mintAmountProductWord_eq_mul _ _ hfitSource]
        simpa [hamount0Eq, hamount1Eq] using hsmall
      obtain ⟨_, _, rd3701⟩ :=
        uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
          rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToNonzero
          hkLastZero
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (mintStore I)
            mintTransition.body .reverted := by
        exact ExecFuncBody.execBlockRevert
          (uniswapMintInitialSmallRootReverts_feeOn_kLastZero
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) evm0S evm1S
            evmFeeS I feeTo (by simp only [initState]; exact hwv) hunlockedSolm hguard0
            hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall
            hfeeDec hfeeToAddr hkLastSource htotalSource hfitSource hsmallSource)
      exact (uniswapMintRuntimeAfterMintFeeInitialSmallRootReverts
          rd3701 htotalZero hfit hsmall hmem hmem64)
        |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
    · rcases hsmallOffCleared with
        ⟨hfeeToZero, hkLastNonzero, htotalZero, hfit, hsmall⟩
      have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
        rw [hfeeToEq]
        exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
          (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
      have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
        intro hzero
        apply hkLastNonzero
        rw [← hkLastEq]
        exact uint256_toNat_eq_zero hzero
      have hPostCleared :
          accountMapEquiv (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩)
            (mintFeeKLastClearedState evmFeeS).accountMap := by
        have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩
          hPostAccountsFee
        simpa [mintFeeKLastClearedState, henvFeeI, storageStore_accountMap] using hstore
      have henvCleared : (mintFeeKLastClearedState evmFeeS).executionEnv = I := by
        simp [mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
      have htotalEqCleared :
          mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFeeS) =
            uniswapSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I :=
        mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPostCleared henvCleared
      have htotalSource : mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFeeS) =
          ⟨0⟩ := by
        rw [htotalEqCleared, htotalZero]
      have hfitSource :
          mintAmountProductNat
              (mintAmount0Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0)
              (mintAmount1Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1) <
            UInt256.size := by
        simpa [mintAmountProductNat, hamount0Eq, hamount1Eq] using hfit
      have hsmallSource :
          (mintAmountProductWord
              (mintAmount0Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0)
              (mintAmount1Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1)).toNat ≤
            3 := by
        rw [mintAmountProductWord_eq_mul _ _ hfitSource]
        simpa [hamount0Eq, hamount1Eq] using hsmall
      obtain ⟨_, _, rd3701⟩ :=
        uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
          rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero
          hperm hkLastNonzero
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (mintStore I)
            mintTransition.body .reverted := by
        exact ExecFuncBody.execBlockRevert
          (uniswapMintInitialSmallRootReverts_feeOff_kLastNonzero
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) evm0S evm1S
            evmFeeS I feeTo (by simp only [initState]; exact hwv) hunlockedSolm hguard0
            hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall
            hfeeDec hfeeToAddr hkLastSource htotalSource hfitSource hsmallSource)
      exact (uniswapMintRuntimeAfterMintFeeInitialSmallRootReverts
          rd3701 htotalZero hfit hsmall hmem hmem64)
        |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

end UniswapV2Pair

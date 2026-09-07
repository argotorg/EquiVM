import Examples.UniswapV2Pair.MintProportionalFactoryArithmetic
import Examples.UniswapV2Pair.MintProportionalSecondMintReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapMintProportionalFeeOnKLastZeroUpdateBoundsFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {liquidity totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    {zFee : Bool}
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) = reserve1)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
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
    (hfeeToNonzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity : liquidity = minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
      ((amount1.mul totalSupply).div reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size)
    (hfitBalanceSource : mintFunctionToBalanceNewNat evmFeeS
      (AccountAddress.ofNat (mintToWord I).toNat) liquidity < UInt256.size)
    (htotalFit : totalSupply.toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord
          (feeToStaticcallMem
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            outFee))).toNat + liquidity.toNat < UInt256.size) :
    (balance0.toNat ≤ reserve112Mask.toNat ∧ balance1.toNat ≤ reserve112Mask.toNat) ∨
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  let memFee :=
    feeToStaticcallMem
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      outFee
  have hmem : memFee.size = 164 := by
    dsimp [memFee]
    exact feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFee]
    exact feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToNonzero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  obtain ⟨_, _, rd3701⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToNonzero
      hkLastZero
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmFeeS) := by
    simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true
  have hamount0Get : nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  have hamount1Get :
      nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true
  have hreserve0Get :
      nextFrame.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    simpa [nextFrame, evmL, evmS, hreserve0Eq] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true
  have hreserve1Get :
      nextFrame.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    simpa [nextFrame, evmL, evmS, hreserve1Eq] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve1]
      dsimp [reserve1Word]
      exact reserve112Word_lt _)
  have htoGet : nextFrame.locals.get? "to" =
      some (.address (AccountAddress.ofNat (mintToWord I).toNat)) := by
    exact mintAfterMintFeeCallStore_to evmL I balance0 balance1 true
  have hbalance0Get : nextFrame.locals.get? "balance0" =
      some (uniswapUint256Value balance0) := by
    exact mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true
  have hbalance1Get : nextFrame.locals.get? "balance1" =
      some (uniswapUint256Value balance1) := by
    exact mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true
  by_cases hbound0 : balance0.toNat ≤ reserve112Mask.toNat
  · by_cases hbound1 : balance1.toNat ≤ reserve112Mask.toNat
    · exact Or.inl ⟨hbound0, hbound1⟩
    · exact Or.inr (uniswapMintProportionalUpdateSecondBoundFromAfterFeeCase nextFrame.locals
        (AccountAddress.ofNat (mintToWord I).toNat)
        hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfee hbase htoGet hamount0Get hamount1Get
        hbalance0Get hbalance1Get hreserve0Get hreserve1Get htotalEq htotalSlot
        htotalNonzero hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity
        hliqNonzero hfitSupply hfitBalanceSource hperm
        (by simpa [hruntimeReserve0, hruntimeReserve1] using rd3701) hclean0 hclean1
        (by simpa only [htotalSlot] using htotalFit)
        (by simpa only [htotalSlot] using hbalanceFit)
        hbound0 (Nat.lt_of_not_ge hbound1) hmem hmem64)
  · exact Or.inr (uniswapMintProportionalUpdateFirstBoundFromAfterFeeCase nextFrame.locals
      (AccountAddress.ofNat (mintToWord I).toNat)
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source hfee hbase htoGet hamount0Get hamount1Get
      hbalance0Get hbalance1Get hreserve0Get hreserve1Get htotalEq htotalSlot
      htotalNonzero hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity
      hliqNonzero hfitSupply hfitBalanceSource hperm
      (by simpa [hruntimeReserve0, hruntimeReserve1] using rd3701) hclean0 hclean1
      (by simpa only [htotalSlot] using htotalFit)
      (by simpa only [htotalSlot] using hbalanceFit)
      (Nat.lt_of_not_ge hbound0) hmem hmem64)

end UniswapV2Pair

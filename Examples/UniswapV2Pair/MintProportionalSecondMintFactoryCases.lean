import Examples.UniswapV2Pair.MintProportionalSecondMintFactoryKLastNonzeroReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

def mintProportionalSecondMintOverflowCase
    (feeToWord totalSupply totalSupplyCleared amount0 amount1 balance0 balance1 reserve0 reserve1
      liquidity liquidityCleared : UInt256)
    (σFee σCleared : AccountMap) (evmFeeS : EVM.State) (I : ExecutionEnv)
    (toWord : UInt256) (memFee : ByteArray) : Prop :=
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
    totalSupply ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupply.toNat < UInt256.size ∧
    amount1.toNat * totalSupply.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidity = minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
      ((amount1.mul totalSupply).div reserve1) ∧
    liquidity ≠ ⟨0⟩ ∧
    UInt256.size ≤ mintFunctionTotalSupplyNewNat evmFeeS liquidity ∧
    UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat) ∨
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
    totalSupply ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupply.toNat < UInt256.size ∧
    amount1.toNat * totalSupply.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidity = minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
      ((amount1.mul totalSupply).div reserve1) ∧
    liquidity ≠ ⟨0⟩ ∧
    mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size ∧
    UInt256.size ≤ mintFunctionToBalanceNewNat evmFeeS
      (AccountAddress.ofNat (mintToWord I).toNat) liquidity ∧
    (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size ∧
    UInt256.size ≤
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat) ∨
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
    totalSupply ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupply.toNat < UInt256.size ∧
    amount1.toNat * totalSupply.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidity = minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
      ((amount1.mul totalSupply).div reserve1) ∧
    liquidity ≠ ⟨0⟩ ∧
    mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size ∧
    mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
      liquidity < UInt256.size ∧
    (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size ∧
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat <
        UInt256.size ∧
    (reserve112Mask.toNat < balance0.toNat ∨
      balance0.toNat ≤ reserve112Mask.toNat ∧ reserve112Mask.toNat < balance1.toNat)) ∨
  (UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
    totalSupply ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupply.toNat < UInt256.size ∧
    amount1.toNat * totalSupply.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidity = minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
      ((amount1.mul totalSupply).div reserve1) ∧
    liquidity ≠ ⟨0⟩ ∧
    UInt256.size ≤ mintFunctionTotalSupplyNewNat evmFeeS liquidity ∧
    UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat) ∨
  (UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
    totalSupply ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupply.toNat < UInt256.size ∧
    amount1.toNat * totalSupply.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidity = minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
      ((amount1.mul totalSupply).div reserve1) ∧
    liquidity ≠ ⟨0⟩ ∧
    mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size ∧
    UInt256.size ≤ mintFunctionToBalanceNewNat evmFeeS
      (AccountAddress.ofNat (mintToWord I).toNat) liquidity ∧
    (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size ∧
    UInt256.size ≤
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat) ∨
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    totalSupplyCleared ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupplyCleared.toNat < UInt256.size ∧
    amount1.toNat * totalSupplyCleared.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidityCleared = minFunctionResultWord ((amount0.mul totalSupplyCleared).div reserve0)
      ((amount1.mul totalSupplyCleared).div reserve1) ∧
    liquidityCleared ≠ ⟨0⟩ ∧
    UInt256.size ≤ mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFeeS)
      liquidityCleared ∧
    UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σCleared I).toNat + liquidityCleared.toNat) ∨
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    totalSupplyCleared ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupplyCleared.toNat < UInt256.size ∧
    amount1.toNat * totalSupplyCleared.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidityCleared = minFunctionResultWord ((amount0.mul totalSupplyCleared).div reserve0)
      ((amount1.mul totalSupplyCleared).div reserve1) ∧
    liquidityCleared ≠ ⟨0⟩ ∧
    mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFeeS) liquidityCleared <
      UInt256.size ∧
    UInt256.size ≤ mintFunctionToBalanceNewNat (mintFeeKLastClearedState evmFeeS)
      (AccountAddress.ofNat (mintToWord I).toNat) liquidityCleared ∧
    (uniswapSlotWord ⟨0⟩ σCleared I).toNat + liquidityCleared.toNat < UInt256.size ∧
    UInt256.size ≤
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σCleared I + liquidityCleared))
        (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidityCleared.toNat)
    ∨
  (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    totalSupplyCleared ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupplyCleared.toNat < UInt256.size ∧
    amount1.toNat * totalSupplyCleared.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidityCleared = minFunctionResultWord ((amount0.mul totalSupplyCleared).div reserve0)
      ((amount1.mul totalSupplyCleared).div reserve1) ∧
    liquidityCleared ≠ ⟨0⟩ ∧
    mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFeeS) liquidityCleared <
      UInt256.size ∧
    mintFunctionToBalanceNewNat (mintFeeKLastClearedState evmFeeS)
      (AccountAddress.ofNat (mintToWord I).toNat) liquidityCleared < UInt256.size ∧
    (uniswapSlotWord ⟨0⟩ σCleared I).toNat + liquidityCleared.toNat < UInt256.size ∧
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σCleared I + liquidityCleared))
      (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidityCleared.toNat <
        UInt256.size ∧
    (reserve112Mask.toNat < balance0.toNat ∨
      balance0.toNat ≤ reserve112Mask.toNat ∧ reserve112Mask.toNat < balance1.toNat))

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalSecondMintOverflowFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σCleared σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply totalSupplyCleared amount0 amount1 balance0 balance1 reserve0 reserve1
      liquidity liquidityCleared toWord sel : UInt256}
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalClearedSlot : uniswapSlotWord ⟨0⟩ σCleared I = totalSupplyCleared)
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
      mintProportionalSecondMintOverflowCase
        (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
        totalSupply totalSupplyCleared amount0 amount1 balance0 balance1 reserve0 reserve1
        liquidity liquidityCleared σFee σCleared evmFeeS I toWord
        (feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  unfold mintProportionalSecondMintOverflowCase at hcase
  rcases hcase with hfeeOffTotal | hrest
  · exact uniswapMintProportionalFeeOffKLastZeroSecondMintTotalSupplyOverflowFromFactoryCase
      feeTo hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq rd7781
      ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalEq
      htotalSlot hruntimeReserve0 hruntimeReserve1 hreserve0Eq hreserve1Eq hamount0Eq
      hamount1Eq hfeeOffTotal
  · rcases hrest with hfeeOffBalance | hrest
    · exact uniswapMintProportionalFeeOffKLastZeroSecondMintBalanceOverflowFromFactoryCase
        feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0
        hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq rd7781
        ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalEq
        htotalSlot hruntimeReserve0 hruntimeReserve1 hreserve0Eq hreserve1Eq hamount0Eq
        hamount1Eq hfeeOffBalance
    · rcases hrest with hfeeOffUpdate | hrest
      · exact uniswapMintProportionalFeeOffKLastZeroUpdateBoundFromFactoryCases
          feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0
          hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
          hfeeToEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
          hkLastEq htotalEq htotalSlot hruntimeReserve0 hruntimeReserve1 hreserve0Eq
          hreserve1Eq hamount0Eq hamount1Eq hfeeOffUpdate
      · rcases hrest with hfeeOnTotal | hrest
        · exact uniswapMintProportionalFeeOnKLastZeroSecondMintTotalSupplyOverflowFromFactoryCase
            feeTo hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0
            hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hfeeToEq
            rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq
            htotalEq htotalSlot hruntimeReserve0 hruntimeReserve1 hreserve0Eq hreserve1Eq
            hamount0Eq hamount1Eq hfeeOnTotal
        · rcases hrest with hfeeOnBalance | hrest
          · exact uniswapMintProportionalFeeOnKLastZeroSecondMintBalanceOverflowFromFactoryCase
              feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0
              hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
              hfeeToEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
              hkLastEq htotalEq htotalSlot hruntimeReserve0 hruntimeReserve1 hreserve0Eq
              hreserve1Eq hamount0Eq hamount1Eq hfeeOnBalance
          · rcases hrest with hfeeOffClearedTotal | hrest
            · exact
                uniswapMintProportionalFeeOffKLastNonzeroSecondMintTotalSupplyOverflowFromFactoryCase
                  feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1
                  hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall
                  hfeeDec hfeeToEq hPostAccountsFee henvFeeI hcleared rd7781 ho32 hoSize
                  ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalClearedSlot
                  hruntimeReserve0 hruntimeReserve1 hreserve0Eq hreserve1Eq hamount0Eq
                  hamount1Eq hfeeOffClearedTotal
            · rcases hrest with hfeeOffClearedBalance | hfeeOffClearedUpdate
              · exact
                  uniswapMintProportionalFeeOffKLastNonzeroSecondMintBalanceOverflowFromFactoryCase
                    feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1
                    hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall
                    hfeeDec hfeeToEq hPostAccountsFee henvFeeI hcleared rd7781 ho32 hoSize
                    ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalClearedSlot
                    hruntimeReserve0 hruntimeReserve1 hreserve0Eq hreserve1Eq hamount0Eq
                    hamount1Eq hfeeOffClearedBalance
              · exact
                  uniswapMintProportionalFeeOffKLastNonzeroUpdateBoundFromFactoryCases
                    feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1
                    hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall
                    hfeeDec hfeeToEq hPostAccountsFee henvFeeI hcleared rd7781 ho32 hoSize
                    ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalClearedSlot
                    hruntimeReserve0 hruntimeReserve1 hreserve0Eq hreserve1Eq hamount0Eq
                    hamount1Eq hfeeOffClearedUpdate

end UniswapV2Pair

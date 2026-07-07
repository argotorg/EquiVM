import Examples.UniswapV2Pair.MintFeeOnKLastNonzeroInitialFactoryCases
import Examples.UniswapV2Pair.MintInitialFactoryOverflowCases
import Examples.UniswapV2Pair.MintInitialFactorySecondMintReverts
import Examples.UniswapV2Pair.MintInitialFactorySecondMintBalanceReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

def mintFeeOnKLastNonzeroInitialMinimumBalanceOverflowFromFactoryCaseData
    (feeToWord reserve0 reserve1 amount0 amount1 : UInt256) (σFee : AccountMap)
    (evmFeeS : EVM.State) (I : ExecutionEnv) (memFee : ByteArray) : Prop :=
  mintFeeOnKLastNonzeroNoFeeLiquidityFromFactoryCaseData feeToWord reserve0 reserve1
      σFee evmFeeS I ∧
    uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
    amount0.toNat * amount1.toNat < UInt256.size ∧
    UInt256.size ≤
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩ memFee)).toNat +
        (⟨1000⟩ : UInt256).toNat

def mintFeeOnKLastNonzeroInitialSecondMintTotalSupplyOverflowFromFactoryCaseData
    (feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 : UInt256)
    (σFee : AccountMap) (evmFeeS evmL : EVM.State) (I : ExecutionEnv)
    (memFee : ByteArray) : Prop :=
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  let afterTotalSupplyLocals :=
    nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  mintFeeOnKLastNonzeroNoFeeLiquidityFromFactoryCaseData feeToWord reserve0 reserve1
      σFee evmFeeS I ∧
    uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
    amount0.toNat * amount1.toNat < UInt256.size ∧
    ∀ rootLiquidity : Int,
      ExecStmt config caller evmFeeS
          (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
            "rootLiquidity")
          (.ok (resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity]))
            evmFeeS) →
      0 ≤ rootLiquidity → rootLiquidity.toNat < UInt256.size →
      let liquidity := UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat
      minimumLiquidity ≤ rootLiquidity ∧
        liquidity ≠ ⟨0⟩ ∧
        mintFunctionTotalSupplyNewNat evmFeeS (⟨1000⟩ : UInt256) < UInt256.size ∧
        mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat 0)
            (⟨1000⟩ : UInt256) <
          UInt256.size ∧
        (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat <
          UInt256.size ∧
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ memFee)).toNat +
            (⟨1000⟩ : UInt256).toNat <
          UInt256.size ∧
        UInt256.size ≤
          mintFunctionTotalSupplyNewNat
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
              (⟨1000⟩ : UInt256))
            liquidity ∧
        (let σAfterMinimum :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩
              (uniswapInternalMintBalanceHashMem ⟨0⟩ memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
              (uniswapInternalMintBalanceHashSlot ⟨0⟩ memFee) + (⟨1000⟩ : UInt256))
        UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat)

def mintFeeOnKLastNonzeroInitialSecondMintBalanceOverflowFromFactoryCaseData
    (feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 : UInt256)
    (σFee : AccountMap) (evmFeeS evmL : EVM.State) (I : ExecutionEnv)
    (memFee : ByteArray) : Prop :=
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  let afterTotalSupplyLocals :=
    nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  mintFeeOnKLastNonzeroNoFeeLiquidityFromFactoryCaseData feeToWord reserve0 reserve1
      σFee evmFeeS I ∧
    uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
    amount0.toNat * amount1.toNat < UInt256.size ∧
    ∀ rootLiquidity : Int,
      ExecStmt config caller evmFeeS
          (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
            "rootLiquidity")
          (.ok (resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity]))
            evmFeeS) →
      0 ≤ rootLiquidity → rootLiquidity.toNat < UInt256.size →
      let liquidity := UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat
      minimumLiquidity ≤ rootLiquidity ∧
        liquidity ≠ ⟨0⟩ ∧
        mintFunctionTotalSupplyNewNat evmFeeS (⟨1000⟩ : UInt256) < UInt256.size ∧
        mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat 0)
            (⟨1000⟩ : UInt256) <
          UInt256.size ∧
        (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat <
          UInt256.size ∧
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ memFee)).toNat +
            (⟨1000⟩ : UInt256).toNat <
          UInt256.size ∧
        mintFunctionTotalSupplyNewNat
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
              (⟨1000⟩ : UInt256))
            liquidity <
          UInt256.size ∧
        UInt256.size ≤
          mintFunctionToBalanceNewNat
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
              (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity ∧
        (let σAfterMinimum :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩
              (uniswapInternalMintBalanceHashMem ⟨0⟩ memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
              (uniswapInternalMintBalanceHashSlot ⟨0⟩ memFee) + (⟨1000⟩ : UInt256))
        (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat <
          UInt256.size) ∧
        (let minimumMem :=
          uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
            (uniswapInternalMintBalanceHashMem ⟨0⟩
              (uniswapInternalMintBalanceHashMem ⟨0⟩ memFee))
        let σAfterMinimum :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩
              (uniswapInternalMintBalanceHashMem ⟨0⟩ memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
              (uniswapInternalMintBalanceHashSlot ⟨0⟩ memFee) + (⟨1000⟩ : UInt256))
        UInt256.size ≤
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem)).toNat +
            liquidity.toNat)

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroInitialMinimumBalanceOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
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
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hcase :
      mintFeeOnKLastNonzeroInitialMinimumBalanceOverflowFromFactoryCaseData feeToWord
        reserve0 reserve1 amount0 amount1 σFee evmFeeS I memFee) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  rcases hcase with ⟨hprefixCase, htotalZero, hfit, hbalanceOverflow⟩
  obtain ⟨k3701, C3701, hfee, rd3701, hmem, hmem64⟩ :=
    uniswapMintFeeOnKLastNonzeroNoFeeLiquidityPrefixFromFactory feeTo hfeeGuard hfeeCall
      hfeeDec hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hkLastEq
      htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
      hfeeToWord hfeeTo htoWord hmemFee hprefixCase
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true
  have hamount0Get : nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true
  have hamount1Get : nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true
  exact uniswapMintInitialMinimumMintBalanceOverflowFromAfterFeeCase nextFrame.locals
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
    hle0Source hle1Source (by simpa [evmL, evmS] using hfee) hbase hamount0Get
    hamount1Get hPostAccountsFee henvFeeI htotalSource htotalZero hfit rd3701
    hbalanceOverflow hperm hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroInitialSecondMintTotalSupplyOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
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
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hcase :
      mintFeeOnKLastNonzeroInitialSecondMintTotalSupplyOverflowFromFactoryCaseData
        feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 σFee evmFeeS
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        I memFee) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  let afterTotalSupplyLocals :=
    nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  rcases hcase with ⟨hprefixCase, htotalZero, hfit, hfinish⟩
  obtain ⟨k3701, C3701, hfee, rd3701, hmem, hmem64⟩ :=
    uniswapMintFeeOnKLastNonzeroNoFeeLiquidityPrefixFromFactory feeTo hfeeGuard hfeeCall
      hfeeDec hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hkLastEq
      htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
      hfeeToWord hfeeTo htoWord hmemFee hprefixCase
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true
  have hto :
      nextFrame.locals.get? "to" =
        some (.address (AccountAddress.ofNat (mintToWord I).toNat)) := by
    simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true
  have hamount0Get :
      nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true
  have hamount1Get :
      nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true
  have hamount0After :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))).get? "amount0" =
        some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0Get]
  have hamount1After :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))).get? "amount1" =
        some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1Get]
  have hargs :
      evalExprs? config caller evmFeeS
        [u256 (.binary .mul (.var "amount0") (.var "amount1"))] =
          .ok [sqrtFunctionYValue (mintAmountProductWord amount0 amount1)] := by
    simpa [caller] using
      evalExprs_mint_initialSqrtArg_of_get evmFeeS amount0 amount1 hamount0After
        hamount1After (by simpa [mintAmountProductNat] using hfit)
  obtain ⟨root, k2531, C2531, hsqrt, hrootNonneg, hrootSize, rd2531⟩ :=
    mintInitialLiquiditySqrtPrefixRuntimeBounded
      (caller := caller) (evm := evmFeeS) rfl hargs rd3701 htotalZero
      (by simpa [mintAmountProductNat] using hfit)
  have hfinishRoot :=
    hfinish root (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS] using hsqrt)
      hrootNonneg hrootSize
  rcases hfinishRoot with
    ⟨hrootGeMin, hliqNonzero, hfitSupplyMinSource, hfitBalanceMinSource,
      htotalFitMin, hbalanceFitMin, hsourceOverflow, hruntimeOverflow⟩
  exact
    uniswapMintInitialAfterMintFeeSecondMintTotalSupplyOverflowRevertCase
      nextFrame.locals root (AccountAddress.ofNat (mintToWord I).toNat)
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
      hdec1 hle0Source hle1Source (by simpa [evmL, evmS] using hfee) hbase hto
      htotalSource
      (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS, htotalSource]
        using hsqrt)
      rd2531 hrootSize hrootGeMin rfl hliqNonzero hfitSupplyMinSource
      hfitBalanceMinSource htotalFitMin hbalanceFitMin hsourceOverflow
      (by simpa [htoWord] using hruntimeOverflow) hperm hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroInitialSecondMintBalanceOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
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
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hcase :
      mintFeeOnKLastNonzeroInitialSecondMintBalanceOverflowFromFactoryCaseData
        feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 σFee evmFeeS
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        I memFee) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  let afterTotalSupplyLocals :=
    nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  rcases hcase with ⟨hprefixCase, htotalZero, hfit, hfinish⟩
  obtain ⟨k3701, C3701, hfee, rd3701, hmem, hmem64⟩ :=
    uniswapMintFeeOnKLastNonzeroNoFeeLiquidityPrefixFromFactory feeTo hfeeGuard hfeeCall
      hfeeDec hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hkLastEq
      htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
      hfeeToWord hfeeTo htoWord hmemFee hprefixCase
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true
  have hto :
      nextFrame.locals.get? "to" =
        some (.address (AccountAddress.ofNat (mintToWord I).toNat)) := by
    simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true
  have hamount0Get :
      nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true
  have hamount1Get :
      nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true
  have hamount0After :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))).get? "amount0" =
        some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0Get]
  have hamount1After :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))).get? "amount1" =
        some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1Get]
  have hargs :
      evalExprs? config caller evmFeeS
        [u256 (.binary .mul (.var "amount0") (.var "amount1"))] =
          .ok [sqrtFunctionYValue (mintAmountProductWord amount0 amount1)] := by
    simpa [caller] using
      evalExprs_mint_initialSqrtArg_of_get evmFeeS amount0 amount1 hamount0After
        hamount1After (by simpa [mintAmountProductNat] using hfit)
  obtain ⟨root, k2531, C2531, hsqrt, hrootNonneg, hrootSize, rd2531⟩ :=
    mintInitialLiquiditySqrtPrefixRuntimeBounded
      (caller := caller) (evm := evmFeeS) rfl hargs rd3701 htotalZero
      (by simpa [mintAmountProductNat] using hfit)
  have hfinishRoot :=
    hfinish root (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS] using hsqrt)
      hrootNonneg hrootSize
  rcases hfinishRoot with
    ⟨hrootGeMin, hliqNonzero, hfitSupplyMinSource, hfitBalanceMinSource,
      htotalFitMin, hbalanceFitMin, hfitSupplySource, hsourceOverflow,
      hruntimeSupplyFit, hruntimeOverflow⟩
  exact
    uniswapMintInitialAfterMintFeeSecondMintBalanceOverflowRevertCase
      nextFrame.locals root (AccountAddress.ofNat (mintToWord I).toNat)
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
      hdec1 hle0Source hle1Source (by simpa [evmL, evmS] using hfee) hbase hto
      htotalSource
      (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS, htotalSource]
        using hsqrt)
      rd2531 hrootSize hrootGeMin rfl hliqNonzero hfitSupplyMinSource
      hfitBalanceMinSource htotalFitMin hbalanceFitMin hfitSupplySource hsourceOverflow
      (by simpa [htoWord] using hruntimeSupplyFit)
      (by simpa [htoWord] using hruntimeOverflow) hperm hmem hmem64

def mintFeeOnKLastNonzeroInitialOverflowFromFactoryCasesData
    (feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 : UInt256)
    (σFee : AccountMap) (evmFeeS evmL : EVM.State) (I : ExecutionEnv)
    (memFee : ByteArray) : Prop :=
  mintFeeOnKLastNonzeroInitialFromFactoryCasesData feeToWord reserve0 reserve1 amount0
      amount1 balance0 balance1 σFee evmFeeS evmL I memFee ∨
    mintFeeOnKLastNonzeroInitialMinimumBalanceOverflowFromFactoryCaseData feeToWord
      reserve0 reserve1 amount0 amount1 σFee evmFeeS I memFee ∨
    mintFeeOnKLastNonzeroInitialSecondMintTotalSupplyOverflowFromFactoryCaseData
      feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 σFee evmFeeS evmL I
      memFee ∨
    mintFeeOnKLastNonzeroInitialSecondMintBalanceOverflowFromFactoryCaseData
      feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 σFee evmFeeS evmL I
      memFee

theorem uniswapMintFeeOnKLastNonzeroInitialOverflowFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hcase :
      mintFeeOnKLastNonzeroInitialOverflowFromFactoryCasesData feeToWord reserve0
        reserve1 amount0 amount1 balance0 balance1 σFee evmFeeS
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        I memFee) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hbaseCase | hrest
  · exact
      uniswapMintFeeOnKLastNonzeroInitialFromFactoryCases feeTo hcode hdispatch hsz36
        hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source
        hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee henvFeeI hcreatedFee
        hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0Eq
        hamount1Eq hkLastEq htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
        hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord hmemFee hbaseCase
  rcases hrest with hminimumBalance | hrest
  · exact
      uniswapMintFeeOnKLastNonzeroInitialMinimumBalanceOverflowFromFactoryCase feeTo
        hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0
        hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
        hPostAccountsFee henvFeeI hreserve0Eq hreserve1Eq hruntimeReserve0
        hruntimeReserve1 hamount0Eq hamount1Eq hkLastEq htotalEq rd7781 ho32 hoSize
        ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord
        hmemFee hminimumBalance
  rcases hrest with hsecondTotal | hsecondBalance
  · exact
      uniswapMintFeeOnKLastNonzeroInitialSecondMintTotalSupplyOverflowFromFactoryCase
        feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0
        hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
        hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0Eq
        hamount1Eq hkLastEq htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
        hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord hmemFee hsecondTotal
  · exact
      uniswapMintFeeOnKLastNonzeroInitialSecondMintBalanceOverflowFromFactoryCase
        feeTo hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0
        hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
        hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0Eq
        hamount1Eq hkLastEq htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
        hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord hmemFee hsecondBalance

end UniswapV2Pair

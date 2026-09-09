import Examples.UniswapV2Pair.MintFeeOnKLastNonzeroFactoryCases
import Examples.UniswapV2Pair.MintInitialFactoryReturnCases
import Examples.UniswapV2Pair.MintInitialZeroCases
import Examples.UniswapV2Pair.MintInitialProductOverflow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

def mintFeeOnKLastNonzeroNoFeeLiquidityFromFactoryCaseData
    (feeToWord reserve0 reserve1 : UInt256) (σFee : AccountMap) (evmFeeS : EVM.State)
    (I : ExecutionEnv) : Prop :=
  UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    ((∀ (rootK rootKLast : Int),
        0 ≤ rootK → rootK.toNat < UInt256.size →
        0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
        ¬ rootK > rootKLast) ∨
      UInt256.mul reserve0 reserve1 = ⟨0⟩ ∨
      mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ ∨
      (∀ (rootK rootKLast : Int),
        0 ≤ rootK → rootK.toNat < UInt256.size →
        0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
        rootK > rootKLast ∧
          mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
          mintFeeRootTimesFiveNat rootK < UInt256.size ∧
          mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
          (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
          ¬ mintFeeLiquidityInt evmFeeS rootK rootKLast > 0))

def mintFeeOnKLastNonzeroInitialReturnFromFactoryCaseData
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
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            liquidity <
          UInt256.size ∧
        mintFunctionToBalanceNewNat
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
          UInt256.size ∧
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
        (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size) ∧
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
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem)).toNat +
            liquidity.toNat <
          UInt256.size) ∧
        balance0.toNat ≤ reserve112Mask.toNat ∧
        balance1.toNat ≤ reserve112Mask.toNat ∧
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
        let σAfterMint :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
              (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) minimumMem))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
                (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
              (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem) +
              liquidity)
        UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
          reserve32Mask = ⟨0⟩) ∧
        syncTimeElapsedInt
            (mintFunctionPostState
              (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
                (⟨1000⟩ : UInt256))
              (AccountAddress.ofNat (mintToWord I).toNat) liquidity) =
          0 ∧
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
        let σAfterMint :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
              (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) minimumMem))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
                (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
              (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem) +
              liquidity)
        let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0
        let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
        (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
              reserve112Mask).toNat <
          UInt256.size) ∧
        mintFeeReserveProductNat
            (uniswapReserve0Word
              (syncUpdatePackedReserveState
                (mintFunctionPostState
                  (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
                    (⟨1000⟩ : UInt256))
                  (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
                balance0 balance1))
            (uniswapReserve1Word
            (syncUpdatePackedReserveState
                (mintFunctionPostState
                  (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
                    (⟨1000⟩ : UInt256))
                  (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
                balance0 balance1)) <
          UInt256.size

def mintFeeOnKLastNonzeroInitialZeroFromFactoryCaseData
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
        liquidity = ⟨0⟩ ∧
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
          UInt256.size

def mintFeeOnKLastNonzeroInitialProductOverflowFromFactoryCaseData
    (feeToWord reserve0 reserve1 amount0 amount1 : UInt256) (σFee : AccountMap)
    (evmFeeS : EVM.State) (I : ExecutionEnv) : Prop :=
  mintFeeOnKLastNonzeroNoFeeLiquidityFromFactoryCaseData feeToWord reserve0 reserve1
      σFee evmFeeS I ∧
    uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
    UInt256.size ≤ amount0.toNat * amount1.toNat

def mintFeeOnKLastNonzeroInitialRootUnderflowFromFactoryCaseData
    (feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 : UInt256)
    (σFee : AccountMap) (evmFeeS evmL : EVM.State) (I : ExecutionEnv)
    (_memFee : ByteArray) : Prop :=
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
      rootLiquidity < minimumLiquidity

def mintFeeOnKLastNonzeroInitialFromFactoryCasesData
    (feeToWord reserve0 reserve1 amount0 amount1 balance0 balance1 : UInt256)
    (σFee : AccountMap) (evmFeeS evmL : EVM.State) (I : ExecutionEnv)
    (memFee : ByteArray) : Prop :=
  mintFeeOnKLastNonzeroInitialReturnFromFactoryCaseData feeToWord reserve0 reserve1
      amount0 amount1 balance0 balance1 σFee evmFeeS evmL I memFee ∨
    mintFeeOnKLastNonzeroInitialZeroFromFactoryCaseData feeToWord reserve0 reserve1
      amount0 amount1 balance0 balance1 σFee evmFeeS evmL I memFee ∨
    mintFeeOnKLastNonzeroInitialProductOverflowFromFactoryCaseData feeToWord reserve0
      reserve1 amount0 amount1 σFee evmFeeS I ∨
    mintFeeOnKLastNonzeroInitialRootUnderflowFromFactoryCaseData feeToWord reserve0
      reserve1 amount0 amount1 balance0 balance1 σFee evmFeeS evmL I memFee

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroNoFeeLiquidityPrefixFromFactory
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm1S evmFeeS : EVM.State}
    {outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
      mintFeeOnKLastNonzeroNoFeeLiquidityFromFactoryCaseData feeToWord reserve0 reserve1
        σFee evmFeeS I) :
    ∃ k3701 C3701,
      ExecStmt config
        { contract := contract,
          locals :=
            mintAmountStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
              I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                mintAmountStore
                  (uniswapLockEnteredState
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
                  I balance0 balance1 }
            "feeOn" (some [.bool true]))
          evmFeeS) ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
        [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
          mintToMaskedWord I, ⟨861⟩, sel]
        memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k3701 C3701 ∧
      memFee.size = 164 ∧
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases hcase with ⟨hfeeToNonzero, hkLastNonzero, hrootCase⟩
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeTo]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32)
      (by simpa [hfeeToWord] using hfeeToNonzero)
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    rw [← hruntimeReserve0]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    rw [← hruntimeReserve1]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg, hrootKSize,
      hrootKLastNonneg, hrootKLastSize, rd7899, hrootOutcome⟩ :
      ∃ rootK rootKLast k7899 C7899,
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastSlotWord σFee I))
          evmFeeS
          [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
              "rootK",
            .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
          (.ok
            (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
              (mintFeeKLastSlotWord σFee I) rootK rootKLast)
            evmFeeS) ∧
        0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
        0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
        RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
          [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat,
            mintFeeKLastSlotWord σFee I, feeToWord, ⟨1⟩, reserve1, reserve0,
            ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
            ⟨0⟩, toWord, ⟨861⟩, sel]
          memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k7899 C7899 ∧
        (¬ rootK > rootKLast ∨
          rootK > rootKLast ∧
            mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
            mintFeeRootTimesFiveNat rootK < UInt256.size ∧
            mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
            (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
            ¬ mintFeeLiquidityInt evmFeeS rootK rootKLast > 0) := by
    rcases hrootCase with hnoMint | hrootRest
    · obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
          hrootKSize, hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
        uniswapMintFeeOnKLastNonzeroFactoryRoots feeTo rd7781 ho32 hoSize ho132 ho1Size
          houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee hruntimeReserve0
          hruntimeReserve1 hfeeToNonzero hkLastNonzero hclean0 hclean1
      exact ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
        hrootKSize, hrootKLastNonneg, hrootKLastSize, rd7899,
        Or.inl (hnoMint rootK rootKLast hrootKNonneg hrootKSize hrootKLastNonneg
          hrootKLastSize)⟩
    · rcases hrootRest with hprodZero | hrootRest
      · obtain ⟨rootKLast, k7899, C7899, hprefixRuntime, hrootKLastNonneg,
            hrootKLastSize, rd7899Raw⟩ :=
          uniswapMintFeeOnKLastNonzeroFactoryProductZeroRoots feeTo rd7781 ho32 hoSize
            ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee
            hruntimeReserve0 hruntimeReserve1 hfeeToNonzero hkLastNonzero hclean0 hclean1
            hprodZero
        refine ⟨0, rootKLast, k7899, C7899, by simpa using hprefixRuntime, by omega,
          ?_, hrootKLastNonneg, hrootKLastSize, by simpa using rd7899Raw,
          Or.inl (by omega)⟩
        norm_num [UInt256.size]
      · rcases hrootRest with htotalZero | hpositiveNoLiquidity
        · obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
              hrootKSize, hrootKInput, hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
            uniswapMintFeeOnKLastNonzeroFactoryRootsInput feeTo rd7781 ho32 hoSize ho132
              ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee
              hruntimeReserve0 hruntimeReserve1 hfeeToNonzero hkLastNonzero hclean0
              hclean1
          have hreserve0Lt : reserve0.toNat < 2 ^ 112 := by
            have h := uniswapUint112Masked_lt reserve0
            simpa [hclean0] using h
          have hreserve1Lt : reserve1.toNat < 2 ^ 112 := by
            have h := uniswapUint112Masked_lt reserve1
            simpa [hclean1] using h
          have hprodLt224 : reserve0.toNat * reserve1.toNat < 2 ^ 224 := by
            nlinarith [hreserve0Lt, hreserve1Lt]
          have hprodFit : reserve0.toNat * reserve1.toNat < UInt256.size :=
            lt_trans hprodLt224 (by norm_num [UInt256.size])
          have hmulNat :
              (UInt256.mul reserve0 reserve1).toNat = reserve0.toNat * reserve1.toNat := by
            rw [u256_mul_toNat, Nat.mod_eq_of_lt hprodFit]
          have hrootK224 : rootK.toNat < 2 ^ 224 := by
            rw [hmulNat] at hrootKInput
            exact lt_of_le_of_lt hrootKInput hprodLt224
          have hrootOutcome :
              ¬ rootK > rootKLast ∨
                rootK > rootKLast ∧
                  mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
                  mintFeeRootTimesFiveNat rootK < UInt256.size ∧
                  mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
                  (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
                  ¬ mintFeeLiquidityInt evmFeeS rootK rootKLast > 0 := by
            by_cases hroot : rootK > rootKLast
            · have hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size := by
                have hnumZero : mintFeeNumeratorNat evmFeeS rootK rootKLast = 0 := by
                  simp [mintFeeNumeratorNat, htotalZero]
                rw [hnumZero]
                norm_num [UInt256.size]
              have hrootFiveLt : rootK.toNat * 5 < UInt256.size := by
                have hbound : rootK.toNat * 5 < 5 * 2 ^ 224 := by
                  nlinarith
                exact lt_trans hbound (by norm_num [UInt256.size])
              have hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size := by
                simpa [mintFeeRootTimesFiveNat] using hrootFiveLt
              have hrootFiveWordNat :
                  (mintFeeRootTimesFiveWord rootK).toNat = rootK.toNat * 5 := by
                have hword :=
                  congrArg UInt256.toNat
                    (mintFeeRootTimesFiveWord_eq_mul rootK hrootFiveFit)
                have hmulToNat :
                    (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256)).toNat =
                      rootK.toNat * 5 := by
                  rw [u256_mul_toNat, ulit_toNat' _ hrootKSize,
                    show (⟨5⟩ : UInt256).toNat = 5 from by decide,
                    Nat.mod_eq_of_lt hrootFiveLt]
                simpa [hmulToNat] using hword
              have hlastLeRoot : rootKLast.toNat ≤ rootK.toNat :=
                Int.toNat_le_toNat (by omega)
              have hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size := by
                have hdenLt224 : rootK.toNat * 5 + rootKLast.toNat < 6 * 2 ^ 224 := by
                  nlinarith
                exact lt_trans
                  (by simpa [mintFeeDenominatorNat, hrootFiveWordNat] using hdenLt224)
                  (by norm_num [UInt256.size])
              have hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 := by
                have hrootKPos : 0 < rootK.toNat := by omega
                have hdenNatPos : 0 < mintFeeDenominatorNat rootK rootKLast := by
                  unfold mintFeeDenominatorNat
                  rw [hrootFiveWordNat]
                  nlinarith
                rw [mintFeeDenominatorWord, ulit_toNat' _ hdenFit]
                omega
              exact Or.inr
                ⟨hroot, hnumFit, hrootFiveFit, hdenFit, hdenom,
                  mintFeeLiquidityInt_not_pos_of_totalSupply_zero evmFeeS rootK rootKLast
                    htotalZero⟩
            · exact Or.inl hroot
          exact ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
            hrootKSize, hrootKLastNonneg, hrootKLastSize, rd7899, hrootOutcome⟩
        · obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
              hrootKSize, hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
            uniswapMintFeeOnKLastNonzeroFactoryRoots feeTo rd7781 ho32 hoSize ho132
              ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee
              hruntimeReserve0 hruntimeReserve1 hfeeToNonzero hkLastNonzero hclean0
              hclean1
          exact ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
            hrootKSize, hrootKLastNonneg, hrootKLastSize, rd7899,
            Or.inr (hpositiveNoLiquidity rootK rootKLast hrootKNonneg hrootKSize
              hrootKLastNonneg hrootKLastSize)⟩
  have hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame
          (uniswapReserve0Word evmL) (uniswapReserve1Word evmL)
          feeTo true (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame
            (uniswapReserve0Word evmL) (uniswapReserve1Word evmL)
            feeTo true (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS) := by
    simpa [evmL, evmS, hreserve0Eq, hreserve1Eq, hkLastEq] using hprefixRuntime
  have hmem : memFee.size = 164 := by
    rw [hmemFee]
    exact feeToStaticcallMem_size_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hmem64 :
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemFee]
    exact feeToStaticcallMem_read64_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  rcases hrootOutcome with hrootNoMint | hpositiveNoLiquidity
  · obtain ⟨k3701, C3701, rd3701Raw⟩ :=
      uniswapMintFeeRuntimeAfterRootsNoMintReturnOfInt rootK rootKLast rd7899
        hrootNoMint hrootKSize hrootKLastSize
    have hfee :
        ExecStmt config
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
          (.ok
            (resumeAfterInternalCall
              { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
              "feeOn" (some [.bool true]))
            evmFeeS) := by
      exact
        uniswapMintFeeCallFromMint_feeOn_kLastNonzero_noMint evmL evm1S evmFeeS I
          balance0 balance1 feeTo rootK rootKLast
          (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeToAddr hkLastSource
          hprefix hrootNoMint
    have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
        [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
          mintToMaskedWord I, ⟨861⟩, sel]
        memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k3701 C3701 := by
      simpa [htoWord] using rd3701Raw
    exact ⟨k3701, C3701, by simpa [evmL, evmS] using hfee, rd3701, hmem, hmem64⟩
  · rcases hpositiveNoLiquidity with
      ⟨hroot, hnumFit, hrootFiveFit, hdenFit, hdenom, hfeeLiq⟩
    obtain ⟨k3701, C3701, rd3701Raw⟩ :=
      uniswapMintFeeRuntimeAfterRootsPositiveNoLiquidityReturn rootK rootKLast rd7899
        evmFeeS htotalEq hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit
        hrootFiveFit hdenFit hdenom hfeeLiq
    have hfee :
        ExecStmt config
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
          (.ok
            (resumeAfterInternalCall
              { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
              "feeOn" (some [.bool true]))
            evmFeeS) := by
      exact
        uniswapMintFeeCallFromMint_feeOn_kLastNonzero_positiveNoLiquidity evmL evm1S
          evmFeeS I balance0 balance1 feeTo rootK rootKLast
          (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeToAddr hkLastSource
          hprefix hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit
          hdenFit hdenom hfeeLiq
    have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
        [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
          mintToMaskedWord I, ⟨861⟩, sel]
        memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k3701 C3701 := by
      simpa [htoWord] using rd3701Raw
    exact ⟨k3701, C3701, by simpa [evmL, evmS] using hfee, rd3701, hmem, hmem64⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOnReturnFromAfterFeeWitnessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σAfter : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity sel : UInt256}
    (rootLiquidity : Int)
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
    (hfee :
      let evmL := uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok
          (resumeAfterInternalCall
            { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
            "feeOn" (some [.bool true]))
          evmAfter))
    (hPostAccountsAfter : accountMapEquiv σAfter evmAfter.accountMap)
    (henvAfterI : evmAfter.executionEnv = I)
    (hcreatedAfter : evmAfter.createdAccounts = cAFee)
    (htotalZero : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (hsqrt :
      let evmL := uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      let nextFrame :=
        resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          "feeOn" (some [.bool true])
      ExecStmt config
        { contract := contract,
          locals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
        evmAfter
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextFrame.locals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmAfter))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, ⟨1⟩, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, mintToMaskedWord I,
        ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σAfter) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σAfter I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hfitSupplySource :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalanceSource :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (htotalFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem)).toNat +
          liquidity.toNat < UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (helapsedSource :
      syncTimeElapsedInt
          (mintFunctionPostState
            (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity) =
        0)
    (hfitKLastRuntime :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfter ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfter I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hfitKLastSource :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmAfter (AccountAddress.ofNat 0)
                  (⟨1000⟩ : UInt256))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmAfter (AccountAddress.ofNat 0)
                  (⟨1000⟩ : UInt256))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1)) <
        UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  have hfitSub : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256 := by
    have hrootNonneg : 0 ≤ rootLiquidity := by
      have hge : (1000 : Int) ≤ rootLiquidity := by
        simpa [minimumLiquidity] using hrootGeMin
      omega
    have hrootLt : rootLiquidity < (UInt256.size : Int) := by
      have h : (rootLiquidity.toNat : Int) < (UInt256.size : Int) := by
        exact_mod_cast hrootSize
      simpa [Int.toNat_of_nonneg hrootNonneg] using h
    norm_num [minimumLiquidity, UInt256.size] at hrootLt ⊢
    omega
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
        (.returned
          (let recipient := AccountAddress.ofNat (mintToWord I).toNat
           let afterTotalSupplyLocals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
           let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
           let afterRoot :=
            resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
           let afterLiquidity : Frame :=
            { contract := contract,
              locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
           let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
           let afterMint := resumeAfterInternalCall afterMinimum "_mintResult" none
           resumeAfterInternalCall afterMint "_updateResult" none)
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdatePackedReserveState
                (mintFunctionPostState
                  (mintFunctionPostState evmAfter (AccountAddress.ofNat 0)
                    (⟨1000⟩ : UInt256))
                  (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
                balance0 balance1)))
          (some [uniswapUint256Value liquidity])) := by
    exact ExecFuncBody.execBlockRet
      (uniswapMintAfterMintFeeInitialFeeOnReturn_of_call evmS evm0S evm1S evmAfter I
        nextFrame.locals rootLiquidity (AccountAddress.ofNat (mintToWord I).toNat)
        (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1
        hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
        (by simpa [evmL, evmS] using hfee)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS, mintToValue] using
          mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_kLast evmL I balance0 balance1 true)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 true)
        htotalZero (by simpa [evmL, evmS, nextFrame] using hsqrt)
        hrootGeMin hfitSub hliquidity hliqNonzero hfitSupplyMinSource
        hfitBalanceMinSource hfitSupplySource hfitBalanceSource
        (by
          have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by decide +native
          have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound0
          norm_num [maxUint112]
          exact_mod_cast hnat)
        (by
          have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by decide +native
          have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound1
          norm_num [maxUint112]
          exact_mod_cast hnat)
        helapsedSource hfitKLastSource)
  have hrecipient :
      AccountAddress.ofNat (mintToWord I).toNat =
        AccountAddress.ofNat (mintToMaskedWord I).toNat := by
    have h := solcAddressValue_masked (mintToWord I)
    simpa [mintToMaskedWord, u256_land_comm] using h
  exact uniswapMintFinishInitialFeeOn hcode hdispatch hsz36 hbody rd2531
    hPostAccountsAfter henvAfterI hcreatedAfter hrecipient
    (mintInitial_rootSub_word_eq rootLiquidity liquidity hrootSize hrootGeMin hliquidity)
    (mintInitial_rootGe_word rootLiquidity hrootSize hrootGeMin) hliqNonzero hperm
    hfitSupplyMinSource hfitBalanceMinSource htotalFitMin hbalanceFitMin hfitSupplySource
    hfitBalanceSource htotalFit hbalanceFit hbound0 hbound1 helapsed0
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hfitKLastRuntime hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroInitialReturnFromFactoryCase
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
      mintFeeOnKLastNonzeroInitialReturnFromFactoryCaseData feeToWord reserve0 reserve1
        amount0 amount1 balance0 balance1 σFee evmFeeS
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
      htotalFitMin, hbalanceFitMin, hfitSupplySource, hfitBalanceSource, htotalFit,
      hbalanceFit, hbound0, hbound1, helapsed0, helapsedSource, hfitKLastRuntime,
      hfitKLastSource⟩
  exact
    uniswapMintInitialFeeOnReturnFromAfterFeeWitnessCase
      (liquidity := UInt256.ofNat (root - minimumLiquidity).toNat)
      root hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 hle0Source hle1Source
      (by simpa [evmL, evmS] using hfee) hPostAccountsFee henvFeeI hcreatedFee
      htotalSource
      (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS, htotalSource]
        using hsqrt)
      rd2531 hrootSize hrootGeMin rfl hliqNonzero hfitSupplyMinSource
      hfitBalanceMinSource htotalFitMin hbalanceFitMin hfitSupplySource hfitBalanceSource
      htotalFit hbalanceFit hbound0 hbound1 helapsed0 helapsedSource hfitKLastRuntime
      hfitKLastSource hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroInitialZeroFromFactoryCase
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
      mintFeeOnKLastNonzeroInitialZeroFromFactoryCaseData feeToWord reserve0 reserve1
        amount0 amount1 balance0 balance1 σFee evmFeeS
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
    ⟨hrootGeMin, hliquidityZero, hfitSupplyMinSource, hfitBalanceMinSource,
      htotalFitMin, hbalanceFitMin⟩
  exact
    uniswapMintInitialAfterMintFeeLiquidityZeroRevertCase nextFrame.locals root hcode
      hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source (by simpa [evmL, evmS] using hfee) hbase htotalSource
      (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS, htotalSource]
        using hsqrt)
      rd2531 hrootSize hrootGeMin rfl hliquidityZero hfitSupplyMinSource
      hfitBalanceMinSource htotalFitMin hbalanceFitMin hperm hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroInitialProductOverflowFromFactoryCase
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
      mintFeeOnKLastNonzeroInitialProductOverflowFromFactoryCaseData feeToWord reserve0
        reserve1 amount0 amount1 σFee evmFeeS I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool true])
  rcases hcase with ⟨hprefixCase, htotalZero, hover⟩
  obtain ⟨k3701, C3701, hfee, rd3701, hmem, hmem64⟩ :=
    uniswapMintFeeOnKLastNonzeroNoFeeLiquidityPrefixFromFactory feeTo hfeeGuard hfeeCall
      hfeeDec hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hkLastEq
      htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
      hfeeToWord hfeeTo htoWord hmemFee hprefixCase
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
  exact
    uniswapMintInitialProductOverflowFromAfterFeeCase nextFrame.locals hcode hdispatch
      hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source
      hle1Source (by simpa [evmL, evmS] using hfee)
      (by simpa [nextFrame, evmL, evmS] using
        mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
      (by simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
        mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
      (by simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
        mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
      htotalSource htotalZero hover rd3701 hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroInitialRootUnderflowFromFactoryCase
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
      mintFeeOnKLastNonzeroInitialRootUnderflowFromFactoryCaseData feeToWord reserve0
        reserve1 amount0 amount1 balance0 balance1 σFee evmFeeS
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
  have hrootLt :=
    hfinish root (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS] using hsqrt)
      hrootNonneg hrootSize
  exact
    uniswapMintInitialAfterMintFeeRootUnderflowRevertCase nextFrame.locals root hcode
      hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
      hle0Source hle1Source (by simpa [evmL, evmS] using hfee) hbase htotalSource
      (by simpa [caller, afterTotalSupplyLocals, nextFrame, evmL, evmS, htotalSource]
        using hsqrt)
      rd2531 hrootSize hrootLt hmem hmem64

theorem uniswapMintFeeOnKLastNonzeroInitialFromFactoryCases
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
      mintFeeOnKLastNonzeroInitialFromFactoryCasesData feeToWord reserve0 reserve1 amount0
        amount1 balance0 balance1 σFee evmFeeS
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        I memFee) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hreturn | hrest
  · exact
      uniswapMintFeeOnKLastNonzeroInitialReturnFromFactoryCase feeTo hcode hdispatch
        hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee henvFeeI
        hcreatedFee hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0Eq
        hamount1Eq hkLastEq htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
        hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord hmemFee hreturn
  rcases hrest with hzero | hrest
  · exact
      uniswapMintFeeOnKLastNonzeroInitialZeroFromFactoryCase feeTo hcode hdispatch
        hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hreserve0Eq hreserve1Eq
        hruntimeReserve0 hruntimeReserve1 hamount0Eq hamount1Eq hkLastEq htotalEq
        rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord
        hfeeTo htoWord hmemFee hzero
  rcases hrest with hproduct | hrootUnderflow
  · exact
      uniswapMintFeeOnKLastNonzeroInitialProductOverflowFromFactoryCase feeTo hcode
        hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hreserve0Eq hreserve1Eq
        hruntimeReserve0 hruntimeReserve1 hamount0Eq hamount1Eq hkLastEq htotalEq
        rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord
        hfeeTo htoWord hmemFee hproduct
  · exact
      uniswapMintFeeOnKLastNonzeroInitialRootUnderflowFromFactoryCase feeTo hcode
        hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hreserve0Eq hreserve1Eq
        hruntimeReserve0 hruntimeReserve1 hamount0Eq hamount1Eq hkLastEq htotalEq
        rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord
        hfeeTo htoWord hmemFee hrootUnderflow

end UniswapV2Pair

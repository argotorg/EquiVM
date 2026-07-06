import Examples.UniswapV2Pair.MintInitialFactorySecondMintReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastZeroSecondMintBalanceOverflowFromFactoryWitnessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity sel : UInt256}
    (feeTo : AccountAddress) (rootLiquidity : Int)
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalZero : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩)
    (hsqrt :
      let evmL := uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      let nextFrame :=
        resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          "feeOn" (some (.bool false))
      ExecStmt config
        { contract := contract,
          locals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS)) }
        evmFeeS
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextFrame.locals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS)) }
            "rootLiquidity" (some (.int rootLiquidity)))
          evmFeeS))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, mintToMaskedWord I,
        ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmFeeS (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hfitSupplySource :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hsourceOverflow :
      UInt256.size ≤
        mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
    (hruntimeSupplyFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hruntimeOverflow :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem)).toNat +
            liquidity.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmFeeS) := by
    simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  exact uniswapMintInitialAfterMintFeeSecondMintBalanceOverflowRevertCase
    nextFrame.locals rootLiquidity (AccountAddress.ofNat (mintToWord I).toNat)
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
    hdec1 hle0Source hle1Source hfee
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    htotalZero (by simpa [evmL, evmS, nextFrame] using hsqrt) rd2531 hrootSize
    hrootGeMin hliquidity hliqNonzero hfitSupplyMinSource hfitBalanceMinSource
    htotalFitMin hbalanceFitMin hfitSupplySource hsourceOverflow hruntimeSupplyFit
    hruntimeOverflow hperm hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOnKLastZeroSecondMintBalanceOverflowFromFactoryWitnessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity sel : UInt256}
    (feeTo : AccountAddress) (rootLiquidity : Int)
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToNonzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalZero : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩)
    (hsqrt :
      let evmL := uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      let nextFrame :=
        resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          "feeOn" (some (.bool true))
      ExecStmt config
        { contract := contract,
          locals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS)) }
        evmFeeS
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextFrame.locals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS)) }
            "rootLiquidity" (some (.int rootLiquidity)))
          evmFeeS))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, mintToMaskedWord I,
        ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmFeeS (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hfitSupplySource :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hsourceOverflow :
      UInt256.size ≤
        mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
    (hruntimeSupplyFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hruntimeOverflow :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem)).toNat +
            liquidity.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool true))
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToNonzero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmFeeS) := by
    simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  exact uniswapMintInitialAfterMintFeeSecondMintBalanceOverflowRevertCase
    nextFrame.locals rootLiquidity (AccountAddress.ofNat (mintToWord I).toNat)
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
    hdec1 hle0Source hle1Source hfee
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
    htotalZero (by simpa [evmL, evmS, nextFrame] using hsqrt) rd2531 hrootSize
    hrootGeMin hliquidity hliqNonzero hfitSupplyMinSource hfitBalanceMinSource
    htotalFitMin hbalanceFitMin hfitSupplySource hsourceOverflow hruntimeSupplyFit
    hruntimeOverflow hperm hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastNonzeroSecondMintBalanceOverflowFromFactoryWitnessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity sel : UInt256}
    (feeTo : AccountAddress) (rootLiquidity : Int)
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalZero :
      mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFeeS) = ⟨0⟩)
    (hsqrt :
      let evmL := uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      let evmAfterFee := mintFeeKLastClearedState evmFeeS
      let nextFrame :=
        resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          "feeOn" (some (.bool false))
      ExecStmt config
        { contract := contract,
          locals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfterFee)) }
        evmAfterFee
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextFrame.locals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfterFee)) }
            "rootLiquidity" (some (.int rootLiquidity)))
          evmAfterFee))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, mintToMaskedWord I,
        ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata
      (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFeeS)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat (mintFeeKLastClearedState evmFeeS)
          (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩
        (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I).toNat +
          (⟨1000⟩ : UInt256).toNat <
        UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) ⟨0⟩
          (uniswapSlotWord ⟨0⟩
            (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hfitSupplySource :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState (mintFeeKLastClearedState evmFeeS)
            (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hsourceOverflow :
      UInt256.size ≤
        mintFunctionToBalanceNewNat
          (mintFunctionPostState (mintFeeKLastClearedState evmFeeS)
            (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
    (hruntimeSupplyFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) ⟨0⟩
            (uniswapSlotWord ⟨0⟩
              (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I +
              (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) ⟨0⟩
              (uniswapSlotWord ⟨0⟩
                (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I +
                (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hruntimeOverflow :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) ⟨0⟩
            (uniswapSlotWord ⟨0⟩
              (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I +
              (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) ⟨0⟩
              (uniswapSlotWord ⟨0⟩
                (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I +
                (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem)).toNat +
            liquidity.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmAfterFee) := by
    simpa [nextFrame, evmL, evmS, evmAfterFee, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  exact uniswapMintInitialAfterMintFeeSecondMintBalanceOverflowRevertCase
    nextFrame.locals rootLiquidity (AccountAddress.ofNat (mintToWord I).toNat)
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
    hdec1 hle0Source hle1Source hfee
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    htotalZero (by simpa [evmAfterFee, evmL, evmS, nextFrame] using hsqrt) rd2531
    hrootSize hrootGeMin hliquidity hliqNonzero hfitSupplyMinSource hfitBalanceMinSource
    htotalFitMin hbalanceFitMin hfitSupplySource hsourceOverflow hruntimeSupplyFit
    hruntimeOverflow hperm hmem hmem64

end UniswapV2Pair

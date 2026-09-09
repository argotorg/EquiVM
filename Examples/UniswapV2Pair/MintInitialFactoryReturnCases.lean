import Examples.UniswapV2Pair.MintInitialCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem mintInitial_rootSub_word_eq
    (rootLiquidity : Int) (liquidity : UInt256)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat) :
    liquidity = UInt256.sub (UInt256.ofNat rootLiquidity.toNat) (⟨1000⟩ : UInt256) := by
  apply u256_inj
  have hrootWordToNat :
      (UInt256.ofNat rootLiquidity.toNat).toNat = rootLiquidity.toNat :=
    ulit_toNat' _ hrootSize
  have hrootGeWord :
      (⟨1000⟩ : UInt256).toNat ≤ (UInt256.ofNat rootLiquidity.toNat).toNat := by
    rw [hrootWordToNat]
    have hge : (1000 : Int) ≤ rootLiquidity := by
      simpa [minimumLiquidity] using hrootGeMin
    have hrootNonneg : 0 ≤ rootLiquidity := by omega
    have h : (1000 : Int) ≤ (rootLiquidity.toNat : Int) := by
      simpa [Int.toNat_of_nonneg hrootNonneg] using hge
    exact_mod_cast h
  have hsubToNat :
      (UInt256.sub (UInt256.ofNat rootLiquidity.toNat) (⟨1000⟩ : UInt256)).toNat =
        rootLiquidity.toNat - 1000 := by
    rw [usub_toNat hrootGeWord, hrootWordToNat]
    have h1000 : (⟨1000⟩ : UInt256).toNat = 1000 := by decide +native
    rw [h1000]
  rw [hliquidity, hsubToNat]
  have hnonneg : 0 ≤ rootLiquidity - minimumLiquidity := by
    have hge : (1000 : Int) ≤ rootLiquidity := by
      simpa [minimumLiquidity] using hrootGeMin
    simp [minimumLiquidity]
    omega
  have htoNatEq : (rootLiquidity - minimumLiquidity).toNat = rootLiquidity.toNat - 1000 := by
    have hrootNonneg : 0 ≤ rootLiquidity := by
      have hge : (1000 : Int) ≤ rootLiquidity := by
        simpa [minimumLiquidity] using hrootGeMin
      omega
    have hrootCast : (rootLiquidity.toNat : Int) = rootLiquidity :=
      Int.toNat_of_nonneg hrootNonneg
    calc
      (rootLiquidity - minimumLiquidity).toNat =
          (rootLiquidity - (1000 : Int)).toNat := by simp [minimumLiquidity]
      _ = (((rootLiquidity.toNat : Nat) : Int) - (1000 : Int)).toNat := by
        rw [hrootCast]
      _ = rootLiquidity.toNat - 1000 := by
        exact Int.toNat_sub rootLiquidity.toNat 1000
  rw [UInt256.toNat_ofNat_of_lt]
  · exact htoNatEq
  · simpa [htoNatEq, UInt256.size] using
      lt_of_le_of_lt (Nat.sub_le rootLiquidity.toNat 1000) hrootSize

theorem mintInitial_rootGe_word
    (rootLiquidity : Int)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootGeMin : minimumLiquidity ≤ rootLiquidity) :
    (⟨1000⟩ : UInt256).toNat ≤ (UInt256.ofNat rootLiquidity.toNat).toNat := by
  rw [ulit_toNat' _ hrootSize]
  have hge : (1000 : Int) ≤ rootLiquidity := by
    simpa [minimumLiquidity] using hrootGeMin
  have hrootNonneg : 0 ≤ rootLiquidity := by omega
  have h : (1000 : Int) ≤ (rootLiquidity.toNat : Int) := by
    simpa [Int.toNat_of_nonneg hrootNonneg] using hge
  exact_mod_cast h

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastZeroReturnFromFactoryWitnessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity sel : UInt256}
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
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
          "feeOn" (some [.bool false])
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
            "rootLiquidity" (some [.int rootLiquidity]))
          evmFeeS))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, ⟨0⟩, amount1,
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
    (hfitBalanceSource :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (htotalFit :
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
    (hbalanceFit :
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
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
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
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity) =
        0)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
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
          (let evmL := uniswapLockEnteredState evmS
           let recipient := AccountAddress.ofNat (mintToWord I).toNat
           let nextFrame :=
            resumeAfterInternalCall
              { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
              "feeOn" (some [.bool false])
           let afterTotalSupplyLocals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))
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
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
                  (⟨1000⟩ : UInt256))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1))
          (some [uniswapUint256Value liquidity])) := by
    exact ExecFuncBody.execBlockRet
      (uniswapMintInitialFeeOffReturn_kLastZero evmS evm0S evm1S evmFeeS I feeTo
        rootLiquidity (by simp only [evmS, initState]; exact hwv) hunlockedSolm
        hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard
        hfeeCall hfeeDec hfeeToAddr hkLastSource htotalZero hsqrt hrootGeMin hfitSub
        hliquidity hliqNonzero hfitSupplyMinSource hfitBalanceMinSource hfitSupplySource
        hfitBalanceSource (by
          have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by decide +native
          have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound0
          norm_num [maxUint112]
          exact_mod_cast hnat)
        (by
          have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by decide +native
          have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound1
          norm_num [maxUint112]
          exact_mod_cast hnat)
        helapsedSource)
  have hrecipient :
      AccountAddress.ofNat (mintToWord I).toNat =
        AccountAddress.ofNat (mintToMaskedWord I).toNat := by
    have h := solcAddressValue_masked (mintToWord I)
    simpa [mintToMaskedWord, u256_land_comm] using h
  exact uniswapMintFinishInitialFeeOff hcode hdispatch hsz36 hbody rd2531
    hPostAccountsFee henvFeeI hcreatedFee hrecipient
    (mintInitial_rootSub_word_eq rootLiquidity liquidity hrootSize hrootGeMin hliquidity)
    (mintInitial_rootGe_word rootLiquidity hrootSize hrootGeMin) hliqNonzero hperm
    hfitSupplyMinSource hfitBalanceMinSource htotalFitMin hbalanceFitMin hfitSupplySource
    hfitBalanceSource htotalFit hbalanceFit hbound0 hbound1 helapsed0 rfl hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOnKLastZeroReturnFromFactoryWitnessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity sel : UInt256}
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
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
          "feeOn" (some [.bool true])
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
            "rootLiquidity" (some [.int rootLiquidity]))
          evmFeeS))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, ⟨1⟩, amount1,
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
    (hfitBalanceSource :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (htotalFit :
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
    (hbalanceFit :
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
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
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
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity) =
        0)
    (hfitKLastRuntime :
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
        UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToNonzero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
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
          (let evmL := uniswapLockEnteredState evmS
           let recipient := AccountAddress.ofNat (mintToWord I).toNat
           let nextFrame :=
            resumeAfterInternalCall
              { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
              "feeOn" (some [.bool true])
           let afterTotalSupplyLocals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))
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
                  (mintFunctionPostState evmFeeS (AccountAddress.ofNat 0)
                    (⟨1000⟩ : UInt256))
                  (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
                balance0 balance1)))
          (some [uniswapUint256Value liquidity])) := by
    exact ExecFuncBody.execBlockRet
      (uniswapMintInitialFeeOnReturn_kLastZero evmS evm0S evm1S evmFeeS I feeTo
        rootLiquidity (by simp only [evmS, initState]; exact hwv) hunlockedSolm
        hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard
        hfeeCall hfeeDec hfeeToAddr hkLastSource htotalZero hsqrt hrootGeMin hfitSub
        hliquidity hliqNonzero hfitSupplyMinSource hfitBalanceMinSource hfitSupplySource
        hfitBalanceSource (by
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
    hPostAccountsFee henvFeeI hcreatedFee hrecipient
    (mintInitial_rootSub_word_eq rootLiquidity liquidity hrootSize hrootGeMin hliquidity)
    (mintInitial_rootGe_word rootLiquidity hrootSize hrootGeMin) hliqNonzero hperm
    hfitSupplyMinSource hfitBalanceMinSource htotalFitMin hbalanceFitMin hfitSupplySource
    hfitBalanceSource htotalFit hbalanceFit hbound0 hbound1 helapsed0
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hfitKLastRuntime hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastNonzeroReturnFromFactoryWitnessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity sel : UInt256}
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
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
          "feeOn" (some [.bool false])
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
            "rootLiquidity" (some [.int rootLiquidity]))
          evmAfterFee))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, ⟨0⟩, amount1,
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
    (hfitBalanceSource :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState (mintFeeKLastClearedState evmFeeS)
            (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (htotalFit :
      let σCleared := sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σCleared I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σCleared I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let σCleared := sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σCleared I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σCleared I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) minimumMem)).toNat +
          liquidity.toNat < UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let σCleared := sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σCleared I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σCleared I + (⟨1000⟩ : UInt256)))
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
            (mintFunctionPostState (mintFeeKLastClearedState evmFeeS)
              (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity) =
        0)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let σCleared := sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some [.bool false])
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
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩
      hPostAccountsFee
    simpa [σCleared, evmAfterFee, mintFeeKLastClearedState, henvFeeI,
      storageStore_accountMap] using hstore
  have henvCleared : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
  have hcreatedCleared : evmAfterFee.createdAccounts = cAFee := by
    simp [evmAfterFee, mintFeeKLastClearedState, storageStore_createdAccounts, hcreatedFee]
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
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmAfterFee) := by
    simpa [nextFrame, evmL, evmS, evmAfterFee, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbody :=
    ExecFuncBody.execBlockRet
      (uniswapMintAfterMintFeeInitialFeeOffReturn_of_call evmS evm0S evm1S evmAfterFee I
        nextFrame.locals rootLiquidity (AccountAddress.ofNat (mintToWord I).toNat)
        (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1
        hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfee
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS, mintToValue] using
          mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 false)
        htotalZero (by simpa [evmAfterFee, evmL, evmS, nextFrame] using hsqrt)
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
        helapsedSource)
  have hrecipient :
      AccountAddress.ofNat (mintToWord I).toNat =
        AccountAddress.ofNat (mintToMaskedWord I).toNat := by
    have h := solcAddressValue_masked (mintToWord I)
    simpa [mintToMaskedWord, u256_land_comm] using h
  exact uniswapMintFinishInitialFeeOff hcode hdispatch hsz36 hbody rd2531
    hPostCleared henvCleared hcreatedCleared hrecipient
    (mintInitial_rootSub_word_eq rootLiquidity liquidity hrootSize hrootGeMin hliquidity)
    (mintInitial_rootGe_word rootLiquidity hrootSize hrootGeMin) hliqNonzero hperm
    hfitSupplyMinSource hfitBalanceMinSource htotalFitMin hbalanceFitMin hfitSupplySource
    hfitBalanceSource (by simpa [σCleared] using htotalFit)
    (by simpa [σCleared] using hbalanceFit) hbound0 hbound1
    (by simpa [σCleared] using helapsed0) rfl hmem hmem64

end UniswapV2Pair

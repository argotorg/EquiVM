import Examples.UniswapV2Pair.ZeroSlotMemory
import Examples.UniswapV2Pair.MintFeeActualHelpers
import Examples.UniswapV2Pair.MintTailMintCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeActualRootRuntimeCasesWithMemoryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
     {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int} {feeTo : AccountAddress}
    {kLast feeToWord reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (evmFeeS : EVM.State) (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeToWord ::
        ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evmFeeS.accountMap)
    (henv : evmFeeS.executionEnv = I)
    (hrecipient : feeTo = AccountAddress.ofNat feeToWord.toNat)
    (hrootKNonneg : 0 ≤ rootK) (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast) (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
      evmFeeS [mintFeeRootComparisonStmt] .reverted ∧
      RDrev uniswapV2PairBytecode g
        s0) ∨
    (∃ frame' evm' σ' mem' k' C',
      ExecBlock config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evmFeeS [mintFeeRootComparisonStmt] (.ok frame' evm') ∧
      evalExpr? config frame' evm' (.var "feeOn") = .ok (.bool true) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evmFeeS.createdAccounts ∧
      RD uniswapV2PairBytecode I g
        s0 ret
        (⟨1⟩ :: R) mem' feeToStaticcallActiveWords rdata (cAFee, σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      evm'.σ₀ = evmFeeS.σ₀ ∧ evm'.genesisBlockHeader = evmFeeS.genesisBlockHeader ∧
      evm'.blocks = evmFeeS.blocks ∧
      mem'.readWithPadding 96 32 = mem.readWithPadding 96 32) := by
  have htotalEq := mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hAccounts henv
  by_cases hroot : rootK > rootKLast
  · rcases uniswapMintFeeActualRootArithmeticCasesOfTail (hov := hov) rd7899 htotalEq hroot hrootKNonneg
      hrootKSize hrootKLastNonneg hrootKLastSize hmem hmem64 with
      ⟨hnumFit, hrootFiveFit, hdenFit⟩ | hrev
    · have hdenom := mintFeeDenominatorWord_ne_zero_of_fits hroot hrootKLastNonneg
        hrootFiveFit hdenFit
      have hliqFit := mintFeeLiquidityInt_toNat_lt evmFeeS rootK rootKLast
      have hliqRuntimeEq := mintFeeLiquidityWord_eq_runtime_div evmFeeS rootK rootKLast
        hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit hdenFit hliqFit
      rw [htotalEq] at hliqRuntimeEq
      have hnumFitRuntime := mintFeeRuntimeNumeratorFit evmFeeS rootK rootKLast hroot
        hrootKNonneg hrootKSize hrootKLastNonneg hnumFit
      rw [htotalEq] at hnumFitRuntime
      obtain ⟨_, _, rd7982⟩ := uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityEntryOfTail (hov := hov)
        rd7899 (mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg)
        hnumFitRuntime (mintFeeRuntimeRootTimesFiveFit rootK hrootFiveFit)
        (mintFeeRuntimeDenominatorFit rootK rootKLast hrootFiveFit hdenFit)
      obtain ⟨_, _, rd7999Raw⟩ := uniswapMintFeeRuntimePositiveLiquidityEntryOfTail (hov := hov) rd7982
        (mintFeeRuntimeDenominator_ne_zero rootK rootKLast hrootFiveFit hdenFit hdenom)
      rw [← hliqRuntimeEq] at rd7999Raw
      by_cases hliq : mintFeeLiquidityInt evmFeeS rootK rootKLast > 0
      · obtain ⟨_, _, rd8128⟩ := uniswapMintFeeRuntimePositiveLiquidityMintEntryOfTail (hov := hov) rd7999Raw
          (mintFeeLiquidityWord_ne_zero_of_pos evmFeeS rootK rootKLast hliq hliqFit)
        have htotalNewEq := mintFunctionTotalSupplyNewNat_eq_runtime
          (liquidity := mintFeeLiquidityWord evmFeeS rootK rootKLast) hAccounts henv
        have hargs := evalExprs_mintFee_mintArgs evmFeeS reserve0 reserve1 feeTo kLast
          rootK rootKLast (le_of_lt hliq) hliqFit
        by_cases hfitSupply : mintFunctionTotalSupplyNewNat evmFeeS
            (mintFeeLiquidityWord evmFeeS rootK rootKLast) < UInt256.size
        · have htotalFit := hfitSupply
          rw [htotalNewEq] at htotalFit
          have hbalanceEq := mintFunctionToBalanceNewNat_eq_runtimeMintRecipient
            (mem := mem) hAccounts henv hrecipient (by rw [hmem]; omega) hfitSupply
          by_cases hfitBalance : mintFunctionToBalanceNewNat evmFeeS feeTo
              (mintFeeLiquidityWord evmFeeS rootK rootKLast) < UInt256.size
          · have hbalanceFit := hfitBalance
            rw [hbalanceEq] at hbalanceFit
            obtain ⟨_, _, rd8014⟩ := uniswapInternalMintRuntimeSuccess rd8128
              hperm htotalFit hbalanceFit
              (uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 feeToWord
                (by rw [hmem]; omega) hmem64)
              (uniswapInternalMintSuccessMem_mload64_of_ge160 feeToWord
                (mintFeeLiquidityWord evmFeeS rootK rootKLast) (by rw [hmem]; omega) hmem64)
              (by jump_dest) (by simp only [List.length_cons]; omega)
            obtain ⟨_, _, rdRet⟩ :=
              uniswapMintFeeRuntimeAfterInternalMintReturnOfTail rd8014 hret hov
            refine Or.inr ⟨_, _, _, _, _, _,
              uniswapMintFeeAfterRoots_positiveWithLiquidity evmFeeS reserve0 reserve1
                feeTo kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg
                hnumFit hrootFiveFit hdenFit hdenom hliq hliqFit hfitSupply hfitBalance,
              evalExpr_mintFee_afterFeeMint_feeOn evmFeeS _ reserve0 reserve1 feeTo
                kLast rootK rootKLast,
              accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient hAccounts henv
                hrecipient (by rw [hmem]; omega) hfitSupply hfitBalance,
              ?_, ?_, rdRet, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
                storageStore_executionEnv, henv]
            · simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
                storageStore_createdAccounts]
            · exact (uniswapInternalMintSuccessMem_size_of_ge160 feeToWord
                (mintFeeLiquidityWord evmFeeS rootK rootKLast) (by rw [hmem]; omega)).trans hmem
            · exact uniswapInternalMintSuccessMem_read64_of_ge160 feeToWord
                (mintFeeLiquidityWord evmFeeS rootK rootKLast) (by rw [hmem]; omega) hmem64
            · simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
                balanceCallStorageStore_sigma0]
            · simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
                balanceCallStorageStore_genesisBlockHeader]
            · simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
                balanceCallStorageStore_blocks]
            · exact uniswapInternalMintSuccessMem_read96 feeToWord
                (mintFeeLiquidityWord evmFeeS rootK rootKLast) (by rw [hmem]; omega)
          · exact Or.inl ⟨uniswapMintFeeAfterRoots_mintCallReverts evmFeeS reserve0 reserve1
              feeTo kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg
              hnumFit hrootFiveFit hdenFit hdenom hliq
              (uniswapMintFunctionCallRevert_balanceOverflow rfl hargs hfitSupply
                (Nat.le_of_not_lt hfitBalance)),
              uniswapInternalMintRuntimeBalanceOverflowReverts rd8128 hperm htotalFit
                (by rw [← hbalanceEq]; exact Nat.le_of_not_lt hfitBalance) hmem hmem64
                (by simp only [List.length_cons]; omega)⟩
        · exact Or.inl ⟨uniswapMintFeeAfterRoots_mintCallReverts evmFeeS reserve0 reserve1
            feeTo kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg
            hnumFit hrootFiveFit hdenFit hdenom hliq
            (uniswapMintFunctionCallRevert_totalSupplyOverflow rfl hargs
              (Nat.le_of_not_lt hfitSupply)),
            uniswapInternalMintRuntimeTotalSupplyOverflowReverts rd8128
              (by rw [← htotalNewEq]; exact Nat.le_of_not_lt hfitSupply) hmem hmem64
              (by simp only [List.length_cons]; omega)⟩
      · obtain ⟨_, _, rdRet⟩ := uniswapMintFeeRuntimePositiveLiquidityZeroNoMintReturnOfTail
          rd7999Raw (mintFeeLiquidityWord_eq_zero_of_not_pos evmFeeS rootK rootKLast hliq)
          hret hov
        exact Or.inr ⟨_, evmFeeS, σFee, mem, _, _,
          uniswapMintFeeAfterRoots_positiveNoLiquidity evmFeeS reserve0 reserve1 feeTo kLast
            rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg
            hnumFit hrootFiveFit hdenFit hdenom hliq,
          evalExpr_mintFee_afterLiquidity_feeOn evmFeeS reserve0 reserve1 feeTo true kLast
            rootK rootKLast, hAccounts, henv, rfl, rdRet, hmem, hmem64, rfl, rfl, rfl, rfl⟩
    · exact Or.inl hrev
  · obtain ⟨_, _, rdRet⟩ := uniswapMintFeeRuntimeAfterRootsNoMintReturnOfTail rd7899
      (mintFeeRuntimeRootLe_of_int_not_gt rootK rootKLast hroot hrootKSize hrootKLastSize)
      hret hov
    exact Or.inr ⟨_, evmFeeS, σFee, mem, _, _,
      uniswapMintFeeAfterRoots_noMint evmFeeS reserve0 reserve1 feeTo kLast rootK rootKLast hroot,
      evalExpr_mintFee_afterRootKLast_feeOn evmFeeS reserve0 reserve1 feeTo true kLast
        rootK rootKLast, hAccounts, henv, rfl, rdRet, hmem, hmem64, rfl, rfl, rfl, rfl⟩


set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeActualRootRuntimeCasesWithWorldOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
     {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int} {feeTo : AccountAddress}
    {kLast feeToWord reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (evmFeeS : EVM.State) (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeToWord ::
        ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evmFeeS.accountMap)
    (henv : evmFeeS.executionEnv = I)
    (hrecipient : feeTo = AccountAddress.ofNat feeToWord.toNat)
    (hrootKNonneg : 0 ≤ rootK) (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast) (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
      evmFeeS [mintFeeRootComparisonStmt] .reverted ∧
      RDrev uniswapV2PairBytecode g
        s0) ∨
    (∃ frame' evm' σ' mem' k' C',
      ExecBlock config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evmFeeS [mintFeeRootComparisonStmt] (.ok frame' evm') ∧
      evalExpr? config frame' evm' (.var "feeOn") = .ok (.bool true) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evmFeeS.createdAccounts ∧
      RD uniswapV2PairBytecode I g
        s0 ret
        (⟨1⟩ :: R) mem' feeToStaticcallActiveWords rdata (cAFee, σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      evm'.σ₀ = evmFeeS.σ₀ ∧ evm'.genesisBlockHeader = evmFeeS.genesisBlockHeader ∧
      evm'.blocks = evmFeeS.blocks) := by
  rcases uniswapMintFeeActualRootRuntimeCasesWithMemoryOfTail evmFeeS rd7899 hAccounts henv
      hrecipient hrootKNonneg hrootKSize hrootKLastNonneg hrootKLastSize hperm hmem hmem64 hret hov with
    hrev | ⟨f, e, σ', m, k', C', hb, hf, ha, he, hc, rd, hm, h64, hs, hg, hbl, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨f, e, σ', m, k', C', hb, hf, ha, he, hc, rd, hm, h64, hs, hg, hbl⟩


set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeActualRootRuntimeCasesOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
     {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int} {feeTo : AccountAddress}
    {kLast feeToWord reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (evmFeeS : EVM.State) (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeToWord ::
        ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evmFeeS.accountMap)
    (henv : evmFeeS.executionEnv = I)
    (hrecipient : feeTo = AccountAddress.ofNat feeToWord.toNat)
    (hrootKNonneg : 0 ≤ rootK) (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast) (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
      evmFeeS [mintFeeRootComparisonStmt] .reverted ∧
      RDrev uniswapV2PairBytecode g
        s0) ∨
    (∃ frame' evm' σ' mem' k' C',
      ExecBlock config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evmFeeS [mintFeeRootComparisonStmt] (.ok frame' evm') ∧
      evalExpr? config frame' evm' (.var "feeOn") = .ok (.bool true) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evmFeeS.createdAccounts ∧
      RD uniswapV2PairBytecode I g
        s0 ret
        (⟨1⟩ :: R) mem' feeToStaticcallActiveWords rdata (cAFee, σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  rcases uniswapMintFeeActualRootRuntimeCasesWithWorldOfTail evmFeeS rd7899 hAccounts henv
      hrecipient hrootKNonneg hrootKSize hrootKLastNonneg hrootKLastSize hperm hmem
      hmem64 hret hov with hrev | ⟨f, e, σ', m, k', C', hb, hf, ha, he, hc, rd, hm, h64, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨f, e, σ', m, k', C', hb, hf, ha, he, hc, rd, hm, h64⟩

end UniswapV2Pair

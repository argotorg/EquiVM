import Examples.UniswapV2Pair.MintFeeRootRuntimeCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeFunctionBodyRuntimeAfterFactoryCasesWithMemory
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata out : ByteArray} {k C : ℕ}
    {reserve0 reserve1 feeToWord ret : UInt256} {R : List UInt256}
    (evm evmFee : EVM.State) (feeTo : AccountAddress)
    (rd7825 : RD uniswapV2PairBytecode I g s0 ⟨7825⟩
      (mintFeeKLastWord evmFee :: feeToWord :: ⟨0⟩ :: ⟨0⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hguard : evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
      (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hrecipient : feeTo = AccountAddress.ofNat feeToWord.toNat)
    (hAccounts : accountMapEquiv σFee evmFee.accountMap)
    (henv : evmFee.executionEnv = I)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ feeOn : Bool, ∃ frame' evm' σ' mem' k' C',
      ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        (.returned frame' evm' (some [.bool feeOn])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evmFee.createdAccounts ∧
      RD uniswapV2PairBytecode I g s0 ret ((if feeOn then ⟨1⟩ else ⟨0⟩) :: R)
        mem' feeToStaticcallActiveWords rdata (cAFee, σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      evm'.σ₀ = evmFee.σ₀ ∧ evm'.genesisBlockHeader = evmFee.genesisBlockHeader ∧
      evm'.blocks = evmFee.blocks ∧
      mem'.readWithPadding 96 32 = mem.readWithPadding 96 32) := by
  by_cases hfeeZero : UInt256.land feeToWord solcAddrMask = ⟨0⟩
  · have hfeeTo : feeTo = AccountAddress.ofNat 0 := by
      rw [hrecipient]
      exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
        feeToWord.val.isLt
        (by simpa only [u256_ofNat_toNat] using hfeeZero)
    obtain ⟨_, _, rd8026⟩ := uniswapMintFeeRuntimeFeeOffEntryOfTail rd7825 hfeeZero hov
    by_cases hkLast : mintFeeKLastWord evmFee = ⟨0⟩
    · obtain ⟨_, _, rdRet⟩ := uniswapMintFeeRuntimeFeeOffKLastZeroReturnOfTail rd8026
        hkLast hret hov
      exact Or.inr ⟨false, _, evmFee, σFee, mem, _, _,
        uniswapMintFeeFunctionBody_feeOff_kLastZero evm evmFee reserve0 reserve1 feeTo
          hguard hcall hdec hfeeTo (by rw [hkLast]; rfl),
        hAccounts, henv, rfl, rdRet, hmem, hmem64, rfl, rfl, rfl, rfl⟩
    · have hkLastNat : (mintFeeKLastWord evmFee).toNat ≠ 0 := by
        intro hz
        exact hkLast (uint256_toNat_eq_zero hz)
      obtain ⟨_, _, rdRet⟩ := uniswapMintFeeRuntimeFeeOffKLastNonzeroReturnOfTail rd8026
        hperm hkLast hret hov
      refine Or.inr ⟨false, _, mintFeeKLastClearedState evmFee, _, mem, _, _,
        uniswapMintFeeFunctionBody_feeOff_kLastNonzero evm evmFee reserve0 reserve1 feeTo
          hguard hcall hdec hfeeTo hkLastNat, ?_, ?_, ?_, rdRet, hmem, hmem64, ?_, ?_, ?_, rfl⟩
      · simpa only [mintFeeKLastClearedState, storageStore_accountMap, henv] using
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩ hAccounts
      · simpa only [mintFeeKLastClearedState, storageStore_executionEnv] using henv
      · simp only [mintFeeKLastClearedState, storageStore_createdAccounts]
      · simp only [mintFeeKLastClearedState, balanceCallStorageStore_sigma0]
      · simp only [mintFeeKLastClearedState, balanceCallStorageStore_genesisBlockHeader]
      · simp only [mintFeeKLastClearedState, balanceCallStorageStore_blocks]
  · have hfeeTo : feeTo ≠ AccountAddress.ofNat 0 := by
      rw [hrecipient]
      exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
        feeToWord.val.isLt
        (by simpa only [u256_ofNat_toNat] using hfeeZero)
    obtain ⟨_, _, rd7848⟩ := uniswapMintFeeRuntimeFeeOnEntryOfTail rd7825 hfeeZero hov
    by_cases hkLast : mintFeeKLastWord evmFee = ⟨0⟩
    · obtain ⟨_, _, rdRet⟩ := uniswapMintFeeRuntimeFeeOnKLastZeroReturnOfTail rd7848
        hkLast hret hov
      exact Or.inr ⟨true, _, evmFee, σFee, mem, _, _,
        uniswapMintFeeFunctionBody_feeOn_kLastZero evm evmFee reserve0 reserve1 feeTo
          hguard hcall hdec hfeeTo (by rw [hkLast]; rfl),
        hAccounts, henv, rfl, rdRet, hmem, hmem64, rfl, rfl, rfl, rfl⟩
    · have hkLastNat : (mintFeeKLastWord evmFee).toNat ≠ 0 := by
        intro hz
        exact hkLast (uint256_toNat_eq_zero hz)
      obtain ⟨_, _, rd6780⟩ := uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntryOfTail rd7848
        hkLast hclean0 hclean1 hov
      obtain ⟨_, _, rd8046⟩ := uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryOfTail rd6780
        hclean0 hclean1 hov
      obtain ⟨rootK, rootKLast, _, _, hprefix, hrootKNonneg, hrootKSize, _,
        hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
        mintFeeSqrtPrefixRuntimeBoundedInputOfTail evmFee feeTo rd8046
          (mintFeeReserveProductNat_lt_of_clean reserve0 reserve1 hclean0 hclean1) hov
      rcases uniswapMintFeeActualRootRuntimeCasesWithMemoryOfTail evmFee rd7899 hAccounts henv hrecipient
          hrootKNonneg hrootKSize hrootKLastNonneg hrootKLastSize hperm hmem hmem64 hret hov with
        ⟨htail, rdRev⟩ | ⟨frame', evm', σ', mem', k', C', htail, hfeeOn, hpost, henv',
          hcreated, rdRet, hmem', hmem64', hs0, hgh, hbl, h96⟩
      · exact Or.inl ⟨uniswapMintFeeFunctionBody_feeOn_kLastNonzero_fromRootBlockRevert
          evm evmFee reserve0 reserve1 feeTo hguard hcall hdec hfeeTo hkLastNat
          (execBlock_append hprefix htail), rdRev⟩
      · exact Or.inr ⟨true, frame', evm', σ', mem', k', C',
          uniswapMintFeeFunctionBody_feeOn_kLastNonzero_fromRootBlock evm evmFee evm'
            reserve0 reserve1 feeTo frame' hguard hcall hdec hfeeTo hkLastNat
            (execBlock_append hprefix htail) hfeeOn,
          hpost, henv', hcreated, rdRet, hmem', hmem64', hs0, hgh, hbl, h96⟩


set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeFunctionBodyRuntimeAfterFactoryCasesWithWorld
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata out : ByteArray} {k C : ℕ}
    {reserve0 reserve1 feeToWord ret : UInt256} {R : List UInt256}
    (evm evmFee : EVM.State) (feeTo : AccountAddress)
    (rd7825 : RD uniswapV2PairBytecode I g s0 ⟨7825⟩
      (mintFeeKLastWord evmFee :: feeToWord :: ⟨0⟩ :: ⟨0⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hguard : evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
      (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hrecipient : feeTo = AccountAddress.ofNat feeToWord.toNat)
    (hAccounts : accountMapEquiv σFee evmFee.accountMap)
    (henv : evmFee.executionEnv = I)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ feeOn : Bool, ∃ frame' evm' σ' mem' k' C',
      ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        (.returned frame' evm' (some [.bool feeOn])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evmFee.createdAccounts ∧
      RD uniswapV2PairBytecode I g s0 ret ((if feeOn then ⟨1⟩ else ⟨0⟩) :: R)
        mem' feeToStaticcallActiveWords rdata (cAFee, σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      evm'.σ₀ = evmFee.σ₀ ∧ evm'.genesisBlockHeader = evmFee.genesisBlockHeader ∧
      evm'.blocks = evmFee.blocks) := by
  rcases uniswapMintFeeFunctionBodyRuntimeAfterFactoryCasesWithMemory evm evmFee feeTo
      rd7825 hguard hcall hdec hrecipient hAccounts henv hclean0 hclean1 hperm hmem hmem64 hret hov with
    hrev | ⟨b, f, e, σ', m, k', C', hb, ha, he, hc, rd, hm, h64, hs, hg, hbl, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨b, f, e, σ', m, k', C', hb, ha, he, hc, rd, hm, h64, hs, hg, hbl⟩


set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeFunctionBodyRuntimeAfterFactoryCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata out : ByteArray} {k C : ℕ}
    {reserve0 reserve1 feeToWord ret : UInt256} {R : List UInt256}
    (evm evmFee : EVM.State) (feeTo : AccountAddress)
    (rd7825 : RD uniswapV2PairBytecode I g s0 ⟨7825⟩
      (mintFeeKLastWord evmFee :: feeToWord :: ⟨0⟩ :: ⟨0⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hguard : evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
      (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hrecipient : feeTo = AccountAddress.ofNat feeToWord.toNat)
    (hAccounts : accountMapEquiv σFee evmFee.accountMap)
    (henv : evmFee.executionEnv = I)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    (ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ feeOn : Bool, ∃ frame' evm' σ' mem' k' C',
      ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
        (.returned frame' evm' (some [.bool feeOn])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evmFee.createdAccounts ∧
      RD uniswapV2PairBytecode I g s0 ret ((if feeOn then ⟨1⟩ else ⟨0⟩) :: R)
        mem' feeToStaticcallActiveWords rdata (cAFee, σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  rcases uniswapMintFeeFunctionBodyRuntimeAfterFactoryCasesWithWorld evm evmFee feeTo
      rd7825 hguard hcall hdec hrecipient hAccounts henv hclean0 hclean1 hperm hmem
      hmem64 hret hov with hrev | ⟨b, f, e, σ', m, k', C', hb, ha, he, hc, rd, hm, h64, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨b, f, e, σ', m, k', C', hb, ha, he, hc, rd, hm, h64⟩

end UniswapV2Pair

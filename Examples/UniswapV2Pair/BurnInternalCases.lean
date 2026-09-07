import Examples.UniswapV2Pair.ZeroSlotMemory
import Examples.UniswapV2Pair.BurnInternalRuntime
import Examples.UniswapV2Pair.BurnInternalReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair


noncomputable abbrev burnRuntimeBalanceMap (σ : AccountMap) (I : ExecutionEnv)
    (holder value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (mapSlot (UInt256.land holder solcAddrMask) ⟨1⟩)
    (UInt256.sub (uniswapCodeOwnerStorageWord I σ
      (mapSlot (UInt256.land holder solcAddrMask) ⟨1⟩)) value)

noncomputable abbrev burnRuntimePostMap (σ : AccountMap) (I : ExecutionEnv)
    (holder value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (burnRuntimeBalanceMap σ I holder value) ⟨0⟩
    (UInt256.sub (uniswapCodeOwnerStorageWord I (burnRuntimeBalanceMap σ I holder value)
      ⟨0⟩) value)

theorem burnFunctionFromSlot_eq_runtime (holder : AccountAddress) (holderWord : UInt256)
    (hholder : holder = AccountAddress.ofNat holderWord.toNat) :
    burnFunctionFromSlot holder = mapSlot (UInt256.land holderWord solcAddrMask) ⟨1⟩ := by
  subst holder
  unfold burnFunctionFromSlot balanceOfSlot burnFunctionFromKey
  rw [keyValueToWord_address_ofNat_mask, u256_land_comm solcAddrMask holderWord]

theorem burnFunctionFromBalanceWord_eq_runtime
    {σ : AccountMap} {I : ExecutionEnv} {evm : EVM.State}
    {holder : AccountAddress} {holderWord : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hholder : holder = AccountAddress.ofNat holderWord.toNat) :
    burnFunctionFromBalanceWord evm holder = uniswapCodeOwnerStorageWord I σ
      (mapSlot (UInt256.land holderWord solcAddrMask) ⟨1⟩) := by
  have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (mapSlot (UInt256.land holderWord solcAddrMask) ⟨1⟩) ⟨0⟩
  simpa [burnFunctionFromBalanceWord, uniswapCodeOwnerStorageWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, henv,
    burnFunctionFromSlot_eq_runtime holder holderWord hholder] using hword.symm

theorem accountMapEquiv_burnFunctionAfterBalanceState
    {σ : AccountMap} {I : ExecutionEnv} {evm : EVM.State}
    {holder : AccountAddress} {holderWord value : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hholder : holder = AccountAddress.ofNat holderWord.toNat)
    (hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat) :
    accountMapEquiv (burnRuntimeBalanceMap σ I holderWord value)
      (burnFunctionAfterBalanceState evm holder value).accountMap := by
  have hword := burnFunctionFromBalanceWord_eq_runtime hAccounts henv hholder
  have hdebit : burnFunctionBalanceDebitWord evm holder value =
      UInt256.sub (burnFunctionFromBalanceWord evm holder) value := by
    unfold burnFunctionBalanceDebitWord
    rw [← usub_toNat hbalance, u256_ofNat_toNat]
  have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner
    (mapSlot (UInt256.land holderWord solcAddrMask) ⟨1⟩)
    (UInt256.sub (uniswapCodeOwnerStorageWord I σ
      (mapSlot (UInt256.land holderWord solcAddrMask) ⟨1⟩)) value) hAccounts
  simpa [burnRuntimeBalanceMap, burnFunctionAfterBalanceState, storageStore_accountMap,
    henv, burnFunctionFromSlot_eq_runtime holder holderWord hholder, hdebit, hword] using hstore

theorem burnFunctionTotalSupplyWord_eq_runtime
    {σ : AccountMap} {I : ExecutionEnv} {evm : EVM.State}
    {holder : AccountAddress} {holderWord value : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hholder : holder = AccountAddress.ofNat holderWord.toNat)
    (hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat) :
    burnFunctionTotalSupplyWord evm holder value =
      uniswapCodeOwnerStorageWord I (burnRuntimeBalanceMap σ I holderWord value) ⟨0⟩ := by
  have hpost := accountMapEquiv_burnFunctionAfterBalanceState hAccounts henv hholder hbalance
  have hword := accountMapEquiv_storage_findD hpost I.codeOwner ⟨0⟩ ⟨0⟩
  simpa [burnFunctionTotalSupplyWord, uniswapCodeOwnerStorageWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, henv] using hword.symm

theorem accountMapEquiv_burnFunctionPostState
    {σ : AccountMap} {I : ExecutionEnv} {evm : EVM.State}
    {holder : AccountAddress} {holderWord value : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hholder : holder = AccountAddress.ofNat holderWord.toNat)
    (hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat)
    (hsupply : value.toNat ≤ (burnFunctionTotalSupplyWord evm holder value).toNat) :
    accountMapEquiv (burnRuntimePostMap σ I holderWord value)
      (burnFunctionPostState evm holder value).accountMap := by
  have hpost := accountMapEquiv_burnFunctionAfterBalanceState hAccounts henv hholder hbalance
  have hword := burnFunctionTotalSupplyWord_eq_runtime hAccounts henv hholder hbalance
  have hdebit : burnFunctionTotalSupplyDebitWord evm holder value =
      UInt256.sub (burnFunctionTotalSupplyWord evm holder value) value := by
    unfold burnFunctionTotalSupplyDebitWord
    rw [← usub_toNat hsupply, u256_ofNat_toNat]
  have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
    (UInt256.sub (uniswapCodeOwnerStorageWord I (burnRuntimeBalanceMap σ I holderWord value)
      ⟨0⟩) value) hpost
  simpa [burnRuntimePostMap, burnFunctionPostState, storageStore_accountMap, henv,
    hdebit, hword] using hstore


set_option maxRecDepth 2000000 in
theorem uniswapInternalBurnCallRuntimeCasesWithMemory
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {value holderWord ret : UInt256}
    {R : List UInt256} {caller : Frame} {args : List Expr} {retVar : Ident}
    (evm : EVM.State) (holder : AccountAddress)
    (rd8302 : RD uniswapV2PairBytecode I g s0 ⟨8302⟩
      (value :: holderWord :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hholder : holder = AccountAddress.ofNat holderWord.toNat)
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [burnFunctionFromValue holder, burnFunctionValueValue value])
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_burn" args retVar) .reverted ∧
      RDrev uniswapV2PairBytecode g s0) ∨
    (∃ mem' k' C',
      ExecStmt config caller evm (.internalCall "_burn" args retVar)
        (.ok (resumeAfterInternalCall caller retVar none) (burnFunctionPostState evm holder value)) ∧
      accountMapEquiv (burnRuntimePostMap σ I holderWord value)
        (burnFunctionPostState evm holder value).accountMap ∧
      RD uniswapV2PairBytecode I g s0 ret R mem' feeToStaticcallActiveWords rdata
        (cA, burnRuntimePostMap σ I holderWord value) k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      mem'.readWithPadding 96 32 = mem.readWithPadding 96 32) := by
  have hhashSize := uniswapInternalMintBalanceHashMem_size_of_ge64 holderWord
    (mem := mem) (by omega)
  have hhashRead := uniswapInternalMintBalanceHashMem_read64_of_ge96 holderWord
    (by omega) hread64
  have hslot0 := uniswapInternalMintBalanceHashSlot_eq_mapSlot holderWord
    (mem := mem) (by omega)
  have hslot1 := uniswapInternalMintBalanceHashSlot_eq_mapSlot holderWord
    (mem := uniswapInternalMintBalanceHashMem holderWord mem) (by rw [hhashSize]; omega)
  have hbalanceEq := burnFunctionFromBalanceWord_eq_runtime hAccounts henv hholder
  obtain ⟨_, _, rdSub0⟩ := uniswapInternalBurnRuntimeBalanceSubEntry rd8302 hov
  rw [hslot0, ← hbalanceEq] at rdSub0
  by_cases hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat
  · obtain ⟨_, _, rd8343⟩ := RD.uniswapSafeMathSubSuccess rdSub0 hbalance (by jump_dest)
      (by simp only [List.length_cons]; omega)
    obtain ⟨kSub1, CSub1, rdSub1'⟩ :=
      uniswapInternalBurnRuntimeStoreBalanceSupplySubEntry rd8343 hperm hov
    have hsupplyEq := burnFunctionTotalSupplyWord_eq_runtime hAccounts henv hholder hbalance
    have rdSub1 : RD uniswapV2PairBytecode I g s0 ⟨6879⟩
        (value :: burnFunctionTotalSupplyWord evm holder value ::
          ⟨8388⟩ :: value :: holderWord :: ret :: R)
        (uniswapInternalMintBalanceHashMem holderWord
          (uniswapInternalMintBalanceHashMem holderWord mem))
        feeToStaticcallActiveWords rdata (cA, burnRuntimeBalanceMap σ I holderWord value)
        kSub1 CSub1 := by
      simpa only [hslot1, hbalanceEq, hsupplyEq, burnRuntimeBalanceMap] using rdSub1'
    have hhash2Size := uniswapInternalMintDoubleBalanceHashMem_size_of_ge64 holderWord
      (mem := mem) (by omega)
    have hhash2Read := uniswapInternalMintDoubleBalanceHashMem_read64_of_ge96 holderWord
      (by omega) hread64
    by_cases hsupply : value.toNat ≤ (burnFunctionTotalSupplyWord evm holder value).toNat
    · obtain ⟨_, _, rd8388⟩ := RD.uniswapSafeMathSubSuccess rdSub1 hsupply (by jump_dest)
        (by simp only [List.length_cons]; omega)
      obtain ⟨kRet, CRet, rdRet⟩ := uniswapInternalBurnRuntimeStoreSupplyEmitAndJump rd8388
        hperm (by rw [hhash2Size]; omega) hhash2Read hret hov
      refine Or.inr ⟨uniswapInternalMintLogMem value
          (uniswapInternalMintBalanceHashMem holderWord
            (uniswapInternalMintBalanceHashMem holderWord mem)), kRet, CRet,
        uniswapBurnFunctionCallSuccess hcontract hargs hbalance hsupply,
        accountMapEquiv_burnFunctionPostState hAccounts henv hholder hbalance hsupply,
        ?_, ?_, ?_, ?_⟩
      · simpa only [burnRuntimePostMap, hsupplyEq] using rdRet
      · exact (uniswapInternalMintSuccessMem_size_of_ge160 holderWord value
          (by omega)).trans hmem
      · exact uniswapInternalMintSuccessMem_read64_of_ge160 holderWord value (by omega) hread64
      · exact uniswapInternalMintSuccessMem_read96 holderWord value (by omega)
    · exact Or.inl ⟨uniswapBurnFunctionCallRevert_totalSupplyUnderflow hcontract hargs
        hbalance (by omega),
        RD.uniswapSafeMathSubUnderflow_aw6_size164_shared rdSub1 (by omega)
          (hhash2Size.trans hmem) hhash2Read (by simp only [List.length_cons]; omega)⟩
  · exact Or.inl ⟨uniswapBurnFunctionCallRevert_balanceUnderflow hcontract hargs (by omega),
      RD.uniswapSafeMathSubUnderflow_aw6_size164_shared rdSub0 (by omega)
        (hhashSize.trans hmem) hhashRead (by simp only [List.length_cons]; omega)⟩


set_option maxRecDepth 2000000 in
theorem uniswapInternalBurnCallRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {value holderWord ret : UInt256}
    {R : List UInt256} {caller : Frame} {args : List Expr} {retVar : Ident}
    (evm : EVM.State) (holder : AccountAddress)
    (rd8302 : RD uniswapV2PairBytecode I g s0 ⟨8302⟩
      (value :: holderWord :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hholder : holder = AccountAddress.ofNat holderWord.toNat)
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [burnFunctionFromValue holder, burnFunctionValueValue value])
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_burn" args retVar) .reverted ∧
      RDrev uniswapV2PairBytecode g s0) ∨
    (∃ mem' k' C',
      ExecStmt config caller evm (.internalCall "_burn" args retVar)
        (.ok (resumeAfterInternalCall caller retVar none) (burnFunctionPostState evm holder value)) ∧
      accountMapEquiv (burnRuntimePostMap σ I holderWord value)
        (burnFunctionPostState evm holder value).accountMap ∧
      RD uniswapV2PairBytecode I g s0 ret R mem' feeToStaticcallActiveWords rdata
        (cA, burnRuntimePostMap σ I holderWord value) k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  rcases uniswapInternalBurnCallRuntimeCasesWithMemory evm holder rd8302 hAccounts henv hholder
      hcontract hargs hperm hmem hread64 hret hov with
    hrev | ⟨m, k', C', hb, ha, rd, hm, h64, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨m, k', C', hb, ha, rd, hm, h64⟩

end UniswapV2Pair

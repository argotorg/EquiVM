import Benchmarks.Dss.Vow.FileAddressFlapper

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `file(bytes32,address)` flapper branch body bridge -/

theorem evmAddress_accountAddress (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow, AccountAddress.size] using a.isLt)

theorem fileAddressVatTargetWord_accountMapEquiv
    {σ τ : AccountMap} (hAccounts : accountMapEquiv σ τ) (I : ExecutionEnv) :
    fileAddressVatTargetWord σ I = fileAddressVatTargetWord τ I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  simp [fileAddressVatTargetWord, vowAddressReturnWord, vowSlotWord, hslot]

theorem fileAddressFlapperTargetWord_accountMapEquiv
    {σ τ : AccountMap} (hAccounts : accountMapEquiv σ τ) (I : ExecutionEnv) :
    fileAddressFlapperTargetWord σ I = fileAddressFlapperTargetWord τ I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  simp [fileAddressFlapperTargetWord, vowAddressReturnWord, vowSlotWord, hslot]

theorem fileAddressFlapperAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat) =
      AccountAddress.ofUInt256 (fileAddressFlapperTargetWord σ I) := by
  apply Fin.ext
  simp [fileAddressFlapperTargetWord, vowAddressReturnWord]
  rfl

theorem fileAddressFlapperTargetWord_clean (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (fileAddressFlapperTargetWord σ I) solcAddrMask =
      fileAddressFlapperTargetWord σ I := by
  simpa [fileAddressFlapperTargetWord, vowAddressReturnWord] using
    (solcAddrMask_clean
      (w := UInt256.land (vowSlotWord ⟨2⟩ σ I) solcAddrMask)
      (solcAddrMask_result_canonical (vowSlotWord ⟨2⟩ σ I)))

theorem fileAddressDataKey_clean (I : ExecutionEnv) :
    UInt256.land solcAddrMask (fileAddressDataKey I) = fileAddressDataKey I := by
  rw [u256_land_comm]
  exact solcAddrMask_clean (fileAddressDataKey_canonical I)

theorem fileAddressVatAddressOf_initState_eq_target_of_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    fileAddressVatAddressOf
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) =
      AccountAddress.ofUInt256 (fileAddressVatTargetWord σ_evm I) := by
  rw [fileAddressVatAddressOf_initState_eq, fileAddressVatTargetWord_accountMapEquiv hAccounts]

theorem fileAddressFlapperAddressOf_initState_eq_target_of_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    fileAddressFlapperAddressOf
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) =
      AccountAddress.ofUInt256 (fileAddressFlapperTargetWord σ_evm I) := by
  rw [fileAddressFlapperAddressOf_initState_eq,
    fileAddressFlapperTargetWord_accountMapEquiv hAccounts]

theorem fileAddressNopeEncode_initState_flapper
    (cA gh bl σ σ₀ A I) (g : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    config.externalABI.encode? "nope"
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))] =
      some ((fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I) mem).readWithPadding
        fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat) := by
  have haddr :=
    fileAddressFlapperAddressOf_initState_eq (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hmask := fileAddressFlapperTargetWord_clean σ I
  simpa [haddr, accountAddress_ofUInt256_eq_ofNat_toNat, hmask] using
    fileAddressNopeEncode_eq (fileAddressFlapperTargetWord σ I) hmem

theorem fileAddressVatAddressOf_eq_target_of_env (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) :
    fileAddressVatAddressOf evm =
      AccountAddress.ofUInt256 (fileAddressVatTargetWord evm.accountMap I) := by
  apply Fin.ext
  simp [fileAddressVatAddressOf, fileAddressVatTargetWord, vowAddressReturnWord, henv,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    vowSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat]

theorem fileAddressSetFlapperAccountMap_equiv
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I) :
    accountMapEquiv
      (fileAddressSetFlapperAccountMap σ I (fileAddressDataKey I))
      (fileAddressSetFlapperEVM evm I).accountMap := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hval :
      setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (fileAddressDataKey I) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          (fileAddressDataKey I) := by
    rw [henv]
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord,
      hslot]
  have hbase :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
      (setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (fileAddressDataKey I))
      hAccounts
  simpa [fileAddressSetFlapperAccountMap, fileAddressSetFlapperEVM, storageStore_accountMap,
    henv, hval] using hbase

theorem fileAddressNopeCall_initState_EVMStateEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' : Substate} {out : ByteArray} {z : Bool}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ_evm I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ_evm I).toNat)]
        (z, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (z, { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }, out) true
      ∧ EVMStateEquiv
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', substate := A', createdAccounts := cA' }
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' } := by
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hState⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcall)
      (by simp [initState]) hAccounts
  refine ⟨σ'_solm, A'_solm, ?_, hState⟩
  have hVatAddr :=
    fileAddressVatAddressOf_initState_eq_target_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hAccounts
  have hFlapperAddr :=
    fileAddressFlapperAddressOf_initState_eq_target_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hAccounts
  simpa [fileAddressVatAddress_eq_target σ_evm I,
    fileAddressFlapperAddress_eq_target σ_evm I, hVatAddr, hFlapperAddr,
    accountAddress_ofUInt256_eq_ofNat_toNat, evmAddress_accountAddress]
    using hcallSolmRaw

theorem vowFileAddressFlapperNopeCallDepthLimitBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (_hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (fileAddressVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  have hVatTargetOrig :
      fileAddressVatTargetWord σ_evm I = fileAddressVatTargetWord σ_solm I :=
    fileAddressVatTargetWord_accountMapEquiv hAccounts I
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (fileAddressVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeNope
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (fileAddressVatTargetWord σ_evm I)
    rw [hsame, hVatTargetOrig]
    exact hzero
  let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ_solm I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq cA gh bl σ_solm σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := fileAddressVatTargetWord σ_solm I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  obtain ⟨_, _, hswitch⟩ := RD.vowFileAddressToSwitch hreach hsz68 hsize hauthSolc
  have hmatch :
      calldataWord I.calldata 4 = ABI.bytesToWord fileAddressFlapperBytes :=
    fileAddressWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, rd4300⟩ := RD.vowFileAddressNopeCallDepthLimit hswitch hmatch hmemAuth
    hread64 hcodeSizeNope hdepth
  let ANope := (evm0Solm.addAccessedAccount (EVM.address (fileAddressVatAddressOf evm0Solm))).substate
  have hcallNope :
      typedCallViaEVM config evm0Solm
        (EVM.address (fileAddressVatAddressOf evm0Solm)) "nope" 0
        [.address (fileAddressFlapperAddressOf evm0Solm)]
        (false, { evm0Solm with substate := ANope }, ByteArray.empty) true := by
    simpa [evm0Solm, ANope] using
      (callNotMade_depthLimit (cfg := config) (evm := evm0Solm)
        (tgt := EVM.address (fileAddressVatAddressOf evm0Solm)) (name := "nope")
        (args := [.address (fileAddressFlapperAddressOf evm0Solm)]) (callPerm := true)
        (fileAddressNopeEncode_initState_flapper cA gh bl σ_solm σ₀ A I g hmemAuth)
        (by simpa [evm0Solm, initState] using hdepth))
  exact vowFileAddressFlapperNopeCallFailureBodyCore (sel := sel) hcode hwv hdispatch hdecode
    rd4300 hcallNope (by decide +native) (by simpa [callerSlot] using hauthSolm) hwhat
    hvatCodeNope

theorem vowFileAddressFlapperHopeNoCodeAfterNopeSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cANope : Batteries.RBSet AccountAddress compare} {σNope : AccountMap}
    {ANope : Substate} {outNope memNope : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (rd4300 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ_evm I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memNope (UInt256.ofNat 6) outNope (cANope, σNope) k C)
    (hmemNope : memNope.size = 164)
    (hread64Nope : memNope.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcallNopeEvm :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ_evm I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ_evm I).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope, createdAccounts := cANope },
          outNope) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (fileAddressVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hVatTargetOrig :
      fileAddressVatTargetWord σ_evm I = fileAddressVatTargetWord σ_solm I :=
    fileAddressVatTargetWord_accountMapEquiv hAccounts I
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (fileAddressVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeNope
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (fileAddressVatTargetWord σ_evm I)
    rw [hsame, hVatTargetOrig]
    exact hzero
  let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ_solm I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq cA gh bl σ_solm σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := fileAddressVatTargetWord σ_solm I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hAccounts hcallNopeEvm
  let evmNopeSolm :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeSolm, substate := ANopeSolm, createdAccounts := cANope }
  have hcallNope :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeSolm, outNope) true := by
    simpa [evmNopeSolm] using hcallNopeSolm
  have hAccountsNope : accountMapEquiv σNope evmNopeSolm.accountMap := by
    simpa [evmNopeSolm, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeSolm.executionEnv = I := by
    simpa [evmNopeSolm, initState] using hStateNope.executionEnv
  let evmSetSolm := fileAddressSetFlapperEVM evmNopeSolm I
  have hAccountsSet :
      accountMapEquiv
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        evmSetSolm.accountMap := by
    simpa [evmSetSolm] using
      fileAddressSetFlapperAccountMap_equiv (I := I) hAccountsNope hEnvNope
  have hEnvSet : evmSetSolm.executionEnv = I := by
    simpa [evmSetSolm, fileAddressSetFlapperEVM, storageStore_executionEnv] using hEnvNope
  have hTargetSet :
      fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I =
        fileAddressVatTargetWord evmSetSolm.accountMap I :=
    fileAddressVatTargetWord_accountMapEquiv hAccountsSet I
  have hcodeSizeHopeSolm :
      Reasoning.Theory.extCodeSizeWord evmSetSolm.accountMap
        (fileAddressVatTargetWord evmSetSolm.accountMap I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsSet
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord evmSetSolm.accountMap
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) = ⟨0⟩ := by
      rw [← hsame]
      exact hcodeSizeHope
    simpa [hTargetSet] using hzeroAtEvmTarget
  have hvatNoCodeHope :
      (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNopeSolm I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNopeSolm I))).option 0
            (fun acc => acc.code.size))).toNat = 0 := by
    have haddr :
        fileAddressVatAddressOf evmSetSolm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord evmSetSolm.accountMap I) :=
      fileAddressVatAddressOf_eq_target_of_env evmSetSolm I hEnvSet
    simpa [evmSetSolm, State.lookupAccount] using
      fileAddress_extCodeSizeWord_zero_lookup_code_zero
        (σ := evmSetSolm.accountMap)
        (target := fileAddressVatTargetWord evmSetSolm.accountMap I)
        (addr := fileAddressVatAddressOf evmSetSolm) haddr hcodeSizeHopeSolm
  obtain ⟨_, _, rd4350⟩ := RD.vowFileAddressNopeSuccessStoreFlapperWithTarget rd4300 hperm
  exact vowFileAddressFlapperHopeNoCodeBodyCore (sel := sel) hcode hwv hdispatch hdecode
    rd4350 hmemNope hread64Nope hcodeSizeHope hcallNope
    (by simpa [callerSlot] using hauthSolm) hwhat hvatCodeNope hvatNoCodeHope

theorem vowFileAddressFlapperHopeCallFailureAfterNopeSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cANope cAHope : Batteries.RBSet AccountAddress compare}
    {σNope σHope : AccountMap} {ANope AHope : Substate}
    {outNope outHope memNope memHope rdataHope : ByteArray}
    {aw : UInt256} {k C kHope CHope : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (_rd4300 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ_evm I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memNope (UInt256.ofNat 6) outNope (cANope, σNope) k C)
    (hcallNopeEvm :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ_evm I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ_evm I).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope, createdAccounts := cANope },
          outNope) true)
    (rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
        fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memHope aw rdataHope (cAHope, σHope) kHope CHope)
    (hcallHopeEvm :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)
          createdAccounts := cANope }
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (false, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σHope, substate := AHope, createdAccounts := cAHope },
          outHope) true)
    (hrdataSize : rdataHope.size < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (fileAddressVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩)
    (hdepthLt : I.depth.val < 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hVatTargetOrig :
      fileAddressVatTargetWord σ_evm I = fileAddressVatTargetWord σ_solm I :=
    fileAddressVatTargetWord_accountMapEquiv hAccounts I
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (fileAddressVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeNope
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (fileAddressVatTargetWord σ_evm I)
    rw [hsame, hVatTargetOrig]
    exact hzero
  let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ_solm I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq cA gh bl σ_solm σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := fileAddressVatTargetWord σ_solm I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hAccounts hcallNopeEvm
  let evmNopeSolm :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeSolm, substate := ANopeSolm, createdAccounts := cANope }
  have hcallNope :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeSolm, outNope) true := by
    simpa [evmNopeSolm] using hcallNopeSolm
  have hAccountsNope : accountMapEquiv σNope evmNopeSolm.accountMap := by
    simpa [evmNopeSolm, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeSolm.executionEnv = I := by
    simpa [evmNopeSolm, initState] using hStateNope.executionEnv
  let evmSetSolm := fileAddressSetFlapperEVM evmNopeSolm I
  have hAccountsSet :
      accountMapEquiv
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        evmSetSolm.accountMap := by
    simpa [evmSetSolm] using
      fileAddressSetFlapperAccountMap_equiv (I := I) hAccountsNope hEnvNope
  have hEnvSet : evmSetSolm.executionEnv = I := by
    simpa [evmSetSolm, fileAddressSetFlapperEVM, storageStore_executionEnv] using hEnvNope
  have hTargetSet :
      fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I =
        fileAddressVatTargetWord evmSetSolm.accountMap I :=
    fileAddressVatTargetWord_accountMapEquiv hAccountsSet I
  have hcodeSizeHopeSolm :
      Reasoning.Theory.extCodeSizeWord evmSetSolm.accountMap
        (fileAddressVatTargetWord evmSetSolm.accountMap I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeHope
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsSet
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I)
    rw [hsame, hTargetSet]
    exact hzero
  have haddrHope :
      fileAddressVatAddressOf evmSetSolm =
        AccountAddress.ofUInt256 (fileAddressVatTargetWord evmSetSolm.accountMap I) :=
    fileAddressVatAddressOf_eq_target_of_env evmSetSolm I hEnvSet
  have hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNopeSolm I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNopeSolm I))).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evmSetSolm, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmSetSolm.accountMap)
        (target := fileAddressVatTargetWord evmSetSolm.accountMap I)
        (addr := fileAddressVatAddressOf evmSetSolm) haddrHope hcodeSizeHopeSolm
  let evmHopeEvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)
      createdAccounts := cANope }
  let evmSetSolmBase := { evmSetSolm with substate := evmHopeEvmIn.substate }
  have hCreatedBase : evmSetSolmBase.createdAccounts = evmHopeEvmIn.createdAccounts := by
    simp [evmSetSolmBase, evmHopeEvmIn, evmSetSolm, fileAddressSetFlapperEVM,
      evmNopeSolm, initState, storageStore_createdAccounts]
  have hEnvBase : evmSetSolmBase.executionEnv = evmHopeEvmIn.executionEnv := by
    simp [evmSetSolmBase, evmHopeEvmIn, hEnvSet, initState]
  obtain ⟨σHopeSolm, AHopeSolm0, hcallHopeBase, hAccountsHope⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSetSolmBase)
      (by simpa [evmHopeEvmIn] using hcallHopeEvm)
      (by simpa [evmHopeEvmIn, evmSetSolmBase] using hAccountsSet)
      (by
        simp [evmHopeEvmIn, evmSetSolmBase, evmSetSolm, fileAddressSetFlapperEVM,
          evmNopeSolm, initState, fileAddress_storageStore_σ₀])
      hCreatedBase
      (by
        simp [evmHopeEvmIn, evmSetSolmBase, evmSetSolm, fileAddressSetFlapperEVM,
          evmNopeSolm, initState, fileAddress_storageStore_genesisBlockHeader])
      (by
        simp [evmHopeEvmIn, evmSetSolmBase, evmSetSolm, fileAddressSetFlapperEVM,
          evmNopeSolm, initState, fileAddress_storageStore_blocks])
      (by simp [evmSetSolmBase, evmHopeEvmIn])
      hEnvBase
  have hdepthNeBase : evmSetSolmBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hdepthEqI : I.depth = 1024 := by
      simpa [evmSetSolmBase, hEnvSet] using hdepthEq
    rw [hdepthEqI] at hdepthLt
    norm_num at hdepthLt
  obtain ⟨AHopeSolm, hcallHopeRaw⟩ :=
    fileAddress_typedCallViaEVM_zero_setSubstate hcallHopeBase hdepthNeBase
      evmSetSolm.substate
  let evmHopeSolm :=
    { evmSetSolm with
      accountMap := σHopeSolm
      substate := AHopeSolm
      createdAccounts := cAHope }
  have hcallHope :
      typedCallViaEVM config evmSetSolm
        (EVM.address (fileAddressVatAddressOf evmSetSolm))
        "hope" 0 [.address (fileAddressData I)] (false, evmHopeSolm, outHope) true := by
    simpa [evmHopeSolm, evmSetSolmBase, hTargetSet, haddrHope,
      fileAddressVatAddress_eq_target
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I,
      fileAddressData_value_masked, fileAddressDataKey_clean, accountAddress_ofUInt256_eq_ofNat_toNat,
      evmAddress_accountAddress] using hcallHopeRaw
  exact vowFileAddressFlapperHopeCallFailureBodyCore (sel := sel) hcode hwv hdispatch hdecode
    rd4423 hcallNope hcallHope hrdataSize (by simpa [callerSlot] using hauthSolm)
    hwhat hvatCodeNope hvatCodeHope

theorem vowFileAddressFlapperHopeSuccessAfterNopeSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cANope cAHope : Batteries.RBSet AccountAddress compare}
    {σNope σHope : AccountMap} {ANope AHope : Substate}
    {outNope outHope memHope rdataHope : ByteArray}
    {aw : UInt256} {kHope CHope : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hcallNopeEvm :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ_evm I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ_evm I).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope, createdAccounts := cANope },
          outNope) true)
    (rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
        fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memHope aw rdataHope (cAHope, σHope) kHope CHope)
    (hcallHopeEvm :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)
          createdAccounts := cANope }
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σHope, substate := AHope, createdAccounts := cAHope },
          outHope) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (fileAddressVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩)
    (hdepthLt : I.depth.val < 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hVatTargetOrig :
      fileAddressVatTargetWord σ_evm I = fileAddressVatTargetWord σ_solm I :=
    fileAddressVatTargetWord_accountMapEquiv hAccounts I
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (fileAddressVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeNope
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (fileAddressVatTargetWord σ_evm I)
    rw [hsame, hVatTargetOrig]
    exact hzero
  let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ_solm I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq cA gh bl σ_solm σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := fileAddressVatTargetWord σ_solm I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hAccounts hcallNopeEvm
  let evmNopeSolm :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeSolm, substate := ANopeSolm, createdAccounts := cANope }
  have hcallNope :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeSolm, outNope) true := by
    simpa [evmNopeSolm] using hcallNopeSolm
  have hAccountsNope : accountMapEquiv σNope evmNopeSolm.accountMap := by
    simpa [evmNopeSolm, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeSolm.executionEnv = I := by
    simpa [evmNopeSolm, initState] using hStateNope.executionEnv
  let evmSetSolm := fileAddressSetFlapperEVM evmNopeSolm I
  have hAccountsSet :
      accountMapEquiv
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        evmSetSolm.accountMap := by
    simpa [evmSetSolm] using
      fileAddressSetFlapperAccountMap_equiv (I := I) hAccountsNope hEnvNope
  have hEnvSet : evmSetSolm.executionEnv = I := by
    simpa [evmSetSolm, fileAddressSetFlapperEVM, storageStore_executionEnv] using hEnvNope
  have hTargetSet :
      fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I =
        fileAddressVatTargetWord evmSetSolm.accountMap I :=
    fileAddressVatTargetWord_accountMapEquiv hAccountsSet I
  have hcodeSizeHopeSolm :
      Reasoning.Theory.extCodeSizeWord evmSetSolm.accountMap
        (fileAddressVatTargetWord evmSetSolm.accountMap I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeHope
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsSet
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I)
    rw [hsame, hTargetSet]
    exact hzero
  have haddrHope :
      fileAddressVatAddressOf evmSetSolm =
        AccountAddress.ofUInt256 (fileAddressVatTargetWord evmSetSolm.accountMap I) :=
    fileAddressVatAddressOf_eq_target_of_env evmSetSolm I hEnvSet
  have hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNopeSolm I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNopeSolm I))).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evmSetSolm, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmSetSolm.accountMap)
        (target := fileAddressVatTargetWord evmSetSolm.accountMap I)
        (addr := fileAddressVatAddressOf evmSetSolm) haddrHope hcodeSizeHopeSolm
  let evmHopeEvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)
      createdAccounts := cANope }
  let evmSetSolmBase := { evmSetSolm with substate := evmHopeEvmIn.substate }
  have hCreatedBase : evmSetSolmBase.createdAccounts = evmHopeEvmIn.createdAccounts := by
    simp [evmSetSolmBase, evmHopeEvmIn, evmSetSolm, fileAddressSetFlapperEVM,
      evmNopeSolm, initState, storageStore_createdAccounts]
  have hEnvBase : evmSetSolmBase.executionEnv = evmHopeEvmIn.executionEnv := by
    simp [evmSetSolmBase, evmHopeEvmIn, hEnvSet, initState]
  obtain ⟨σHopeSolm, AHopeSolm0, hcallHopeBase, hAccountsHope⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSetSolmBase)
      (by simpa [evmHopeEvmIn] using hcallHopeEvm)
      (by simpa [evmHopeEvmIn, evmSetSolmBase] using hAccountsSet)
      (by
        simp [evmHopeEvmIn, evmSetSolmBase, evmSetSolm, fileAddressSetFlapperEVM,
          evmNopeSolm, initState, fileAddress_storageStore_σ₀])
      hCreatedBase
      (by
        simp [evmHopeEvmIn, evmSetSolmBase, evmSetSolm, fileAddressSetFlapperEVM,
          evmNopeSolm, initState, fileAddress_storageStore_genesisBlockHeader])
      (by
        simp [evmHopeEvmIn, evmSetSolmBase, evmSetSolm, fileAddressSetFlapperEVM,
          evmNopeSolm, initState, fileAddress_storageStore_blocks])
      (by simp [evmSetSolmBase, evmHopeEvmIn])
      hEnvBase
  have hdepthNeBase : evmSetSolmBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hdepthEqI : I.depth = 1024 := by
      simpa [evmSetSolmBase, hEnvSet] using hdepthEq
    rw [hdepthEqI] at hdepthLt
    norm_num at hdepthLt
  obtain ⟨AHopeSolm, hcallHopeRaw⟩ :=
    fileAddress_typedCallViaEVM_zero_setSubstate hcallHopeBase hdepthNeBase
      evmSetSolm.substate
  let evmHopeSolm :=
    { evmSetSolm with
      accountMap := σHopeSolm
      substate := AHopeSolm
      createdAccounts := cAHope }
  have hcallHope :
      typedCallViaEVM config evmSetSolm
        (EVM.address (fileAddressVatAddressOf evmSetSolm))
        "hope" 0 [.address (fileAddressData I)] (true, evmHopeSolm, outHope) true := by
    simpa [evmHopeSolm, evmSetSolmBase, hTargetSet, haddrHope,
      fileAddressVatAddress_eq_target
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I,
      fileAddressData_value_masked, fileAddressDataKey_clean, accountAddress_ofUInt256_eq_ofNat_toNat,
      evmAddress_accountAddress] using hcallHopeRaw
  have hcreated : (cAHope, σHope).1 = evmHopeSolm.createdAccounts := by
    rfl
  have hAccountsFinal : accountMapEquiv (cAHope, σHope).2 evmHopeSolm.accountMap := by
    simpa [evmHopeSolm] using hAccountsHope
  exact vowFileAddressFlapperHopeSuccessBodyCore (sel := sel) hcode hwv hdispatch hdecode
    rd4423 hcallNope hcallHope (by simpa [callerSlot] using hauthSolm)
    hwhat hvatCodeNope hvatCodeHope hcreated hAccountsFinal

theorem vowFileAddressFlapperAuthorizedBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  have hVatTargetOrig :
      fileAddressVatTargetWord σ_evm I = fileAddressVatTargetWord σ_solm I :=
    fileAddressVatTargetWord_accountMapEquiv hAccounts I
  obtain ⟨_, _, hswitch⟩ := RD.vowFileAddressToSwitch hreach hsz68 hsize hauthSolc
  have hmatch :
      calldataWord I.calldata 4 = ABI.bytesToWord fileAddressFlapperBytes :=
    fileAddressWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  by_cases hcodeSizeNopeZero :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (fileAddressVatTargetWord σ_evm I) = ⟨0⟩
  · exact vowFileAddressFlapperNopeNoCodeBodyCore (sel := sel) hcode hwv hperm hsz68
      hsize hdispatch hdecode hreach hAccounts hauthEvm hwhat hcodeSizeNopeZero
  have hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (fileAddressVatTargetWord σ_evm I) ≠ ⟨0⟩ :=
    hcodeSizeNopeZero
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (fileAddressVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeNope
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (fileAddressVatTargetWord σ_evm I)
    rw [hsame, hVatTargetOrig]
    exact hzero
  let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ_solm I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq cA gh bl σ_solm σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := fileAddressVatTargetWord σ_solm I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  by_cases hdepthLt : I.depth.val < 1024
  · obtain ⟨cANope, σNope, zNope, outNope, ANope, k4300, C4300,
        rd4300, hcallNopeEvm, houtNopeSize⟩ :=
      RD.vowFileAddressNopePostCall hswitch hmatch hmemAuth hread64 hcodeSizeNope
        hdepthLt hperm
    cases zNope
    · have rd4300False : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
          (⟨0⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
            fileAddressVatTargetWord σ_evm I :: fileAddressDataKey I ::
            calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ_evm I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
          (UInt256.ofNat 6) outNope (cANope, σNope) k4300 C4300 := by
        simpa using rd4300
      have hcallNopeFalse :
          typedCallViaEVM config
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ_evm I).toNat))
            "nope" 0
            [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ_evm I).toNat)]
            (false, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σNope, substate := ANope, createdAccounts := cANope },
              outNope) true := by
        simpa using hcallNopeEvm
      obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, _hStateNope⟩ :=
        fileAddressNopeCall_initState_EVMStateEquiv hAccounts hcallNopeFalse
      let evmNopeSolm :=
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σNopeSolm, substate := ANopeSolm, createdAccounts := cANope }
      have hcallNope :
          typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (fileAddressVatAddressOf
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
            [.address (fileAddressFlapperAddressOf
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
            (false, evmNopeSolm, outNope) true := by
        simpa [evmNopeSolm] using hcallNopeSolm
      exact vowFileAddressFlapperNopeCallFailureBodyCore (sel := sel) hcode hwv
        hdispatch hdecode rd4300False hcallNope houtNopeSize
        (by simpa [callerSlot] using hauthSolm) hwhat hvatCodeNope
    · have rd4300True : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
          (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
            fileAddressVatTargetWord σ_evm I :: fileAddressDataKey I ::
            calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ_evm I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
          (UInt256.ofNat 6) outNope (cANope, σNope) k4300 C4300 := by
        simpa using rd4300
      have hcallNopeTrue :
          typedCallViaEVM config
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ_evm I).toNat))
            "nope" 0
            [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ_evm I).toNat)]
            (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σNope, substate := ANope, createdAccounts := cANope },
              outNope) true := by
        simpa using hcallNopeEvm
      have hmemNope :
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ_evm I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 164 :=
        fileAddressNopeCalldataMem_size _ hmemAuth
      have hreadNope :
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ_evm I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        fileAddressNopeCalldataMem_read64 _ hmemAuth hread64
      by_cases hcodeSizeHopeZero :
          Reasoning.Theory.extCodeSizeWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
            (fileAddressVatTargetWord
              (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) = ⟨0⟩
      · exact vowFileAddressFlapperHopeNoCodeAfterNopeSuccessBodyCore (sel := sel)
          hcode hwv hperm hdispatch hdecode rd4300True hmemNope hreadNope
          hcallNopeTrue hAccounts hauthEvm hwhat hcodeSizeNope hcodeSizeHopeZero
      have hcodeSizeHope :
          Reasoning.Theory.extCodeSizeWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
            (fileAddressVatTargetWord
              (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩ :=
        hcodeSizeHopeZero
      obtain ⟨cAHope, σHope, zHope, outHope, AHope, k4423, C4423,
          rd4423, hcallHopeEvm, houtHopeSize⟩ :=
        RD.vowFileAddressNopeSuccessToHopePostCall rd4300True hperm hmemNope hreadNope
          hcodeSizeHope hdepthLt
      cases zHope
      · have rd4423False : RD vowBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
            (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
              fileAddressVatTargetWord
                (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
              fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
            (fileAddressHopeCalldataMem (UInt256.land solcAddrMask (fileAddressDataKey I))
              (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ_evm I)
                (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)))
            (UInt256.ofNat 6) outHope (cAHope, σHope) k4423 C4423 := by
          simpa [fileAddressDataKey_clean] using rd4423
        have hcallHopeFalse :
            typedCallViaEVM config
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)
                createdAccounts := cANope }
              (EVM.address (AccountAddress.ofNat
                (fileAddressVatTargetWord
                  (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
              "hope" 0 [.address (AccountAddress.ofNat
                (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
              (false, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σHope, substate := AHope, createdAccounts := cAHope },
                outHope) true := by
          simpa using hcallHopeEvm
        exact vowFileAddressFlapperHopeCallFailureAfterNopeSuccessBodyCore (sel := sel)
          hcode hwv hdispatch hdecode rd4300True hcallNopeTrue rd4423False
          hcallHopeFalse houtHopeSize hAccounts hauthEvm hwhat hcodeSizeNope
          hcodeSizeHope hdepthLt
      · have rd4423True : RD vowBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
            (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
              fileAddressVatTargetWord
                (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
              fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
            (fileAddressHopeCalldataMem (UInt256.land solcAddrMask (fileAddressDataKey I))
              (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ_evm I)
                (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)))
            (UInt256.ofNat 6) outHope (cAHope, σHope) k4423 C4423 := by
          simpa [fileAddressDataKey_clean] using rd4423
        have hcallHopeTrue :
            typedCallViaEVM config
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)
                createdAccounts := cANope }
              (EVM.address (AccountAddress.ofNat
                (fileAddressVatTargetWord
                  (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
              "hope" 0 [.address (AccountAddress.ofNat
                (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
              (true, { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σHope, substate := AHope, createdAccounts := cAHope },
                outHope) true := by
          simpa using hcallHopeEvm
        exact vowFileAddressFlapperHopeSuccessAfterNopeSuccessBodyCore (sel := sel)
          hcode hwv hdispatch hdecode hcallNopeTrue rd4423True hcallHopeTrue
          hAccounts hauthEvm hwhat hcodeSizeNope hcodeSizeHope hdepthLt
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    exact vowFileAddressFlapperNopeCallDepthLimitBodyCore (sel := sel) hcode hwv hperm
      hsz68 hsize hdispatch hdecode hreach hAccounts hauthEvm hwhat hcodeSizeNope
      hdepthEq

theorem vowFileAddressFlapperBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  by_cases hauthEvm : vowSlotWord callerSlot σ_evm I = ⟨1⟩
  · exact vowFileAddressFlapperAuthorizedBodyCore (sel := sel) hcode hwv hperm hsz68
      hsize hdispatch hdecode hreach hAccounts (by simpa [callerSlot] using hauthEvm)
      hwhat
  · exact vowFileAddressAuthRevertBodyCore (sel := sel) hcode hwv hsz68 hsize hdispatch
      hdecode hreach hAccounts (by simpa [callerSlot] using hauthEvm)

theorem vowFileAddressFlapperBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  exact vowFileAddressFlapperBodyCore (sel := vowSelWord I) hcode hwv hperm hsz68 hsize
    (vowDispatch_fileAddress hsel)
    (by simpa [fileAddressLocals] using vowDecode_fileAddress_ok (I := I) hsz68)
    (vowReachFileAddressBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts hwhat

theorem vowFileAddressBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 68
  · exact vowFileAddressShort hcode hsize hperm hwv hsz4 hshort hsel hAccounts
  have hsz68 : 68 ≤ I.calldata.size := by omega
  by_cases hwhat : fileAddressWhat I = fileAddressFlapperBytes
  · exact vowFileAddressFlapperBody hcode hsize hperm hwv hsz68 hsel hAccounts hwhat
  · exact vowFileAddressNonFlapperBody hcode hsize hperm hwv hsz68 hsel hAccounts hwhat

end Benchmarks.Dss.Vow

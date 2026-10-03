import Benchmarks.Dss.Vow.KissSuccess
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

theorem fileAddressNopeEncode_initState_flapper
    (σ σ₀ A I) (g : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    config.externalABI.encode? "nope"
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))] =
      some ((fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I) mem).readWithPadding
        fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat) := by
  have haddr :=
    fileAddressFlapperAddressOf_initState_eq
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
    (hAccounts : Eq σ evm.accountMap)
    (henv : evm.executionEnv = I) :
    Eq
      (fileAddressSetFlapperAccountMap σ I (fileAddressDataKey I))
      (fileAddressSetFlapperEVM evm I).accountMap := by
  have hval :
      setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (fileAddressDataKey I) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          (fileAddressDataKey I) := by
    rw [henv, hAccounts]
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord]
  have hbase := congrArg
    (fun accounts => sstoreAccountMap I.codeOwner accounts ⟨2⟩
      (setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (fileAddressDataKey I)))
    hAccounts
  simpa [fileAddressSetFlapperAccountMap, fileAddressSetFlapperEVM, storageStore_accountMap,
    henv, hval] using hbase

theorem fileAddressNopeCall_initState_EVMStateEquiv
    {σ σ₀ A I} {g : UInt256}
    {σ' : AccountMap}
    {A' : Substate} {out : ByteArray} {z : Bool}
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (z, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' }, out) true) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (z, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm, substate := A'_solm }, out) true
      ∧ EVMStateEquiv
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', substate := A' }
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm, substate := A'_solm } := by
  refine ⟨σ', A', ?_, ⟨rfl, rfl⟩⟩
  have hVatAddr := fileAddressVatAddressOf_initState_eq σ σ₀ A I g
  have hFlapperAddr := fileAddressFlapperAddressOf_initState_eq σ σ₀ A I g
  simpa [fileAddressVatAddress_eq_target σ I,
    fileAddressFlapperAddress_eq_target σ I, hVatAddr, hFlapperAddr,
    accountAddress_ofUInt256_eq_ofNat_toNat, evmAddress_accountAddress]
    using hcall

theorem vowFileAddressFlapperNopeCallDepthLimitBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (_hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthSolm : vowSlotWord callerSlot σ I = ⟨1⟩ := hauthEvm
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
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
        (fileAddressNopeEncode_initState_flapper σ σ₀ A I g hmemAuth)
        (by simpa [evm0Solm, initState] using hdepth))
  exact vowFileAddressFlapperNopeCallFailureBodyCore (sel := sel) hcode hwv hdispatch hdecode
    rd4300 hcallNope (by native_decide) (by simpa [callerSlot] using hauthSolm) hwhat
    hvatCodeNope

theorem vowFileAddressFlapperHopeNoCodeAfterNopeSuccessBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σNope : AccountMap}
    {ANope : Substate} {outNope memNope : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (rd4300 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memNope (UInt256.ofNat 6) outNope σNope k C)
    (hmemNope : memNope.size = 164)
    (hread64Nope : memNope.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcallNopeEvm :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope },
          outNope) true)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthSolm : vowSlotWord callerSlot σ I = ⟨1⟩ := hauthEvm
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hcallNopeEvm
  let evmNopeSolm :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeSolm, substate := ANopeSolm }
  have hcallNope :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeSolm, outNope) true := by
    simpa [evmNopeSolm] using hcallNopeSolm
  have hAccountsNope : Eq σNope evmNopeSolm.accountMap := by
    simpa [evmNopeSolm, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeSolm.executionEnv = I := by
    simpa [evmNopeSolm, initState] using hStateNope.executionEnv
  let evmSetSolm := fileAddressSetFlapperEVM evmNopeSolm I
  have hAccountsSet :
      Eq
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        evmSetSolm.accountMap := by
    simpa [evmSetSolm] using
      fileAddressSetFlapperAccountMap_equiv (I := I) hAccountsNope hEnvNope
  have hEnvSet : evmSetSolm.executionEnv = I := by
    simpa [evmSetSolm, fileAddressSetFlapperEVM, storageStore_executionEnv] using hEnvNope
  have hcodeSizeHopeSolm :
      Reasoning.Theory.extCodeSizeWord evmSetSolm.accountMap
        (fileAddressVatTargetWord evmSetSolm.accountMap I) = ⟨0⟩ := by
    simpa [hAccountsSet] using hcodeSizeHope
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
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
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
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memNope (UInt256.ofNat 6) outNope σNope k C)
    (hcallNopeEvm :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope },
          outNope) true)
    (rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
        fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memHope aw rdataHope σHope kHope CHope)
    (hcallHopeEvm :
      typedCallViaEVM config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (false, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σHope, substate := AHope },
          outHope) true)
    (hrdataSize : rdataHope.size < UInt256.size)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩)
    (hdepthLt : I.depth.val < 1024) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthSolm : vowSlotWord callerSlot σ I = ⟨1⟩ := hauthEvm
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hcallNopeEvm
  let evmNopeSolm :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeSolm, substate := ANopeSolm }
  have hcallNope :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeSolm, outNope) true := by
    simpa [evmNopeSolm] using hcallNopeSolm
  have hAccountsNope : Eq σNope evmNopeSolm.accountMap := by
    simpa [evmNopeSolm, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeSolm.executionEnv = I := by
    simpa [evmNopeSolm, initState] using hStateNope.executionEnv
  let evmSetSolm := fileAddressSetFlapperEVM evmNopeSolm I
  have hAccountsSet :
      Eq
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
    congrArg (fun accounts => fileAddressVatTargetWord accounts I) hAccountsSet
  have hcodeSizeHopeSolm :
      Reasoning.Theory.extCodeSizeWord evmSetSolm.accountMap
        (fileAddressVatTargetWord evmSetSolm.accountMap I) ≠ ⟨0⟩ := by
    simpa [hAccountsSet] using hcodeSizeHope
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
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
  let evmSetSolmBase := { evmSetSolm with substate := evmHopeEvmIn.substate }
  have hNopeMap : σNope = σNopeSolm := by
    simpa [evmNopeSolm] using hAccountsNope
  have hHopeInput : evmSetSolmBase = evmHopeEvmIn := by
    cases hFind : σNopeSolm.find? I.codeOwner <;>
      simp [evmSetSolmBase, evmHopeEvmIn, evmSetSolm, evmNopeSolm,
        fileAddressSetFlapperAccountMap,
        Solm.EVM.storageStore, Solm.EVM.storageLoad, State.setAccount,
        State.lookupAccount, Account.lookupStorage, Account.updateStorage,
        sstoreAccountMap, solcSlotWord, Option.option, hNopeMap, hFind, initState]
  have hcallHopeBase :
      typedCallViaEVM config evmSetSolmBase
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (false, { evmSetSolmBase with accountMap := σHope, substate := AHope }, outHope)
        true := by
    simpa [hHopeInput, evmHopeEvmIn] using hcallHopeEvm
  have hdepthNeBase : evmSetSolmBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hdepthEqI : I.depth = 1024 := by
      simpa [evmSetSolmBase, hEnvSet] using hdepthEq
    rw [hdepthEqI] at hdepthLt
    norm_num at hdepthLt
  obtain ⟨AHopeSolm, hcallHopeRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallHopeBase hdepthNeBase
      evmSetSolm.substate
  let evmHopeSolm :=
    { evmSetSolm with
      accountMap := σHope
      substate := AHopeSolm }
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
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
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
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope },
          outNope) true)
    (rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
        fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memHope aw rdataHope σHope kHope CHope)
    (hcallHopeEvm :
      typedCallViaEVM config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σHope, substate := AHope },
          outHope) true)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩)
    (hdepthLt : I.depth.val < 1024) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthSolm : vowSlotWord callerSlot σ I = ⟨1⟩ := hauthEvm
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hcallNopeEvm
  let evmNopeSolm :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeSolm, substate := ANopeSolm }
  have hcallNope :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeSolm, outNope) true := by
    simpa [evmNopeSolm] using hcallNopeSolm
  have hAccountsNope : Eq σNope evmNopeSolm.accountMap := by
    simpa [evmNopeSolm, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeSolm.executionEnv = I := by
    simpa [evmNopeSolm, initState] using hStateNope.executionEnv
  let evmSetSolm := fileAddressSetFlapperEVM evmNopeSolm I
  have hAccountsSet :
      Eq
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
    congrArg (fun accounts => fileAddressVatTargetWord accounts I) hAccountsSet
  have hcodeSizeHopeSolm :
      Reasoning.Theory.extCodeSizeWord evmSetSolm.accountMap
        (fileAddressVatTargetWord evmSetSolm.accountMap I) ≠ ⟨0⟩ := by
    simpa [hAccountsSet] using hcodeSizeHope
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
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
  let evmSetSolmBase := { evmSetSolm with substate := evmHopeEvmIn.substate }
  have hNopeMap : σNope = σNopeSolm := by
    simpa [evmNopeSolm] using hAccountsNope
  have hHopeInput : evmSetSolmBase = evmHopeEvmIn := by
    cases hFind : σNopeSolm.find? I.codeOwner <;>
      simp [evmSetSolmBase, evmHopeEvmIn, evmSetSolm, evmNopeSolm,
        fileAddressSetFlapperAccountMap,
        Solm.EVM.storageStore, Solm.EVM.storageLoad, State.setAccount,
        State.lookupAccount, Account.lookupStorage, Account.updateStorage,
        sstoreAccountMap, solcSlotWord, Option.option, hNopeMap, hFind, initState]
  have hcallHopeBase :
      typedCallViaEVM config evmSetSolmBase
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (true, { evmSetSolmBase with accountMap := σHope, substate := AHope }, outHope)
        true := by
    simpa [hHopeInput, evmHopeEvmIn] using hcallHopeEvm
  have hdepthNeBase : evmSetSolmBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hdepthEqI : I.depth = 1024 := by
      simpa [evmSetSolmBase, hEnvSet] using hdepthEq
    rw [hdepthEqI] at hdepthLt
    norm_num at hdepthLt
  obtain ⟨AHopeSolm, hcallHopeRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallHopeBase hdepthNeBase
      evmSetSolm.substate
  let evmHopeSolm :=
    { evmSetSolm with
      accountMap := σHope
      substate := AHopeSolm }
  have hcallHope :
      typedCallViaEVM config evmSetSolm
        (EVM.address (fileAddressVatAddressOf evmSetSolm))
        "hope" 0 [.address (fileAddressData I)] (true, evmHopeSolm, outHope) true := by
    simpa [evmHopeSolm, evmSetSolmBase, hTargetSet, haddrHope,
      fileAddressVatAddress_eq_target
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I,
      fileAddressData_value_masked, fileAddressDataKey_clean, accountAddress_ofUInt256_eq_ofNat_toNat,
      evmAddress_accountAddress] using hcallHopeRaw
  have hAccountsFinal : Eq σHope evmHopeSolm.accountMap := rfl
  exact vowFileAddressFlapperHopeSuccessBodyCore (sel := sel) hcode hwv hdispatch hdecode
    rd4423 hcallNope hcallHope (by simpa [callerSlot] using hauthSolm)
    hwhat hvatCodeNope hvatCodeHope hAccountsFinal

theorem vowFileAddressFlapperAuthorizedBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthSolm : vowSlotWord callerSlot σ I = ⟨1⟩ := hauthEvm
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
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
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) = ⟨0⟩
  · exact vowFileAddressFlapperNopeNoCodeBodyCore (sel := sel) hcode hwv hperm hsz68
      hsize hdispatch hdecode hreach hauthEvm hwhat hcodeSizeNopeZero
  have hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ :=
    hcodeSizeNopeZero
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Solm =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Solm] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Solm, initState, State.lookupAccount] using
      fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Solm) haddr hcodeSizeSolm
  by_cases hdepthLt : I.depth.val < 1024
  · obtain ⟨σNope, zNope, outNope, ANope, k4300, C4300,
        rd4300, hcallNopeEvm, houtNopeSize⟩ :=
      RD.vowFileAddressNopePostCall hswitch hmatch hmemAuth hread64 hcodeSizeNope
        hdepthLt hperm
    cases zNope
    · have rd4300False : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
          (⟨0⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
            fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
            calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
          (UInt256.ofNat 6) outNope σNope k4300 C4300 := by
        simpa using rd4300
      have hcallNopeFalse :
          typedCallViaEVM config
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
            "nope" 0
            [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
            (false, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σNope, substate := ANope },
              outNope) true := by
        simpa using hcallNopeEvm
      obtain ⟨σNopeSolm, ANopeSolm, hcallNopeSolm, _hStateNope⟩ :=
        fileAddressNopeCall_initState_EVMStateEquiv hcallNopeFalse
      let evmNopeSolm :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σNopeSolm, substate := ANopeSolm }
      have hcallNope :
          typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (fileAddressVatAddressOf
              (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
            [.address (fileAddressFlapperAddressOf
              (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
            (false, evmNopeSolm, outNope) true := by
        simpa [evmNopeSolm] using hcallNopeSolm
      exact vowFileAddressFlapperNopeCallFailureBodyCore (sel := sel) hcode hwv
        hdispatch hdecode rd4300False hcallNope houtNopeSize
        (by simpa [callerSlot] using hauthSolm) hwhat hvatCodeNope
    · have rd4300True : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
          (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
            fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
            calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
          (UInt256.ofNat 6) outNope σNope k4300 C4300 := by
        simpa using rd4300
      have hcallNopeTrue :
          typedCallViaEVM config
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
            "nope" 0
            [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
            (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σNope, substate := ANope },
              outNope) true := by
        simpa using hcallNopeEvm
      have hmemNope :
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 164 :=
        fileAddressNopeCalldataMem_size _ hmemAuth
      have hreadNope :
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
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
          hcallNopeTrue hauthEvm hwhat hcodeSizeNope hcodeSizeHopeZero
      have hcodeSizeHope :
          Reasoning.Theory.extCodeSizeWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
            (fileAddressVatTargetWord
              (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩ :=
        hcodeSizeHopeZero
      obtain ⟨σHope, zHope, outHope, AHope, k4423, C4423,
          rd4423, hcallHopeEvm, houtHopeSize⟩ :=
        RD.vowFileAddressNopeSuccessToHopePostCall rd4300True hperm hmemNope hreadNope
          hcodeSizeHope hdepthLt
      cases zHope
      · have rd4423False : RD vowBytecode I (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
            (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
              fileAddressVatTargetWord
                (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
              fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
            (fileAddressHopeCalldataMem (UInt256.land solcAddrMask (fileAddressDataKey I))
              (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
                (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)))
            (UInt256.ofNat 6) outHope σHope k4423 C4423 := by
          simpa [fileAddressDataKey_clean] using rd4423
        have hcallHopeFalse :
            typedCallViaEVM config
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
              (EVM.address (AccountAddress.ofNat
                (fileAddressVatTargetWord
                  (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
              "hope" 0 [.address (AccountAddress.ofNat
                (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
              (false, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σHope, substate := AHope },
                outHope) true := by
          simpa using hcallHopeEvm
        exact vowFileAddressFlapperHopeCallFailureAfterNopeSuccessBodyCore (sel := sel)
          hcode hwv hdispatch hdecode rd4300True hcallNopeTrue rd4423False
          hcallHopeFalse houtHopeSize hauthEvm hwhat hcodeSizeNope
          hcodeSizeHope hdepthLt
      · have rd4423True : RD vowBytecode I (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
            (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
              fileAddressVatTargetWord
                (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
              fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
            (fileAddressHopeCalldataMem (UInt256.land solcAddrMask (fileAddressDataKey I))
              (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
                (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)))
            (UInt256.ofNat 6) outHope σHope k4423 C4423 := by
          simpa [fileAddressDataKey_clean] using rd4423
        have hcallHopeTrue :
            typedCallViaEVM config
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
              (EVM.address (AccountAddress.ofNat
                (fileAddressVatTargetWord
                  (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
              "hope" 0 [.address (AccountAddress.ofNat
                (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
              (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σHope, substate := AHope },
                outHope) true := by
          simpa using hcallHopeEvm
        exact vowFileAddressFlapperHopeSuccessAfterNopeSuccessBodyCore (sel := sel)
          hcode hwv hdispatch hdecode hcallNopeTrue rd4423True hcallHopeTrue
          hauthEvm hwhat hcodeSizeNope hcodeSizeHope hdepthLt
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    exact vowFileAddressFlapperNopeCallDepthLimitBodyCore (sel := sel) hcode hwv hperm
      hsz68 hsize hdispatch hdecode hreach hauthEvm hwhat hcodeSizeNope
      hdepthEq

theorem vowFileAddressFlapperBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  by_cases hauthEvm : vowSlotWord callerSlot σ I = ⟨1⟩
  · exact vowFileAddressFlapperAuthorizedBodyCore (sel := sel) hcode hwv hperm hsz68
      hsize hdispatch hdecode hreach (by simpa [callerSlot] using hauthEvm)
      hwhat
  · exact vowFileAddressAuthRevertBodyCore (sel := sel) hcode hwv hsz68 hsize hdispatch
      hdecode hreach (by simpa [callerSlot] using hauthEvm)

theorem vowFileAddressFlapperBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  exact vowFileAddressFlapperBodyCore (sel := vowSelWord I) hcode hwv hperm hsz68 hsize
    (vowDispatch_fileAddress hsel)
    (by simpa [fileAddressLocals] using vowDecode_fileAddress_ok (I := I) hsz68)
    (vowReachFileAddressBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hwhat

theorem vowFileAddressBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 68
  · exact vowFileAddressShort hcode hsize hperm hwv hsz4 hshort hsel
  have hsz68 : 68 ≤ I.calldata.size := by omega
  by_cases hwhat : fileAddressWhat I = fileAddressFlapperBytes
  · exact vowFileAddressFlapperBody hcode hsize hperm hwv hsz68 hsel hwhat
  · exact vowFileAddressNonFlapperBody hcode hsize hperm hwv hsz68 hsel hwhat

end Benchmarks.Dss.Vow

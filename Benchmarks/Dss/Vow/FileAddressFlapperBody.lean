import Reasoning.WordArithmetic
import Benchmarks.Dss.Vow.KissSuccess
import Benchmarks.Dss.Vow.FileAddressFlapper

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `file(bytes32,address)` flapper branch body bridge -/


theorem fileAddressFlapperAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat) =
      AccountAddress.ofUInt256 (fileAddressFlapperTargetWord σ I) := by
  apply Fin.ext
  simp [fileAddressFlapperTargetWord, solcAddressSlotWord]
  rfl

theorem fileAddressFlapperTargetWord_clean (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (fileAddressFlapperTargetWord σ I) solcAddrMask =
      fileAddressFlapperTargetWord σ I := by
  simpa [fileAddressFlapperTargetWord, solcAddressSlotWord] using
    (solcAddrMask_clean
      (w := UInt256.land (solcSlotWordAt ⟨2⟩ σ I) solcAddrMask)
      (solcAddrMask_result_canonical (solcSlotWordAt ⟨2⟩ σ I)))

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
  simp [fileAddressVatAddressOf, fileAddressVatTargetWord, solcAddressSlotWord, henv,
    Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWordAt, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat]

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
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          (fileAddressDataKey I) := by
    rw [henv, hAccounts]
    simp [Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord]
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
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (z, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' }, out) true) :
    ∃ (σ'_stele : AccountMap) (A'_stele : Substate),
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (z, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_stele, substate := A'_stele }, out) true
      ∧ EVMStateEquiv
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', substate := A' }
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_stele, substate := A'_stele } := by
  refine ⟨σ', A', ?_, ⟨rfl, rfl⟩⟩
  have hVatAddr := fileAddressVatAddressOf_initState_eq σ σ₀ A I g
  have hFlapperAddr := fileAddressFlapperAddressOf_initState_eq σ σ₀ A I g
  simpa [fileAddressVatAddress_eq_target σ I,
    fileAddressFlapperAddress_eq_target σ I, hVatAddr, hFlapperAddr,
    accountAddress_ofUInt256_eq_ofNat_toNat, eVM_address_id]
    using hcall

theorem vowFileAddressFlapperNopeCallDepthLimitBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hauthEvm : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := hauthEvm
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, solcSlotWordAt] using hauthEvm
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Stele =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Stele] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Stele, initState, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Stele) haddr hcodeSizeStele
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
  let ANope := (Ethereum.EVM.callSubstate fork evm0Stele.accountMap
    (EVM.address (fileAddressVatAddressOf evm0Stele)) evm0Stele.substate)
  have hcallNope :
      typedCallViaEVM fork config evm0Stele
        (EVM.address (fileAddressVatAddressOf evm0Stele)) "nope" 0
        [.address (fileAddressFlapperAddressOf evm0Stele)]
        (false, { evm0Stele with substate := ANope }, ByteArray.empty) true := by
    simpa [evm0Stele, ANope] using
      (callNotMade_depthLimit (cfg := config) (evm := evm0Stele)
        (tgt := EVM.address (fileAddressVatAddressOf evm0Stele)) (name := "nope")
        (args := [.address (fileAddressFlapperAddressOf evm0Stele)]) (callPerm := true)
        (fileAddressNopeEncode_initState_flapper σ σ₀ A I g hmemAuth)
        (by simpa [evm0Stele, initState] using hdepth))
  exact vowFileAddressFlapperNopeCallFailureBodyCore (sel := sel) hcode hwv hdispatch hdecode
    rd4300 hcallNope (by native_decide) (by simpa [callerSlot] using hauthStele) hwhat
    hvatCodeNope

theorem vowFileAddressFlapperHopeNoCodeAfterNopeSuccessBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σNope : AccountMap}
    {ANope : Substate} {outNope memNope : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (rd4300 : RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memNope (UInt256.ofNat 6) outNope σNope k C)
    (hmemNope : memNope.size = 164)
    (hread64Nope : memNope.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcallNopeEvm :
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope },
          outNope) true)
    (hauthEvm : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) = ⟨0⟩) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := hauthEvm
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Stele =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Stele] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Stele, initState, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Stele) haddr hcodeSizeStele
  obtain ⟨σNopeStele, ANopeStele, hcallNopeStele, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hcallNopeEvm
  let evmNopeStele :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeStele, substate := ANopeStele }
  have hcallNope :
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeStele, outNope) true := by
    simpa [evmNopeStele] using hcallNopeStele
  have hAccountsNope : Eq σNope evmNopeStele.accountMap := by
    simpa [evmNopeStele, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeStele.executionEnv = I := by
    simpa [evmNopeStele, initState] using hStateNope.executionEnv
  let evmSetStele := fileAddressSetFlapperEVM evmNopeStele I
  have hAccountsSet :
      Eq
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        evmSetStele.accountMap := by
    simpa [evmSetStele] using
      fileAddressSetFlapperAccountMap_equiv (I := I) hAccountsNope hEnvNope
  have hEnvSet : evmSetStele.executionEnv = I := by
    simpa [evmSetStele, fileAddressSetFlapperEVM, storageStore_executionEnv] using hEnvNope
  have hcodeSizeHopeStele :
      Reasoning.Theory.extCodeSizeWord evmSetStele.accountMap
        (fileAddressVatTargetWord evmSetStele.accountMap I) = ⟨0⟩ := by
    simpa [hAccountsSet] using hcodeSizeHope
  have hvatNoCodeHope :
      (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNopeStele I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNopeStele I))).option 0
            (fun acc => acc.code.size))).toNat = 0 := by
    have haddr :
        fileAddressVatAddressOf evmSetStele =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord evmSetStele.accountMap I) :=
      fileAddressVatAddressOf_eq_target_of_env evmSetStele I hEnvSet
    simpa [evmSetStele, State.lookupAccount] using
      extCodeSizeWord_zero_lookup_code_zero
        (σ := evmSetStele.accountMap)
        (target := fileAddressVatTargetWord evmSetStele.accountMap I)
        (addr := fileAddressVatAddressOf evmSetStele) haddr hcodeSizeHopeStele
  obtain ⟨_, _, rd4350⟩ := RD.vowFileAddressNopeSuccessStoreFlapperWithTarget rd4300 hperm
  exact vowFileAddressFlapperHopeNoCodeBodyCore (hperm := by assumption) (sel := sel) hcode hwv hdispatch hdecode
    rd4350 hmemNope hread64Nope hcodeSizeHope hcallNope
    (by simpa [callerSlot] using hauthStele) hwhat hvatCodeNope hvatNoCodeHope

theorem vowFileAddressFlapperHopeCallFailureAfterNopeSuccessBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σNope σHope : AccountMap} {ANope AHope : Substate}
    {outNope outHope memNope memHope rdataHope : ByteArray}
    {aw : UInt256} {k C kHope CHope : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (_rd4300 : RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memNope (UInt256.ofNat 6) outNope σNope k C)
    (hcallNopeEvm :
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope },
          outNope) true)
    (rd4423 : RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
        fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memHope aw rdataHope σHope kHope CHope)
    (hcallHopeEvm :
      typedCallViaEVM fork config
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
    (hauthEvm : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩)
    (hdepthLt : I.depth.val < 1024)
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := hauthEvm
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Stele =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Stele] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Stele, initState, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Stele) haddr hcodeSizeStele
  obtain ⟨σNopeStele, ANopeStele, hcallNopeStele, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hcallNopeEvm
  let evmNopeStele :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeStele, substate := ANopeStele }
  have hcallNope :
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeStele, outNope) true := by
    simpa [evmNopeStele] using hcallNopeStele
  have hAccountsNope : Eq σNope evmNopeStele.accountMap := by
    simpa [evmNopeStele, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeStele.executionEnv = I := by
    simpa [evmNopeStele, initState] using hStateNope.executionEnv
  let evmSetStele := fileAddressSetFlapperEVM evmNopeStele I
  have hAccountsSet :
      Eq
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        evmSetStele.accountMap := by
    simpa [evmSetStele] using
      fileAddressSetFlapperAccountMap_equiv (I := I) hAccountsNope hEnvNope
  have hEnvSet : evmSetStele.executionEnv = I := by
    simpa [evmSetStele, fileAddressSetFlapperEVM, storageStore_executionEnv] using hEnvNope
  have hTargetSet :
      fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I =
        fileAddressVatTargetWord evmSetStele.accountMap I :=
    congrArg (fun accounts => fileAddressVatTargetWord accounts I) hAccountsSet
  have hcodeSizeHopeStele :
      Reasoning.Theory.extCodeSizeWord evmSetStele.accountMap
        (fileAddressVatTargetWord evmSetStele.accountMap I) ≠ ⟨0⟩ := by
    simpa [hAccountsSet] using hcodeSizeHope
  have haddrHope :
      fileAddressVatAddressOf evmSetStele =
        AccountAddress.ofUInt256 (fileAddressVatTargetWord evmSetStele.accountMap I) :=
    fileAddressVatAddressOf_eq_target_of_env evmSetStele I hEnvSet
  have hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNopeStele I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNopeStele I))).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evmSetStele, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmSetStele.accountMap)
        (target := fileAddressVatTargetWord evmSetStele.accountMap I)
        (addr := fileAddressVatAddressOf evmSetStele) haddrHope hcodeSizeHopeStele
  let evmHopeEvmIn :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
  let evmSetSteleBase := { evmSetStele with substate := evmHopeEvmIn.substate }
  have hNopeMap : σNope = σNopeStele := by
    simpa [evmNopeStele] using hAccountsNope
  have hHopeInput : evmSetSteleBase = evmHopeEvmIn := by
    cases hFind : σNopeStele.get? I.codeOwner <;>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, evmSetSteleBase, evmHopeEvmIn, evmSetStele, evmNopeStele,
        fileAddressSetFlapperAccountMap,
        Stele.EVM.storageStore, Stele.EVM.storageLoad, State.setAccount,
        State.lookupAccount, Account.lookupStorage, Account.updateStorage,
        sstoreAccountMap, solcSlotWord, Option.option, hNopeMap, hFind, initState]
  have hcallHopeBase :
      typedCallViaEVM fork config evmSetSteleBase
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (false, { evmSetSteleBase with accountMap := σHope, substate := AHope }, outHope)
        true := by
    simpa [hHopeInput, evmHopeEvmIn] using hcallHopeEvm
  have hdepthNeBase : evmSetSteleBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hdepthEqI : I.depth = 1024 := by
      simpa [evmSetSteleBase, hEnvSet] using hdepthEq
    rw [hdepthEqI] at hdepthLt
    norm_num at hdepthLt
  obtain ⟨AHopeStele, hcallHopeRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallHopeBase hdepthNeBase
      evmSetStele.substate
  let evmHopeStele :=
    { evmSetStele with
      accountMap := σHope
      substate := AHopeStele }
  have hcallHope :
      typedCallViaEVM fork config evmSetStele
        (EVM.address (fileAddressVatAddressOf evmSetStele))
        "hope" 0 [.address (fileAddressData I)] (false, evmHopeStele, outHope) true := by
    simpa [evmHopeStele, evmSetSteleBase, hTargetSet, haddrHope,
      fileAddressVatAddress_eq_target
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I,
      fileAddressData_value_masked, fileAddressDataKey_clean, accountAddress_ofUInt256_eq_ofNat_toNat,
      eVM_address_id] using hcallHopeRaw
  exact vowFileAddressFlapperHopeCallFailureBodyCore (hperm := by assumption) (sel := sel) hcode hwv hdispatch hdecode
    rd4423 hcallNope hcallHope hrdataSize (by simpa [callerSlot] using hauthStele)
    hwhat hvatCodeNope hvatCodeHope

theorem vowFileAddressFlapperHopeSuccessAfterNopeSuccessBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σNope σHope : AccountMap} {ANope AHope : Substate}
    {outNope outHope memHope rdataHope : ByteArray}
    {aw : UInt256} {kHope CHope : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hcallNopeEvm :
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σNope, substate := ANope },
          outNope) true)
    (rd4423 : RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I ::
        fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      memHope aw rdataHope σHope kHope CHope)
    (hcallHopeEvm :
      typedCallViaEVM fork config
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
    (hauthEvm : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        (fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I) ≠ ⟨0⟩)
    (hdepthLt : I.depth.val < 1024)
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := hauthEvm
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Stele =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Stele] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Stele, initState, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Stele) haddr hcodeSizeStele
  obtain ⟨σNopeStele, ANopeStele, hcallNopeStele, hStateNope⟩ :=
    fileAddressNopeCall_initState_EVMStateEquiv hcallNopeEvm
  let evmNopeStele :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σNopeStele, substate := ANopeStele }
  have hcallNope :
      typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNopeStele, outNope) true := by
    simpa [evmNopeStele] using hcallNopeStele
  have hAccountsNope : Eq σNope evmNopeStele.accountMap := by
    simpa [evmNopeStele, initState] using hStateNope.accountMap
  have hEnvNope : evmNopeStele.executionEnv = I := by
    simpa [evmNopeStele, initState] using hStateNope.executionEnv
  let evmSetStele := fileAddressSetFlapperEVM evmNopeStele I
  have hAccountsSet :
      Eq
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I))
        evmSetStele.accountMap := by
    simpa [evmSetStele] using
      fileAddressSetFlapperAccountMap_equiv (I := I) hAccountsNope hEnvNope
  have hEnvSet : evmSetStele.executionEnv = I := by
    simpa [evmSetStele, fileAddressSetFlapperEVM, storageStore_executionEnv] using hEnvNope
  have hTargetSet :
      fileAddressVatTargetWord
          (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I =
        fileAddressVatTargetWord evmSetStele.accountMap I :=
    congrArg (fun accounts => fileAddressVatTargetWord accounts I) hAccountsSet
  have hcodeSizeHopeStele :
      Reasoning.Theory.extCodeSizeWord evmSetStele.accountMap
        (fileAddressVatTargetWord evmSetStele.accountMap I) ≠ ⟨0⟩ := by
    simpa [hAccountsSet] using hcodeSizeHope
  have haddrHope :
      fileAddressVatAddressOf evmSetStele =
        AccountAddress.ofUInt256 (fileAddressVatTargetWord evmSetStele.accountMap I) :=
    fileAddressVatAddressOf_eq_target_of_env evmSetStele I hEnvSet
  have hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNopeStele I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNopeStele I))).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evmSetStele, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmSetStele.accountMap)
        (target := fileAddressVatTargetWord evmSetStele.accountMap I)
        (addr := fileAddressVatAddressOf evmSetStele) haddrHope hcodeSizeHopeStele
  let evmHopeEvmIn :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I) }
  let evmSetSteleBase := { evmSetStele with substate := evmHopeEvmIn.substate }
  have hNopeMap : σNope = σNopeStele := by
    simpa [evmNopeStele] using hAccountsNope
  have hHopeInput : evmSetSteleBase = evmHopeEvmIn := by
    cases hFind : σNopeStele.get? I.codeOwner <;>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, evmSetSteleBase, evmHopeEvmIn, evmSetStele, evmNopeStele,
        fileAddressSetFlapperAccountMap,
        Stele.EVM.storageStore, Stele.EVM.storageLoad, State.setAccount,
        State.lookupAccount, Account.lookupStorage, Account.updateStorage,
        sstoreAccountMap, solcSlotWord, Option.option, hNopeMap, hFind, initState]
  have hcallHopeBase :
      typedCallViaEVM fork config evmSetSteleBase
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord
            (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (fileAddressDataKey I)).toNat)]
        (true, { evmSetSteleBase with accountMap := σHope, substate := AHope }, outHope)
        true := by
    simpa [hHopeInput, evmHopeEvmIn] using hcallHopeEvm
  have hdepthNeBase : evmSetSteleBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hdepthEqI : I.depth = 1024 := by
      simpa [evmSetSteleBase, hEnvSet] using hdepthEq
    rw [hdepthEqI] at hdepthLt
    norm_num at hdepthLt
  obtain ⟨AHopeStele, hcallHopeRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallHopeBase hdepthNeBase
      evmSetStele.substate
  let evmHopeStele :=
    { evmSetStele with
      accountMap := σHope
      substate := AHopeStele }
  have hcallHope :
      typedCallViaEVM fork config evmSetStele
        (EVM.address (fileAddressVatAddressOf evmSetStele))
        "hope" 0 [.address (fileAddressData I)] (true, evmHopeStele, outHope) true := by
    simpa [evmHopeStele, evmSetSteleBase, hTargetSet, haddrHope,
      fileAddressVatAddress_eq_target
        (fileAddressSetFlapperAccountMap σNope I (fileAddressDataKey I)) I,
      fileAddressData_value_masked, fileAddressDataKey_clean, accountAddress_ofUInt256_eq_ofNat_toNat,
      eVM_address_id] using hcallHopeRaw
  have hAccountsFinal : Eq σHope evmHopeStele.accountMap := rfl
  exact vowFileAddressFlapperHopeSuccessBodyCore (hperm := by assumption) (sel := sel) hcode hwv hdispatch hdecode
    rd4423 hcallNope hcallHope (by simpa [callerSlot] using hauthStele)
    hwhat hvatCodeNope hvatCodeHope hAccountsFinal

theorem vowFileAddressFlapperAuthorizedBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hauthEvm : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := hauthEvm
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, solcSlotWordAt] using hauthEvm
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
  · exact vowFileAddressFlapperNopeNoCodeBodyCore (sel := sel) hcode hwv hsz68
      hsize hdispatch hdecode hreach hauthEvm hwhat hcodeSizeNopeZero
  have hcodeSizeNope :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ :=
    hcodeSizeNopeZero
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (fileAddressVatTargetWord σ I) ≠ ⟨0⟩ := hcodeSizeNope
  let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat := by
    have haddr :
        fileAddressVatAddressOf evm0Stele =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
      simpa [evm0Stele] using fileAddressVatAddressOf_initState_eq σ σ₀ A I g
    simpa [evm0Stele, initState, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ) (target := fileAddressVatTargetWord σ I)
        (addr := fileAddressVatAddressOf evm0Stele) haddr hcodeSizeStele
  by_cases hdepthLt : I.depth.val < 1024
  · obtain ⟨σNope, zNope, outNope, ANope, k4300, C4300,
        rd4300, hcallNopeEvm, houtNopeSize⟩ :=
      RD.vowFileAddressNopePostCall hswitch hmatch hmemAuth hread64 hcodeSizeNope
        hdepthLt
    cases zNope
    · have rd4300False : RD fork vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
          (⟨0⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
            fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
            calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
          (UInt256.ofNat 6) outNope σNope k4300 C4300 := by
        simpa using rd4300
      have hcallNopeFalse :
          typedCallViaEVM fork config
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
            "nope" 0
            [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
            (false, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σNope, substate := ANope },
              outNope) true := by
        simpa using hcallNopeEvm
      obtain ⟨σNopeStele, ANopeStele, hcallNopeStele, _hStateNope⟩ :=
        fileAddressNopeCall_initState_EVMStateEquiv hcallNopeFalse
      let evmNopeStele :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σNopeStele, substate := ANopeStele }
      have hcallNope :
          typedCallViaEVM fork config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (fileAddressVatAddressOf
              (initState σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
            [.address (fileAddressFlapperAddressOf
              (initState σ σ₀ (Sat256.ofUInt256 g) A I))]
            (false, evmNopeStele, outNope) true := by
        simpa [evmNopeStele] using hcallNopeStele
      exact vowFileAddressFlapperNopeCallFailureBodyCore (sel := sel) hcode hwv
        hdispatch hdecode rd4300False hcallNope houtNopeSize
        (by simpa [callerSlot] using hauthStele) hwhat hvatCodeNope
    · have rd4300True : RD fork vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
          (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
            fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
            calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
          (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
          (UInt256.ofNat 6) outNope σNope k4300 C4300 := by
        simpa using rd4300
      have hcallNopeTrue :
          typedCallViaEVM fork config
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
      rcases RD.vowFileAddressNopeSuccessStoreFlapperWithTargetSplit rd4300True with
        ⟨hperm, -⟩ | ⟨hpf, hstatic⟩
      swap
      · obtain ⟨_, _, hcallNopeStele, -⟩ :=
          fileAddressNopeCall_initState_EVMStateEquiv hcallNopeTrue
        exact hstatic.reEquivStaticHalt hcode hdispatch hdecode
          ((fileAddressFlapperSourceStoreSplit (g := g) hwv hauthEvm hwhat hvatCodeNope
            hcallNopeStele).2 hpf)
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
      · have rd4423False : RD fork vowBytecode I (Sat256.ofUInt256 g)
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
            typedCallViaEVM fork config
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
        exact vowFileAddressFlapperHopeCallFailureAfterNopeSuccessBodyCore (hperm := by assumption) (sel := sel)
          hcode hwv hdispatch hdecode rd4300True hcallNopeTrue rd4423False
          hcallHopeFalse houtHopeSize hauthEvm hwhat hcodeSizeNope
          hcodeSizeHope hdepthLt
      · have rd4423True : RD fork vowBytecode I (Sat256.ofUInt256 g)
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
            typedCallViaEVM fork config
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
        exact vowFileAddressFlapperHopeSuccessAfterNopeSuccessBodyCore (hperm := by assumption) (sel := sel)
          hcode hwv hdispatch hdecode hcallNopeTrue rd4423True hcallHopeTrue
          hauthEvm hwhat hcodeSizeNope hcodeSizeHope hdepthLt
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    exact vowFileAddressFlapperNopeCallDepthLimitBodyCore (sel := sel) hcode hwv
      hsz68 hsize hdispatch hdecode hreach hauthEvm hwhat hcodeSizeNope
      hdepthEq

theorem vowFileAddressFlapperBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  by_cases hauthEvm : solcSlotWordAt callerSlot σ I = ⟨1⟩
  · exact vowFileAddressFlapperAuthorizedBodyCore (sel := sel) hcode hwv hsz68
      hsize hdispatch hdecode hreach (by simpa [callerSlot] using hauthEvm)
      hwhat
  · exact vowFileAddressAuthRevertBodyCore (sel := sel) hcode hwv hsz68 hsize hdispatch
      hdecode hreach (by simpa [callerSlot] using hauthEvm)

theorem vowFileAddressFlapperBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  exact vowFileAddressFlapperBodyCore (sel := vowSelWord I) hcode hwv hsz68 hsize
    (vowDispatch_fileAddress hsel)
    (by simpa [fileAddressLocals] using vowDecode_fileAddress_ok (I := I) hsz68)
    (vowReachFileAddressBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hwhat

theorem vowFileAddressBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 68
  · exact vowFileAddressShort hcode hsize hwv hsz4 hshort hsel
  have hsz68 : 68 ≤ I.calldata.size := by omega
  by_cases hwhat : fileAddressWhat I = fileAddressFlapperBytes
  · exact vowFileAddressFlapperBody hcode hsize hwv hsz68 hsel hwhat
  · exact vowFileAddressNonFlapperBody hcode hsize hwv hsz68 hsel hwhat

end Benchmarks.Dss.Vow

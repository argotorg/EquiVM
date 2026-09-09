import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `hope(address)` -/

abbrev hopeUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev hopeUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (hopeUsrWord I)

abbrev hopeSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev hopeUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (hopeUsrWord I).toNat)

abbrev hopeSourceKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev hopeUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (hopeUsrWord I).toNat)

abbrev hopeStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "usr" (hopeUsrValue I)

def hopeStorageSlot (I : ExecutionEnv) : UInt256 :=
  canSlot (hopeSourceKey I) (hopeUsrKey I)

def hopePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (hopeStorageSlot I) ⟨1⟩

abbrev hopeEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "can", steps := [.mindex (hopeSourceKey I), .mindex (hopeUsrKey I)] }

theorem hopeStore_get_usr (I : ExecutionEnv) :
    (hopeStore I).get? "usr" = some (hopeUsrValue I) := by
  unfold hopeStore
  simp

theorem hopeStore_can (I : ExecutionEnv) :
    (hopeStore I).get? "can" = none := by
  unfold hopeStore
  rw [store_get_ne _ _ (by decide +native)]
  simp

theorem hopeStore_index_usr (I : ExecutionEnv) :
    (hopeStore I)["usr"] = hopeUsrValue I := by
  unfold hopeStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem hopeSourceWord_toNat (I : ExecutionEnv) :
    (hopeSourceWord I).toNat = I.source.val := by
  unfold hopeSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem hopeStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    hopeStorageSlot I =
      mapSlot (hopeUsrMaskedWord I) (mapSlot (hopeSourceWord I) ⟨1⟩) := by
  unfold hopeStorageSlot canSlot canOwnerSlot hopeSourceKey hopeUsrKey hopeUsrMaskedWord
    hopeSourceWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem vatDecode_hope_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (hopeTransition.params.map Param.name)
      (transitionSignature hopeTransition).paramTypes I.calldata = some (hopeStore I) := by
  simpa [config, hopeTransition, hopeStore, hopeUsrValue, hopeUsrWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem vatDecode_hope_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (hopeTransition.params.map Param.name)
      (transitionSignature hopeTransition).paramTypes I.calldata = none := by
  simpa [config, hopeTransition] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

theorem evalStorageRef_hope_can (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := hopeStore I } evm
      (canRef sender (.var "usr")) = .ok (hopeEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, hopeEvaledRef, hsrc, hopeUsrValue, hopeSourceKey, hopeUsrKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem hopeAssign (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := hopeStore I } evm
      .storage (canRef sender (.var "usr")) (.int 1) =
        .ok ({ contract := contract, locals := hopeStore I }, hopePostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (hopeStorageSlot I))
      (hbase := hopeStore_can I)
      (her := evalStorageRef_hope_can evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
        hopeSourceKey, hopeUsrKey, uint256St])
      (hloc := by rfl)
  simpa [hopePostState] using vatStorageLocStore_uint256 evm (hopeStorageSlot I) ⟨1⟩

theorem vatHopeBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecTransitionBody config contract evm (hopeStore I) hopeTransition.body
      (.returned { contract := contract, locals := hopeStore I } (hopePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [hopeTransition, nonpayable] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (by simp [evalExpr?, pure]) (hopeAssign evm I hsrc)) <|
        ExecBlock.nil

theorem vatDispatchHope {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 15)) :
    dispatchMsg contract I.calldata = some hopeTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some hopeTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes]
  decide +native

theorem vatReachHopeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 15)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1207⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xa3b22fc4⟩ :=
    vatSelWord_eq_of_beq I hsz 0xa3 0xb2 0x2f 0xc4 ⟨0xa3b22fc4⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    decide +native
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms163Body 1 (by omega) ⟨1207⟩ hcode hwv hsz hsize
    hroot hhigh hhighlow heq0 htake (by jump_dest) (by decide +native)

noncomputable abbrev hopeInnerMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (hopeSourceWord I) ⟨1⟩ solcFreePtrMem

noncomputable abbrev hopeInnerSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (hopeSourceWord I) ⟨1⟩

noncomputable abbrev hopeHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (hopeUsrMaskedWord I) (hopeInnerSlot I) (hopeInnerMem I)

theorem hopeUsrMaskedWord_canonical (I : ExecutionEnv) :
    (hopeUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold hopeUsrMaskedWord
  rw [u256_land_comm solcAddrMask (hopeUsrWord I)]
  exact solcAddrMask_result_canonical (hopeUsrWord I)

theorem hopeStorageSlot_eq_innerSlot (I : ExecutionEnv) :
    hopeStorageSlot I = mapSlot (hopeUsrMaskedWord I) (hopeInnerSlot I) := by
  simpa [hopeInnerSlot] using hopeStorageSlot_eq_mapSlot_masked I

theorem hopeInnerMem_size (I : ExecutionEnv) :
    (hopeInnerMem I).size = 96 := by
  exact twoWordHashMem_size_96 (hopeSourceWord I) ⟨1⟩ solcFreePtrMem_size

set_option maxHeartbeats 1000000 in
theorem vatHopeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1207⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5540⟩
        [hopeUsrMaskedWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1207⟩) (ret := ⟨524⟩)
    (decoded := ⟨1229⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨1229⟩) (ret := ⟨524⟩) (routine := ⟨5540⟩)
    (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [hopeUsrMaskedWord, hopeUsrWord, calldataWord] using hroutine⟩

theorem vatHopeX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1207⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1207⟩) (ret := ⟨524⟩)
    (decoded := ⟨1229⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

set_option maxHeartbeats 1000000 in
theorem vatHopeX_storeOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD vatBytecode I g s0 ⟨5540⟩
      [hopeUsrMaskedWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret vatBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (hopeStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((hopeInnerMem I).readWithPadding 0 64))) =
        hopeInnerSlot I := by
    simpa [hopeInnerMem, hopeInnerSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (hopeSourceWord I)
        solcFreePtrMem_size
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((hopeHashMem I).readWithPadding 0 64))) =
        mapSlot (hopeUsrMaskedWord I) (hopeInnerSlot I) := by
    simpa [hopeHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (hopeInnerSlot I) (hopeUsrMaskedWord I)
        (hopeInnerMem_size I)
  have rd5546pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd5547 := rd5546pre.mstore 0 (wordAt0Mem (hopeSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd5553pre := evm_run rd5547 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd5554 := rd5553pre.mstore 0 (hopeInnerMem I) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd5558pre := evm_run rd5554 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov)]
  have rd5559 := rd5558pre.keccak256 0 (hopeInnerSlot I) (UInt256.ofNat 3)
    (by decide +native) mem_cost hinnerSlot (by decide +native) (by evm_ov)
  have rd5572pre := evm_run rd5559 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov)]
  have hmask :
      UInt256.land (hopeUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = hopeUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (hopeUsrMaskedWord_canonical I)
  have hmask' :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (hopeUsrMaskedWord I)
        = hopeUsrMaskedWord I := by
    rw [u256_land_comm]
    exact hmask
  rw [hmask'] at rd5572pre
  have rd5573 := rd5572pre.mstore 0 (wordAt0Mem (hopeUsrMaskedWord I) (hopeInnerMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd5575pre := evm_run rd5573 with [
    raw swap4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd5576 := rd5575pre.mstore 0 (hopeHashMem I) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd5578pre := evm_run rd5576 with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd5579 := rd5578pre.keccak256 0
    (mapSlot (hopeUsrMaskedWord I) (hopeInnerSlot I)) (UInt256.ofNat 3)
    (by decide +native) mem_cost houterSlot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5580raw⟩ := rd5579.sstore hperm (by decide +native) (by evm_ov)
  have rd524 := rd5580raw.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd525 := rd524.jumpdest (by decide +native) (by evm_ov)
  simpa [hopeStorageSlot_eq_innerSlot I] using RD.stop rd525 (by decide +native) (by evm_ov)

theorem vatHopeBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some hopeTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (hopeTransition.params.map Param.name)
        (transitionSignature hopeTransition).paramTypes I.calldata = some (hopeStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1207⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm (hopeStore I)
        hopeTransition.body
        (.returned { contract := contract, locals := hopeStore I }
          (hopePostState evmSolm I) none) := by
    simpa [evmSolm] using
      vatHopeBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
  obtain ⟨_, _, rd5540⟩ := vatHopeX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  exact (vatHopeX_storeOk (I := I) hperm rd5540)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [hopePostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [hopePostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (hopeStorageSlot I) ⟨1⟩ hAccounts)
      (by
        simpa [hopeTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by decide +native) (by decide +native)))

theorem vatHopeBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some hopeTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1207⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatHopeX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (vatDecode_hope_none_short hsz4 hshort)

theorem vatHopeBodyCore : VatBodyTheorem 15 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 15) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some hopeTransition :=
    vatDispatchHope hsel
  have hreach := vatReachHopeBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatHopeBodyCoreOk hcode hsize hperm hwv hsz36 hdispatch
      (vatDecode_hope_ok hsz36) hreach hAccounts
  · exact vatHopeBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Vat

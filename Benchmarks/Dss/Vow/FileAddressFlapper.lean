import Benchmarks.Dss.Vow.FileAddress

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `file(bytes32,address)` flapper branch continuation -/

abbrev fileAddressHopeSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨686590961⟩ ⟨226⟩

abbrev fileAddressHopeSelector : UInt256 :=
  ⟨2746363844⟩

noncomputable def fileAddressHopeSelectorMem (mem : ByteArray) : ByteArray :=
  fileAddressHopeSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def fileAddressHopeCalldataMem (arg : UInt256) (mem : ByteArray) : ByteArray :=
  arg.toByteArray.write 0 (fileAddressHopeSelectorMem mem) 132 32

theorem fileAddressHopeSelectorMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (fileAddressHopeSelectorMem mem).size = 164 := by
  unfold fileAddressHopeSelectorMem
  exact toByteArray_write32_size_of_le mem fileAddressHopeSelectorShifted 128 164 164 hmem
    (by rw [hmem]; omega) (by omega)

theorem fileAddressHopeCalldataMem_size (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (fileAddressHopeCalldataMem arg mem).size = 164 := by
  unfold fileAddressHopeCalldataMem
  exact toByteArray_write32_size_of_le (fileAddressHopeSelectorMem mem) arg 132 164 164
    (fileAddressHopeSelectorMem_size hmem)
    (by rw [fileAddressHopeSelectorMem_size hmem]; omega)
    (by omega)

theorem fileAddressHopeSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (fileAddressHopeSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold fileAddressHopeSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem fileAddressHopeCalldataMem_read64 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (fileAddressHopeCalldataMem arg mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold fileAddressHopeCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [fileAddressHopeSelectorMem_size hmem]; omega) (by omega)]
  exact fileAddressHopeSelectorMem_read64 hmem hread64

theorem fileAddressHopeSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 164) :
    (fileAddressHopeSelectorMem mem).extract 128 132 = vatHopeSelector := by
  unfold fileAddressHopeSelectorMem
  rw [write32_eq _ mem 128 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  have hAsz : (mem.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, hmem]
    omega
  have hBsz : (fileAddressHopeSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  rw [show
      (mem.extract 0 128 ++ fileAddressHopeSelectorShifted.toByteArray.extract 0 32 ++
          mem.extract (128 + 32) mem.size) =
        (mem.extract 0 128 ++
          (fileAddressHopeSelectorShifted.toByteArray.extract 0 32 ++
            mem.extract (128 + 32) mem.size)) by
    apply ByteArray.ext
    simp [ByteArray.data_append, Array.append_assoc]]
  rw [extract_append_right_window _ _ 128 132 (by rw [hAsz]), hAsz,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    extract_append_left _ _ 0 4 (by rw [hBsz]; omega), extract_extract_BA,
    show (0 : ℕ) + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega]
  native_decide

theorem fileAddressHopeCalldataMem_read128_36 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (fileAddressHopeCalldataMem arg mem).readWithPadding 128 36 =
      vatHopeSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [fileAddressHopeCalldataMem_size arg hmem]), fileAddressHopeCalldataMem,
    write32_eq _ (fileAddressHopeSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [fileAddressHopeSelectorMem_size hmem]; omega)]
  have hAsz : ((fileAddressHopeSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, fileAddressHopeSelectorMem_size hmem]
    omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((fileAddressHopeSelectorMem mem).extract 0 132 ++
        arg.toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), fileAddressHopeSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem fileAddressHopeEncode_eq (w : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    config.externalABI.encode? "hope"
        [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)] =
      some ((fileAddressHopeCalldataMem (UInt256.land w solcAddrMask) mem).readWithPadding
        fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat) := by
  rw [fileAddressCallInSize_eq]
  change config.externalABI.encode? "hope"
      [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)] =
    some ((fileAddressHopeCalldataMem (UInt256.land w solcAddrMask) mem).readWithPadding
      128 36)
  rw [fileAddressHopeCalldataMem_read128_36 _ hmem]
  have hcanon := solcAddrMask_result_canonical w
  have haddrVal : (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat).val =
      (UInt256.land w solcAddrMask).toNat := by
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword :
      EVM.word ↑(AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat) =
        UInt256.land w solcAddrMask := by
    change UInt256.ofNat (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat).val =
      UInt256.land w solcAddrMask
    rw [haddrVal]
    exact u256_ofNat_toNat _
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, vatHopeSelector, selectorBytes,
    hword, word_toBytesBE_toByteArray_eq_toByteArray]

abbrev fileAddressSetFlapperAccountMap
    (σ : AccountMap) (I : ExecutionEnv) (data : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨2⟩
    (setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) data)

theorem fileAddressVatTargetWord_sstore_flapper
    (σ : AccountMap) (I : ExecutionEnv) (val : UInt256) :
    fileAddressVatTargetWord (sstoreAccountMap I.codeOwner σ ⟨2⟩ val) I =
      fileAddressVatTargetWord σ I := by
  have hslot := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨2⟩ val
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨2⟩)
  simpa [fileAddressVatTargetWord, vowAddressReturnWord, vowSlotWord, solcSlotWord] using
    congrArg (fun word => UInt256.land word solcAddrMask) hslot

theorem fileAddressVatAddress_sstore_flapper
    (σ : AccountMap) (I : ExecutionEnv) (val : UInt256) :
    AccountAddress.ofNat
        (fileAddressVatTargetWord (sstoreAccountMap I.codeOwner σ ⟨2⟩ val) I).toNat =
      AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat := by
  rw [fileAddressVatTargetWord_sstore_flapper]

theorem fileAddressVatAddressOf_eq_ofUInt256 (evm : EVM.State) :
    fileAddressVatAddressOf evm =
      AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) := by
  apply Fin.ext
  simp [fileAddressVatAddressOf, accountAddress_ofUInt256_eq_ofNat_toNat]

theorem fileAddressFlapperAddressOf_eq_ofUInt256 (evm : EVM.State) :
    fileAddressFlapperAddressOf evm =
      AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask) := by
  apply Fin.ext
  simp [fileAddressFlapperAddressOf, accountAddress_ofUInt256_eq_ofNat_toNat]

theorem fileAddressVatAddressOf_initState_eq
    (cA gh bl σ σ₀ A I) (g : UInt256) :
    fileAddressVatAddressOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) =
      AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
  apply Fin.ext
  simp [fileAddressVatAddressOf, fileAddressVatTargetWord, vowAddressReturnWord,
    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    vowSlotWord, solcSlotWord,
    accountAddress_ofUInt256_eq_ofNat_toNat]

theorem fileAddressFlapperAddressOf_initState_eq
    (cA gh bl σ σ₀ A I) (g : UInt256) :
    fileAddressFlapperAddressOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) =
      AccountAddress.ofUInt256 (fileAddressFlapperTargetWord σ I) := by
  apply Fin.ext
  simp [fileAddressFlapperAddressOf, fileAddressFlapperTargetWord, vowAddressReturnWord,
    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    vowSlotWord, solcSlotWord,
    accountAddress_ofUInt256_eq_ofNat_toNat]

theorem fileAddress_extCodeSizeWord_ne_zero_lookup_code_pos
    {σ : AccountMap} {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

theorem fileAddress_extCodeSizeWord_zero_lookup_code_zero
    {σ : AccountMap} {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem fileAddress_typedCallViaEVM_zero_setSubstate
    {cfg : Config} {evm evm' : EVM.State} {tgt : EVM.Address} {name : Ident}
    {args : List Value} {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) perm)
    (hdepth : evm.executionEnv.depth ≠ 1024) (A0 : Substate) :
    ∃ A',
      typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
        (z,
          { { evm with substate := A0 } with
            accountMap := evm'.accountMap
            substate := A'
            createdAccounts := evm'.createdAccounts },
          out) perm := by
  obtain ⟨calldata, henc, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' hvalueLe _hdepth =>
      rename_i valueWord cA' σ' g' A'
      subst evm'
      rcases hTheta with ⟨callGas, A_in, hTheta⟩
      refine ⟨A', ⟨calldata, henc, ?_⟩⟩
      refine callViaEVM.callMade (valueWord := valueWord) (cA' := cA') (σ' := σ')
        (g' := g') (A' := A') (perm := perm) hvalue ⟨callGas, A_in, ?_⟩ ?_ ?_ ?_
      · simpa using hTheta
      · rfl
      · simpa using hvalueLe
      · simpa using hdepth
  | callNotMade _hsubstate _hevm' hfail =>
      exfalso
      exact hfail ⟨(by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _), hdepth⟩

theorem fileAddress_storageStore_σ₀
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem fileAddress_storageStore_genesisBlockHeader
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem fileAddress_storageStore_blocks
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem evalExpr_fileAddressVatCodeGuard_false {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem fileAddressFlapperSourceNopeNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat = 0) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flapperParamLit) = .ok (.bool true) := by
    simpa [flapperParamLit, fileAddressFlapperBytes] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlapperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hvatNope :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evm0)) := by
    simpa [locals] using
      evalExpr_fileAddressVatStorage evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hguardNope :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_fileAddressVatCodeGuard_false hvatNope (by simpa [evm0] using hvatNoCode)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
            [.storage flapperRef] "_nopeRet" ++
          [ .assign .storage flapperRef (.var "data") ] ++
          checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
            [.var "data"] "_hopeRet")
        .reverted := by
    simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNope)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hflapper hthen)
  simpa [ExecTransitionBody, evm0, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockRevert hblock

theorem fileAddressFlapperSourceNopeCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmNope : EVM.State} {outNope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))]
        (false, evmNope, outNope) true) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flapperParamLit) = .ok (.bool true) := by
    simpa [flapperParamLit, fileAddressFlapperBytes] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlapperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hvatNope :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evm0)) := by
    simpa [locals] using
      evalExpr_fileAddressVatStorage evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hguardNope :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileAddressVatCodeGuard_true hvatNope (by simpa [evm0] using hvatCodeNope)
  have hargsNope :
      evalExprs? config { contract := contract, locals := locals } evm0 [.storage flapperRef] =
        .ok [.address (fileAddressFlapperAddressOf evm0)] := by
    simpa [locals] using
      evalExprs_fileAddressNopeArgs evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hcallNopeStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "nope" (.intLit 0) [.storage flapperRef] "_nopeRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hvatNope (by simp [evalExpr?, pure]) hargsNope
      hcallNope
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
            [.storage flapperRef] "_nopeRet" ++
          [ .assign .storage flapperRef (.var "data") ] ++
          checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
            [.var "data"] "_hopeRet")
        .reverted := by
    simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNope) ?_
    exact ExecBlock.consRevert hcallNopeStmt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hflapper hthen)
  simpa [ExecTransitionBody, evm0, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockRevert hblock

theorem fileAddressFlapperSourceHopeNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmNope : EVM.State} {outNope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNope, outNope) true)
    (hvatNoCodeHope :
      (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNope I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I))).option 0
            (fun acc => acc.code.size))).toNat = 0) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  let localsNope := fileAddressLocalsNope I
  let evmSet := fileAddressSetFlapperEVM evmNope I
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flapperParamLit) = .ok (.bool true) := by
    simpa [flapperParamLit, fileAddressFlapperBytes] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlapperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hvatNope :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evm0)) := by
    simpa [locals] using
      evalExpr_fileAddressVatStorage evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hguardNope :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileAddressVatCodeGuard_true hvatNope (by simpa [evm0] using hvatCodeNope)
  have hargsNope :
      evalExprs? config { contract := contract, locals := locals } evm0 [.storage flapperRef] =
        .ok [.address (fileAddressFlapperAddressOf evm0)] := by
    simpa [locals] using
      evalExprs_fileAddressNopeArgs evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hcallNopeStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "nope" (.intLit 0) [.storage flapperRef] "_nopeRet")
        (.ok { contract := contract, locals := localsNope } evmNope) := by
    simpa [locals, localsNope, fileAddressLocalsNope, collapseReturns, config, vowExternalABI,
      decodeVoid?] using
        ExecStmt.externalCallSuccess hvatNope (by simp [evalExpr?, pure]) hargsNope
          hcallNope (vowExternalABI_decode_nope outNope)
  have hdataNope :
      evalExpr? config { contract := contract, locals := localsNope } evmNope (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [localsNope, fileAddressLocalsNope] using
      (evalExpr_fileAddressData (evm := evmNope) (I := I) (locals := localsNope)
        (by simpa [localsNope] using fileAddressLocalsNope_get_data I))
  have hassign :
      assignStorageRef? config { contract := contract, locals := localsNope } evmNope
        .storage flapperRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := localsNope }, evmSet) := by
    simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord, evmSet,
      fileAddressSetFlapperEVM] using
      (assign_fileAddressFlapperStorage evmNope (locals := localsNope)
        (calldataWord I.calldata 36)
        (by simp [localsNope]))
  have hvatHope :
      evalExpr? config { contract := contract, locals := localsNope } evmSet (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evmSet)) := by
    simpa [localsNope] using
      evalExpr_fileAddressVatStorage evmSet (locals := localsNope)
        (by simp [localsNope])
  have hguardHope :
      evalExpr? config { contract := contract, locals := localsNope } evmSet
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_fileAddressVatCodeGuard_false hvatHope (by simpa [evmSet] using hvatNoCodeHope)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
            [.storage flapperRef] "_nopeRet" ++
          [ .assign .storage flapperRef (.var "data") ] ++
          checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
            [.var "data"] "_hopeRet")
        .reverted := by
    simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNope) ?_
    refine ExecBlock.consNormal hcallNopeStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hdataNope hassign) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardHope)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hflapper hthen)
  simpa [ExecTransitionBody, evm0, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockRevert hblock

theorem fileAddressFlapperSourceHopeCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmNope evmHope : EVM.State}
    {outNope outHope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNope, outNope) true)
    (hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNope I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallHope :
      typedCallViaEVM config (fileAddressSetFlapperEVM evmNope I)
        (EVM.address (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I)))
        "hope" 0 [.address (fileAddressData I)] (false, evmHope, outHope) true) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  let localsNope := fileAddressLocalsNope I
  let evmSet := fileAddressSetFlapperEVM evmNope I
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flapperParamLit) = .ok (.bool true) := by
    simpa [flapperParamLit, fileAddressFlapperBytes] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlapperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hvatNope :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evm0)) := by
    simpa [locals] using
      evalExpr_fileAddressVatStorage evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hguardNope :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileAddressVatCodeGuard_true hvatNope (by simpa [evm0] using hvatCodeNope)
  have hargsNope :
      evalExprs? config { contract := contract, locals := locals } evm0 [.storage flapperRef] =
        .ok [.address (fileAddressFlapperAddressOf evm0)] := by
    simpa [locals] using
      evalExprs_fileAddressNopeArgs evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hcallNopeStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "nope" (.intLit 0) [.storage flapperRef] "_nopeRet")
        (.ok { contract := contract, locals := localsNope } evmNope) := by
    simpa [locals, localsNope, fileAddressLocalsNope, collapseReturns, config, vowExternalABI,
      decodeVoid?] using
        ExecStmt.externalCallSuccess hvatNope (by simp [evalExpr?, pure]) hargsNope
          hcallNope (vowExternalABI_decode_nope outNope)
  have hdataNope :
      evalExpr? config { contract := contract, locals := localsNope } evmNope (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [localsNope, fileAddressLocalsNope] using
      (evalExpr_fileAddressData (evm := evmNope) (I := I) (locals := localsNope)
        (by simpa [localsNope] using fileAddressLocalsNope_get_data I))
  have hassign :
      assignStorageRef? config { contract := contract, locals := localsNope } evmNope
        .storage flapperRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := localsNope }, evmSet) := by
    simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord, evmSet,
      fileAddressSetFlapperEVM] using
      (assign_fileAddressFlapperStorage evmNope (locals := localsNope)
        (calldataWord I.calldata 36)
        (by simp [localsNope]))
  have hvatHope :
      evalExpr? config { contract := contract, locals := localsNope } evmSet (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evmSet)) := by
    simpa [localsNope] using
      evalExpr_fileAddressVatStorage evmSet (locals := localsNope)
        (by simp [localsNope])
  have hguardHope :
      evalExpr? config { contract := contract, locals := localsNope } evmSet
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileAddressVatCodeGuard_true hvatHope (by simpa [evmSet] using hvatCodeHope)
  have hargsHope :
      evalExprs? config { contract := contract, locals := localsNope } evmSet [.var "data"] =
        .ok [.address (fileAddressData I)] := by
    simpa [localsNope, fileAddressLocalsNope] using
      evalExprs_fileAddressHopeArgs (evm := evmSet) (I := I) (locals := localsNope)
        (by simpa [localsNope] using fileAddressLocalsNope_get_data I)
  have hcallHopeStmt :
      ExecStmt config { contract := contract, locals := localsNope } evmSet
        (.externalCall (.storage vatRef) "hope" (.intLit 0) [.var "data"] "_hopeRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hvatHope (by simp [evalExpr?, pure]) hargsHope
      hcallHope
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
            [.storage flapperRef] "_nopeRet" ++
          [ .assign .storage flapperRef (.var "data") ] ++
          checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
            [.var "data"] "_hopeRet")
        .reverted := by
    simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNope) ?_
    refine ExecBlock.consNormal hcallNopeStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hdataNope hassign) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardHope) ?_
    exact ExecBlock.consRevert hcallHopeStmt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hflapper hthen)
  simpa [ExecTransitionBody, evm0, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockRevert hblock

theorem RD.vowFileAddressNopeCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4197⟩
      (fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: []) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressFlapperBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I) mem)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasWord, _, _, rd4299⟩ :=
    RD.vowFileAddressFlapperToNopeCall rd hmatch hmem hread64 hcodeSize
  obtain ⟨k4300, C4300, rd4300raw⟩ := RD.callDepthLimit
    (by simpa [fileAddressCallOutSize] using rd4299)
    (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat)
        fileAddressCallOutPtr.toNat fileAddressCallOutSize.toNat) = UInt256.ofNat 6 := by
    rw [fileAddressCallInSize_eq]
    unfold fileAddressCallOutPtr fileAddressCallOutSize
    native_decide
  have hmin : (min fileAddressCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold fileAddressCallOutSize
    rfl
  have rd4300 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      (ByteArray.empty.write 0 (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I) mem)
        fileAddressCallOutPtr.toNat
        (min fileAddressCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k4300 C4300 :=
    haw ▸ rd4300raw
  rw [hmin, byteArray_write_len_zero] at rd4300
  exact ⟨k4300, C4300, rd4300⟩

theorem RD.vowFileAddressNopeNoCode
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4197⟩ (data :: what :: ret :: sel :: []) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileAddressFlapperBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ ee) = ⟨0⟩) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd4284⟩ :=
    RD.vowFileAddressFlapperToNopeExtcodesizeGuard rd hmatch hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4284⟩) (okPc := ⟨4296⟩) rd4284
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFileAddressNopeSuccessStoreFlapperWithTarget
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {target data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hperm : ee.perm = true) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata
      (cA, fileAddressSetFlapperAccountMap σ ee data) k' C' := by
  obtain ⟨k4318, C4318, rd4318⟩ := RD.solcCallSuccessGuardOk
    (pc := ⟨4300⟩) (okPc := ⟨4316⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) (by simp)
  have rd4318' : RD vowBytecode ee g s0 ⟨4318⟩
      (fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k4318 C4318 := by
    simpa [show ((⟨4316⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨4318⟩ from by native_decide]
      using rd4318
  have rd4319 := rd4318'.pop (by native_decide) (by evm_ov)
  have rd4321 := rd4319.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd4322 := rd4321.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4323⟩ := rd4322.sload (by native_decide) (by evm_ov)
  have rd4325 := rd4323.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4327 := rd4325.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4329 := rd4327.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4330 := rd4329.shl (by native_decide) (by evm_ov)
  have rd4331 := rd4330.sub (by native_decide) (by evm_ov)
  have rd4332 := rd4331.not (by native_decide) (by evm_ov)
  have rd4333 := rd4332.and (by native_decide) (by evm_ov)
  have rd4335 := rd4333.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4337 := rd4335.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4339 := rd4337.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4340 := rd4339.shl (by native_decide) (by evm_ov)
  have rd4341 := rd4340.sub (by native_decide) (by evm_ov)
  have rd4342 := rd4341.dup6 (by native_decide) (by evm_ov)
  have rd4343 := rd4342.dup2 (by native_decide) (by evm_ov)
  have rd4344 := rd4343.and (by native_decide) (by evm_ov)
  have rd4345 := rd4344.swap2 (by native_decide) (by evm_ov)
  have rd4346 := rd4345.dup3 (by native_decide) (by evm_ov)
  have rd4347 := rd4346.lor (by native_decide) (by evm_ov)
  have rd4348 := rd4347.swap1 (by native_decide) (by evm_ov)
  have rd4349 := rd4348.swap3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4350⟩ := rd4349.sstore hperm (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land solcAddrMask data)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)) =
        setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data := by
    calc
      UInt256.lor (UInt256.land solcAddrMask data)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)) =
          UInt256.lor (UInt256.land data solcAddrMask)
            (UInt256.land (solcSlotWord σ ee ⟨2⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm solcAddrMask data,
              u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ ee ⟨2⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land data solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data := by
            rfl
  have hpc4350 :
      (⟨4318⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ = ⟨4350⟩ := by
    native_decide
  rw [hpc4350] at rd4350
  exact ⟨_, _, by
    simpa [fileAddressSetFlapperAccountMap, solcSlotWord, hword,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
      using rd4350⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowFileAddressFlapperToHopeExtcodesizeGuard
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨4407⟩
      (fileAddressVatTargetWord σ ee :: fileAddressVatTargetWord σ ee ::
        fileAddressCallOutSize :: fileAddressCallOutPtr :: fileAddressCallInSize ::
        fileAddressCallOutPtr :: fileAddressCallOutSize :: fileAddressCallEndPtr ::
        fileAddressHopeSelector :: fileAddressVatTargetWord σ ee ::
        data :: what :: ret :: sel :: [])
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  have rd4352 := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4353, C4353, rd4353₀⟩ := rd4352.sload (by native_decide) (by evm_ov)
  have rd4353 : RD vowBytecode ee g s0 ⟨4353⟩
      (vowSlotWord ⟨1⟩ σ ee :: UInt256.land solcAddrMask data :: solcAddrMask ::
        ⟨3696042234⟩ :: fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k4353 C4353 := by
    simpa [fileAddressVatTargetWord, vowSlotWord, solcSlotWord] using rd4353₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hHopeMem :
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).size = 164 :=
    fileAddressHopeCalldataMem_size _ hmem
  have hHopeRead64 :
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    fileAddressHopeCalldataMem_read64 _ hmem hread64
  have hmload64Hope :
      (if (⟨64⟩ : UInt256).toNat ≥
            (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hHopeMem]; decide) (by decide) hHopeRead64
  have rd4407 := evm_run rd4353 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨686590961⟩,
    push1 ⟨226⟩,
    shl,
    dup2,
    raw mstore 0 (fileAddressHopeSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    swap4,
    swap1,
    swap4,
    raw mstore 0 (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Hope (by decide) (by evm_ov),
    swap3,
    and,
    swap4,
    pop,
    push4 fileAddressHopeSelector,
    swap3,
    pop,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 fileAddressCallOutSize,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  have hpc4407 :
      (⟨4353⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨4407⟩ := by
    native_decide
  rw [hpc4407] at rd4407
  exact ⟨_, _, by
    simpa [fileAddressVatTargetWord, fileAddressHopeSelectorShifted, fileAddressHopeSelector,
      fileAddressHopeSelectorMem, fileAddressHopeCalldataMem, fileAddressCallOutPtr,
      fileAddressCallOutSize, fileAddressCallInSize, fileAddressCallEndPtr,
      vowSlotWord, solcSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd4407⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowFileAddressFlapperToHopeExtcodesizeGuardWithTarget
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {target data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨4407⟩
      (fileAddressVatTargetWord σ ee :: fileAddressVatTargetWord σ ee ::
        fileAddressCallOutSize :: fileAddressCallOutPtr :: fileAddressCallInSize ::
        fileAddressCallOutPtr :: fileAddressCallOutSize :: fileAddressCallEndPtr ::
        fileAddressHopeSelector :: fileAddressVatTargetWord σ ee ::
        data :: what :: ret :: sel :: [])
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  have rd4352 := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4353, C4353, rd4353₀⟩ := rd4352.sload (by native_decide) (by evm_ov)
  have rd4353 : RD vowBytecode ee g s0 ⟨4353⟩
      (vowSlotWord ⟨1⟩ σ ee :: UInt256.land solcAddrMask data :: solcAddrMask ::
        ⟨3696042234⟩ :: target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k4353 C4353 := by
    simpa [fileAddressVatTargetWord, vowSlotWord, solcSlotWord] using rd4353₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hHopeMem :
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).size = 164 :=
    fileAddressHopeCalldataMem_size _ hmem
  have hHopeRead64 :
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    fileAddressHopeCalldataMem_read64 _ hmem hread64
  have hmload64Hope :
      (if (⟨64⟩ : UInt256).toNat ≥
            (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hHopeMem]; decide) (by decide) hHopeRead64
  have rd4407 := evm_run rd4353 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨686590961⟩,
    push1 ⟨226⟩,
    shl,
    dup2,
    raw mstore 0 (fileAddressHopeSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    swap4,
    swap1,
    swap4,
    raw mstore 0 (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Hope (by decide) (by evm_ov),
    swap3,
    and,
    swap4,
    pop,
    push4 fileAddressHopeSelector,
    swap3,
    pop,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 fileAddressCallOutSize,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  have hpc4407 :
      (⟨4353⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨4407⟩ := by
    native_decide
  rw [hpc4407] at rd4407
  exact ⟨_, _, by
    simpa [fileAddressVatTargetWord, fileAddressHopeSelectorShifted, fileAddressHopeSelector,
      fileAddressHopeSelectorMem, fileAddressHopeCalldataMem, fileAddressCallOutPtr,
      fileAddressCallOutSize, fileAddressCallInSize, fileAddressCallEndPtr,
      vowSlotWord, solcSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd4407⟩

theorem RD.vowFileAddressFlapperToHopeCall
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ ee) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨4422⟩
      (gasWord :: fileAddressVatTargetWord σ ee :: fileAddressCallOutSize ::
        fileAddressCallOutPtr :: fileAddressCallInSize :: fileAddressCallOutPtr ::
        fileAddressCallOutSize :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4407⟩ :=
    RD.vowFileAddressFlapperToHopeExtcodesizeGuard rd hmem hread64
  obtain ⟨gasWord, k', C', rd4422⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4407⟩) (okPc := ⟨4419⟩) rd4407
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd4422⟩

theorem RD.vowFileAddressFlapperToHopeCallWithTarget
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {target data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ ee) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨4422⟩
      (gasWord :: fileAddressVatTargetWord σ ee :: fileAddressCallOutSize ::
        fileAddressCallOutPtr :: fileAddressCallInSize :: fileAddressCallOutPtr ::
        fileAddressCallOutSize :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4407⟩ :=
    RD.vowFileAddressFlapperToHopeExtcodesizeGuardWithTarget rd hmem hread64
  obtain ⟨gasWord, k', C', rd4422⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4407⟩) (okPc := ⟨4419⟩) rd4407
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd4422⟩

theorem RD.vowFileAddressHopeNoCode
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ ee) = ⟨0⟩) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd4407⟩ :=
    RD.vowFileAddressFlapperToHopeExtcodesizeGuard rd hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4407⟩) (okPc := ⟨4419⟩) rd4407
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFileAddressHopeNoCodeWithTarget
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {target data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ ee) = ⟨0⟩) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd4407⟩ :=
    RD.vowFileAddressFlapperToHopeExtcodesizeGuardWithTarget rd hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4407⟩) (okPc := ⟨4419⟩) rd4407
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFileAddressHopePostCall
    {cA gh bl σ σ₀ A I} {g sel data what ret : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ' I :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (fileAddressVatTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (out : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
          fileAddressVatTargetWord σ' I :: data :: what :: ret :: sel :: [])
        (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
        (UInt256.ofNat 6) out (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ' I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4422⟩ :=
    RD.vowFileAddressFlapperToHopeCall rd hmem hread64 hcodeSize
  obtain ⟨cA'', σ'', z, out, A_in, callGas, k4423, C4423, hΘpack, rd4423raw, houtsz⟩ :=
    RD.call rd4422 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A'', hΘ⟩ := hΘpack
  refine ⟨cA'', σ'', z, out, A'', k4423, C4423, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat)
          fileAddressCallOutPtr.toNat fileAddressCallOutSize.toNat) = UInt256.ofNat 6 := by
      rw [fileAddressCallInSize_eq]
      unfold fileAddressCallOutPtr fileAddressCallOutSize
      native_decide
    have hmin : (min fileAddressCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold fileAddressCallOutSize
      rfl
    have rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
          fileAddressVatTargetWord σ' I :: data :: what :: ret :: sel :: [])
        (out.write 0 (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
          fileAddressCallOutPtr.toNat
          (min fileAddressCallOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA'', σ'') k4423 C4423 :=
      haw ▸ rd4423raw
    rw [hmin, byteArray_write_len_zero] at rd4423
    exact rd4423
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := fileAddressVatTargetWord σ' I)
      (mem := fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (inOff := fileAddressCallOutPtr) (inSize := fileAddressCallInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (fileAddressVatAddress_eq_target σ' I) ?_ ?_
    · simpa [u256_land_comm] using fileAddressHopeEncode_eq data hmem
    · simpa [initState, hperm] using hΘ

theorem RD.vowFileAddressHopePostCallWithTarget
    {cA gh bl σ σ₀ A I} {g sel target data what ret : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (fileAddressVatTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (out : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
          fileAddressVatTargetWord σ' I :: data :: what :: ret :: sel :: [])
        (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
        (UInt256.ofNat 6) out (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ' I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4422⟩ :=
    RD.vowFileAddressFlapperToHopeCallWithTarget rd hmem hread64 hcodeSize
  obtain ⟨cA'', σ'', z, out, A_in, callGas, k4423, C4423, hΘpack, rd4423raw, houtsz⟩ :=
    RD.call rd4422 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A'', hΘ⟩ := hΘpack
  refine ⟨cA'', σ'', z, out, A'', k4423, C4423, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat)
          fileAddressCallOutPtr.toNat fileAddressCallOutSize.toNat) = UInt256.ofNat 6 := by
      rw [fileAddressCallInSize_eq]
      unfold fileAddressCallOutPtr fileAddressCallOutSize
      native_decide
    have hmin : (min fileAddressCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold fileAddressCallOutSize
      rfl
    have rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
          fileAddressVatTargetWord σ' I :: data :: what :: ret :: sel :: [])
        (out.write 0 (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
          fileAddressCallOutPtr.toNat
          (min fileAddressCallOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA'', σ'') k4423 C4423 :=
      haw ▸ rd4423raw
    rw [hmin, byteArray_write_len_zero] at rd4423
    exact rd4423
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := fileAddressVatTargetWord σ' I)
      (mem := fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (inOff := fileAddressCallOutPtr) (inSize := fileAddressCallInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (fileAddressVatAddress_eq_target σ' I) ?_ ?_
    · simpa [u256_land_comm] using fileAddressHopeEncode_eq data hmem
    · simpa [initState, hperm] using hΘ

theorem RD.vowFileAddressHopeCallDepthLimitWithTarget
    {cA gh bl σ σ₀ A I} {g sel target data what ret : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (fileAddressVatTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord σ' I :: data :: what :: ret :: sel :: [])
      (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
      (UInt256.ofNat 6) ByteArray.empty (cA', σ') k' C' := by
  obtain ⟨gasWord, _, _, rd4422⟩ :=
    RD.vowFileAddressFlapperToHopeCallWithTarget rd hmem hread64 hcodeSize
  obtain ⟨k4423, C4423, rd4423raw⟩ := RD.callDepthLimit
    (by simpa [fileAddressCallOutSize] using rd4422)
    (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat)
        fileAddressCallOutPtr.toNat fileAddressCallOutSize.toNat) = UInt256.ofNat 6 := by
    rw [fileAddressCallInSize_eq]
    unfold fileAddressCallOutPtr fileAddressCallOutSize
    native_decide
  have hmin : (min fileAddressCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold fileAddressCallOutSize
    rfl
  have rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        fileAddressVatTargetWord σ' I :: data :: what :: ret :: sel :: [])
      (ByteArray.empty.write 0 (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
        fileAddressCallOutPtr.toNat
        (min fileAddressCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA', σ') k4423 C4423 :=
    haw ▸ rd4423raw
  rw [hmin, byteArray_write_len_zero] at rd4423
  exact ⟨k4423, C4423, rd4423⟩

theorem RD.vowFileAddressNopeSuccessToHopePostCall
    {cA gh bl σ σ₀ A I} {g sel target data what ret : UInt256}
    {cANope : Batteries.RBSet AccountAddress compare} {σNope : AccountMap}
    {mem outNope : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) outNope (cANope, σNope) k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord
        (fileAddressSetFlapperAccountMap σNope I data)
        (fileAddressVatTargetWord (fileAddressSetFlapperAccountMap σNope I data) I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cAHope : Batteries.RBSet AccountAddress compare) (σHope : AccountMap) (z : Bool)
      (outHope : ByteArray) (AHope : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
          fileAddressVatTargetWord (fileAddressSetFlapperAccountMap σNope I data) I ::
          data :: what :: ret :: sel :: [])
        (fileAddressHopeCalldataMem (UInt256.land solcAddrMask data) mem)
        (UInt256.ofNat 6) outHope (cAHope, σHope) k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := fileAddressSetFlapperAccountMap σNope I data
          createdAccounts := cANope }
        (EVM.address (AccountAddress.ofNat
          (fileAddressVatTargetWord (fileAddressSetFlapperAccountMap σNope I data) I).toNat))
        "hope" 0 [.address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σHope, substate := AHope, createdAccounts := cAHope }, outHope) true
    ∧ outHope.size < UInt256.size := by
  obtain ⟨_, _, rd4350⟩ :=
    RD.vowFileAddressNopeSuccessStoreFlapperWithTarget rd hperm
  exact RD.vowFileAddressHopePostCallWithTarget
    (σ' := fileAddressSetFlapperAccountMap σNope I data) rd4350
    hmem hread64 hcodeSizeHope hdepth hperm

theorem RD.vowFileAddressHopeCallFailure
    {cA gh bl σ σ₀ A I} {g sel target data what ret : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        target :: data :: what :: ret :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4423⟩) (okPc := ⟨4439⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.vowFileAddressHopeCallSuccessToReturn
    {cA gh bl σ σ₀ A I} {g sel target data what ret : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        target :: data :: what :: ret :: sel :: [])
      mem aw rdata acc k C)
    (hret : (D_J vowBytecode 0).contains ret = true) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ret
      [sel] mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd4441⟩ := RD.solcCallSuccessGuardOk
    (pc := ⟨4423⟩) (okPc := ⟨4439⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) (by simp)
  have rd4442 := rd4441.pop (by native_decide) (by evm_ov)
  have rd4443 := rd4442.pop (by native_decide) (by evm_ov)
  have rd4444 := rd4443.pop (by native_decide) (by evm_ov)
  have rd4447 := rd4444.push2 ⟨2233⟩ (by native_decide) (by evm_ov)
  have rd2233 := rd4447.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2234 := rd2233.jumpdest (by native_decide) (by evm_ov)
  have rd2235 := rd2234.pop (by native_decide) (by evm_ov)
  have rd2236 := rd2235.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2236.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.vowFileAddressHopeCallSuccess
    {cA gh bl σ σ₀ A I} {g sel target data what : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        target :: data :: what :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty := by
  obtain ⟨_, _, rd412⟩ := RD.vowFileAddressHopeCallSuccessToReturn rd (by jump_dest)
  have rd413 := rd412.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd413 (by native_decide) (by simp)

theorem vowFileAddressFlapperNopeNoCodeBodyCore
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
        (fileAddressVatTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hVatWord : vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  have hVatTarget :
      fileAddressVatTargetWord σ_evm I = fileAddressVatTargetWord σ_solm I := by
    simp [fileAddressVatTargetWord, vowAddressReturnWord, hVatWord]
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (fileAddressVatTargetWord σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (fileAddressVatTargetWord σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (fileAddressVatTargetWord σ_evm I) = ⟨0⟩ := by
      rw [← hsame]
      exact hcodeSizeNope
    simpa [hVatTarget] using hzeroAtEvmTarget
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hvatNoCodeSolm :
      (UInt256.ofNat
        ((evm0.lookupAccount (fileAddressVatAddressOf evm0)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    have haddr :
        fileAddressVatAddressOf evm0 =
          AccountAddress.ofUInt256 (fileAddressVatTargetWord σ_solm I) := by
      simpa [evm0] using fileAddressVatAddressOf_initState_eq cA gh bl σ_solm σ₀ A I g
    have hlookup :=
      fileAddress_extCodeSizeWord_zero_lookup_code_zero
        (σ := σ_solm) (target := fileAddressVatTargetWord σ_solm I)
        (addr := fileAddressVatAddressOf evm0) haddr hcodeSizeSolm
    simpa [evm0, initState, State.lookupAccount] using hlookup
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    simpa [evm0, locals] using
      (fileAddressFlapperSourceNopeNoCode (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hauthSolm hwhat hvatNoCodeSolm)
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
  have hrev := RD.vowFileAddressNopeNoCode
    (data := fileAddressDataKey I) (what := calldataWord I.calldata 4)
    (ret := ⟨412⟩) (sel := sel) hswitch hmatch hmemAuth hread64 hcodeSizeNope
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFileAddressFlapperNopeCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {evmNope : EVM.State} {outNope mem rdata : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (rd4300 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ_evm I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (false, evmNope, outNope) true)
    (hrdataSize : rdata.size < UInt256.size)
    (hauthSolm : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    simpa [evm0, locals] using
      (fileAddressFlapperSourceNopeCallFailure (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmNope := evmNope) (outNope := outNope)
        hwv hauthSolm hwhat hvatCodeNope hcallNope)
  have hrev := RD.vowFileAddressNopeCallFailure rd4300 hrdataSize
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFileAddressFlapperHopeNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel target data what ret : UInt256}
    {cANope : Batteries.RBSet AccountAddress compare} {σSet : AccountMap}
    {evmNope : EVM.State} {outNope mem rdata : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (rd4350 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        target :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cANope, σSet) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeHope :
      Reasoning.Theory.extCodeSizeWord σSet (fileAddressVatTargetWord σSet I) = ⟨0⟩)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNope, outNope) true)
    (hauthSolm : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hvatNoCodeHope :
      (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNope I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I))).option 0
            (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    simpa [evm0, locals] using
      (fileAddressFlapperSourceHopeNoCode (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmNope := evmNope) (outNope := outNope)
        hwv hauthSolm hwhat hvatCodeNope hcallNope hvatNoCodeHope)
  have hrev := RD.vowFileAddressHopeNoCodeWithTarget rd4350 hmem hread64 hcodeSizeHope
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFileAddressFlapperHopeCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel target data what ret : UInt256}
    {evmNope evmHope : EVM.State} {outNope outHope mem rdata : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        target :: data :: what :: ret :: sel :: [])
      mem aw rdata acc k C)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNope, outNope) true)
    (hcallHope :
      typedCallViaEVM config (fileAddressSetFlapperEVM evmNope I)
        (EVM.address (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I)))
        "hope" 0 [.address (fileAddressData I)] (false, evmHope, outHope) true)
    (hrdataSize : rdata.size < UInt256.size)
    (hauthSolm : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNope I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I))).option 0
            (fun acc => acc.code.size))).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    simpa [evm0, locals] using
      (fileAddressFlapperSourceHopeCallFailure (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmNope := evmNope) (evmHope := evmHope) (outNope := outNope)
        (outHope := outHope) hwv hauthSolm hwhat hvatCodeNope hcallNope hvatCodeHope
        hcallHope)
  have hrev := RD.vowFileAddressHopeCallFailure rd4423 hrdataSize
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFileAddressFlapperHopeSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel target data what : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmNope evmHope : EVM.State} {outNope outHope mem rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (rd4423 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4423⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: fileAddressHopeSelector ::
        target :: data :: what :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNope, outNope) true)
    (hcallHope :
      typedCallViaEVM config (fileAddressSetFlapperEVM evmNope I)
        (EVM.address (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I)))
        "hope" 0 [.address (fileAddressData I)] (true, evmHope, outHope) true)
    (hauthSolm : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNope I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcreated : acc.1 = evmHope.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmHope.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body
        (.returned { contract := contract, locals := fileAddressLocalsNopeHope I } evmHope none) := by
    simpa [evm0, locals] using
      (fileAddressFlapperSourceSuccess (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmNope := evmNope) (evmHope := evmHope) (outNope := outNope)
        (outHope := outHope) hwv hauthSolm hwhat hvatCodeNope hcallNope hvatCodeHope
        hcallHope)
  have hret := RD.vowFileAddressHopeCallSuccess rd4423
  have henc : returnEquiv ByteArray.empty none fileAddressTransition.returnType := by
    rw [show fileAddressTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated hAccountsFinal henc

end Benchmarks.Dss.Vow

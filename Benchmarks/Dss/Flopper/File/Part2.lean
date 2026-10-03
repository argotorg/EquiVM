import Benchmarks.Dss.Flopper.File.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper
theorem flopperFileX_unrecognized {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hbeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes)
    (hpad : calldataWord I.calldata 4 ≠ ABI.bytesToWord filePadBytes)
    (httl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes)
    (htau : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes)
    (h : RD flopperBytecode I g s0 ⟨1308⟩
      [fileData I, calldataWord I.calldata 4, ⟨334⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev flopperBytecode g s0 := by
  have rd1309 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1310 := rd1309.dup2 (by native_decide) (by evm_ov)
  have rd1314 := rd1310.pushConst (⟨0x626567⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1316 := rd1314.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1317 := rd1316.shl (by native_decide) (by evm_ov)
  have hbegConst : UInt256.shiftLeft (⟨0x626567⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileBegBytes := by
    native_decide
  rw [hbegConst] at rd1317
  have rd1318 := rd1317.eq (by native_decide) (by evm_ov)
  have hbegEq0 : UInt256.eq (ABI.bytesToWord fileBegBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hbeg h.symm)
  rw [hbegEq0] at rd1318
  have rd1319 := rd1318.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1319
  have rd1322 := rd1319.pushConst (⟨1332⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1332 := rd1322.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  have rd1333 := rd1332.jumpdest (by native_decide) (by evm_ov)
  have rd1334 := rd1333.dup2 (by native_decide) (by evm_ov)
  have rd1338 := rd1334.pushConst (⟨0x1c1859⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1340 := rd1338.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1341 := rd1340.shl (by native_decide) (by evm_ov)
  have hpadConst : UInt256.shiftLeft (⟨0x1c1859⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord filePadBytes := by
    native_decide
  rw [hpadConst] at rd1341
  have rd1342 := rd1341.eq (by native_decide) (by evm_ov)
  have hpadEq0 : UInt256.eq (ABI.bytesToWord filePadBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hpad h.symm)
  rw [hpadEq0] at rd1342
  have rd1343 := rd1342.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1343
  have rd1346 := rd1343.pushConst (⟨1356⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1356 := rd1346.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  have rd1357 := rd1356.jumpdest (by native_decide) (by evm_ov)
  have rd1358 := rd1357.dup2 (by native_decide) (by evm_ov)
  have rd1362 := rd1358.pushConst (⟨0x1d1d1b⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1364 := rd1362.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1365 := rd1364.shl (by native_decide) (by evm_ov)
  have httlConst : UInt256.shiftLeft (⟨0x1d1d1b⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileTtlBytes := by
    native_decide
  rw [httlConst] at rd1365
  have rd1366 := rd1365.eq (by native_decide) (by evm_ov)
  have httlEq0 : UInt256.eq (ABI.bytesToWord fileTtlBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => httl h.symm)
  rw [httlEq0] at rd1366
  have rd1367 := rd1366.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1367
  have rd1370 := rd1367.pushConst (⟨1400⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1400 := rd1370.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  have rd1401 := rd1400.jumpdest (by native_decide) (by evm_ov)
  have rd1402 := rd1401.dup2 (by native_decide) (by evm_ov)
  have rd1406 := rd1402.pushConst (⟨0x746175⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1408 := rd1406.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1409 := rd1408.shl (by native_decide) (by evm_ov)
  have htauConst : UInt256.shiftLeft (⟨0x746175⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileTauBytes := by
    native_decide
  rw [htauConst] at rd1409
  have rd1410 := rd1409.eq (by native_decide) (by evm_ov)
  have htauEq0 : UInt256.eq (ABI.bytesToWord fileTauBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => htau h.symm)
  rw [htauEq0] at rd1410
  have rd1411 := rd1410.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1411
  have rd1414 := rd1411.pushConst (⟨1456⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1456 := rd1414.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.flopperFileUnrecognizedRevert rd1456
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flopperFileBodyCoreBeg
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileWhat I = fileBegBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let data := fileData I
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := fileBegPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, data] using
      (flopperFileBegSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := flopperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flopperFileX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileBegBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flopperFileX_storeBegAuthorized hperm hmatch hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, fileBegPostState, storageStore_accountMap, data])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperFileBodyCorePad
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (hwhat : fileWhat I = filePadBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let data := fileData I
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := filePadPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, data] using
      (flopperFilePadSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg hwhat)
  obtain ⟨_, _, hdecoded⟩ := flopperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flopperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord filePadBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flopperFileX_storePadAuthorized hperm hbegWord hmatch hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, filePadPostState, storageStore_accountMap, data])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperFileBodyCoreTtl
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (hpad : fileWhat I ≠ filePadBytes)
    (hwhat : fileWhat I = fileTtlBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := fileTtlPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (flopperFileTtlSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg hpad hwhat)
  obtain ⟨_, _, hdecoded⟩ := flopperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flopperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have hpadWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord filePadBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hpad (by native_decide)
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTtlBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flopperFileX_storeTtlAuthorized hperm hbegWord hpadWord hmatch hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by
      simp [evm1, evm0, initState, fileTtlPostState, fileTtlPostAccountMap,
        fileTtlStoredWord, fileTtlStoredWordMap, storageStore_accountMap,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperFileBodyCoreTau
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (hpad : fileWhat I ≠ filePadBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (hwhat : fileWhat I = fileTauBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := fileTauPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (flopperFileTauSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg hpad httl hwhat)
  obtain ⟨_, _, hdecoded⟩ := flopperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flopperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have hpadWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord filePadBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hpad (by native_decide)
  have httlWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) httl (by native_decide)
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTauBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flopperFileX_storeTauAuthorized hperm hbegWord hpadWord httlWord hmatch
    hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by
      simp [evm1, evm0, initState, fileTauPostState, fileTauPostAccountMap,
        fileTauStoredWord, fileTauStoredWordMap, storageStore_accountMap,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperFileBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ I ≠ ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
    simpa [evm0, locals] using
      (flopperFileSourceBodyAuthReverts (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := flopperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  exact (flopperFileX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperFileBodyCoreUnrecognized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (hpad : fileWhat I ≠ filePadBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (htau : fileWhat I ≠ fileTauBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
    simpa [evm0, locals] using
      (flopperFileSourceBodyUnrecognized (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg hpad httl htau)
  obtain ⟨_, _, hdecoded⟩ := flopperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flopperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have hpadWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord filePadBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hpad (by native_decide)
  have httlWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) httl (by native_decide)
  have htauWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) htau (by native_decide)
  exact (flopperFileX_unrecognized hbegWord hpadWord httlWord htauWord hswitch)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperFileBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact (flopperFileX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flopperDecode_file_none_short hsz4 hshort)

theorem flopperFileBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 6)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileTransition :=
    flopperDispatchFile hsel
  have hreach := flopperReachFileBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · by_cases hbeg : fileWhat I = fileBegBytes
      · exact flopperFileBodyCoreBeg hcode hsize hperm hwv hsz68 hauth hbeg
          hdispatch (flopperDecode_file_ok hsz68) hreach
      · by_cases hpad : fileWhat I = filePadBytes
        · exact flopperFileBodyCorePad hcode hsize hperm hwv hsz68 hauth hbeg hpad
            hdispatch (flopperDecode_file_ok hsz68) hreach
        · by_cases httl : fileWhat I = fileTtlBytes
          · exact flopperFileBodyCoreTtl hcode hsize hperm hwv hsz68 hauth hbeg hpad httl
              hdispatch (flopperDecode_file_ok hsz68) hreach
          · by_cases htau : fileWhat I = fileTauBytes
            · exact flopperFileBodyCoreTau hcode hsize hperm hwv hsz68 hauth hbeg hpad
                httl htau hdispatch (flopperDecode_file_ok hsz68) hreach
            · exact flopperFileBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hbeg hpad
                httl htau hdispatch (flopperDecode_file_ok hsz68) hreach
    · exact flopperFileBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (flopperDecode_file_ok hsz68) hreach
  · exact flopperFileBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flopper

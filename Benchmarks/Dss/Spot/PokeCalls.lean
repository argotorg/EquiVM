import Benchmarks.Dss.Spot.PokeArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

theorem evalExpr_pokeStorageVatOfLocals {evm : EVM.State} {locals : Store}
    (hvat : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (pokeVatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (pokeVatAddress evm.accountMap evm.executionEnv))
    hvat
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, vatRef, addrSt])
    (by rfl)
    (by
      simpa [pokeVatAddress, pokeVatTargetWord, spotAddressReturnWord, spotSlotWord] using
        spotStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_pokeVatCodeGuard_false_ofLocals {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (pokeVatAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_pokeVatCodeGuard_true_ofLocals {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (pokeVatAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExprs_pokeVatFileArgs
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) (spot : UInt256) :
    evalExprs? config { contract := contract, locals := pokeSpotLocals I out spot } evm
      [.var "ilk", spotParamLit, .var "spot"] =
        .ok [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes, .int (Int.ofNat spot.toNat)] := by
  have hilk :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out spot } evm
        (.var "ilk") = .ok (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((pokeSpotLocals I out spot).get? "ilk") =
      .ok (.fixedBytes bytes32Width (pokeIlkBytes I))
    rw [pokeSpotLocals_get_ilk]
    rfl
  have hwhat :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out spot } evm
        spotParamLit = .ok (.fixedBytes bytes32Width pokeSpotParamBytes) := by
    simp [spotParamLit, pokeSpotParamBytes, evalExpr?, pure]
  have hspot :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out spot } evm
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((pokeSpotLocals I out spot).get? "spot") =
      .ok (.int (Int.ofNat spot.toNat))
    rw [pokeSpotLocals_get_spot]
    rfl
  simp [evalExprs?, hilk, hwhat, hspot, EvalResult.bind, bind, pure]

theorem pokeSpotParamBytes_eq_toBytesBE :
    pokeSpotParamBytes = EVM.Word.toBytesBE pokeSpotParamWord := by
  native_decide

theorem pokeVatFileEncode_eq (I : ExecutionEnv) (spot : UInt256) {mem : ByteArray}
    (hsz36 : 36 ≤ I.calldata.size) (hmem : mem.size = 192) :
    config.externalABI.encode? "file"
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes, .int (Int.ofNat spot.toNat)] =
      some ((pokeVatFileCalldataMem I spot mem).readWithPadding
        pokeVatFileOutPtr.toNat pokeVatFileInSize.toNat) := by
  change config.externalABI.encode? "file"
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes, .int (Int.ofNat spot.toNat)] =
      some ((pokeVatFileCalldataMem I spot mem).readWithPadding 128 100)
  rw [pokeVatFileCalldataMem_read128_100 I spot hmem]
  have hilkBytes := pokeIlkBytes_eq_toBytesBE (I := I) hsz36
  have hilkLen : (EVM.Word.toBytesBE (pokeIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (pokeIlkWord I)
  have hwhatLen : (EVM.Word.toBytesBE pokeSpotParamWord).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size pokeSpotParamWord
  have hspotLt : spot.toNat < EVM.twoPow 256 := by
    simp [UInt256.toNat, UInt256.size, EVM.twoPow, spot.val.isLt]
  have hspotWord : EVM.word spot.toNat = spot := by
    simpa [UInt256.ofNat] using u256_ofNat_toNat spot
  simp [config, spotExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, uint256, uint256Int,
    vatFileSelector, selectorBytes, hilkBytes, pokeSpotParamBytes_eq_toBytesBE, hilkLen,
    hwhatLen, ABI.zeroBytes, hspotLt, hspotWord, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

theorem pokeVatFileDecode_ok (out : ByteArray) :
    config.externalABI.decode? "file" out = some [] := by
  simp [config, spotExternalABI]

theorem pokeParWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    pokeParWord σ I = pokeParWord τ I := by
  have hslot : spotSlotWord ⟨3⟩ σ I = spotSlotWord ⟨3⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  simpa [pokeParWord] using hslot

theorem pokeMatWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    pokeMatWord σ I = pokeMatWord τ I := by
  have hslot : spotSlotWord (pokeMatSlotFor I) σ I =
      spotSlotWord (pokeMatSlotFor I) τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (pokeMatSlotFor I) ⟨0⟩
  simpa [pokeMatWord] using hslot

theorem pokePipTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hAccounts : accountMapEquiv σ τ) :
    pokePipTargetWord σ I = pokePipTargetWord τ I := by
  have hslot : spotSlotWord (pokePipSlotFor I) σ I =
      spotSlotWord (pokePipSlotFor I) τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (pokePipSlotFor I) ⟨0⟩
  simp [pokePipTargetWord, pokePipRawWord, hslot]

theorem pokePipAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hAccounts : accountMapEquiv σ τ) :
    pokePipAddress σ I = pokePipAddress τ I := by
  apply Fin.ext
  simp [pokePipAddress, pokePipTargetWord_accountMapEquiv hsz36 hAccounts]

theorem pokePipCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (pokePipTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (pokePipTargetWord σ I)
  have htarget : pokePipTargetWord σ I = pokePipTargetWord τ I :=
    pokePipTargetWord_accountMapEquiv hsz36 hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem pokePipCodeSize_ne_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (pokePipTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  exact hne (pokePipCodeSize_zero_accountMapEquiv hsz36 hAccounts.symm hzero)

theorem pokePipAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    pokePipAddress σ I = AccountAddress.ofUInt256 (pokePipTargetWord σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem spotEvmAddress_accountAddress (a : AccountAddress) :
    EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

theorem pokePipEvmAddress_eq_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (pokePipAddress σ_solm I) =
      AccountAddress.ofUInt256 (pokePipTargetWord σ_evm I) := by
  have haddr : pokePipAddress σ_solm I = pokePipAddress σ_evm I :=
    (pokePipAddress_accountMapEquiv hsz36 hAccounts).symm
  rw [haddr, pokePipAddress_eq_target σ_evm I]
  exact spotEvmAddress_accountAddress _

theorem pokeVatTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    pokeVatTargetWord σ I = pokeVatTargetWord τ I := by
  have hslot : spotSlotWord ⟨2⟩ σ I = spotSlotWord ⟨2⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  simp [pokeVatTargetWord, spotAddressReturnWord, hslot]

theorem pokeVatAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    pokeVatAddress σ I = pokeVatAddress τ I := by
  apply Fin.ext
  simp [pokeVatAddress, pokeVatTargetWord_accountMapEquiv hAccounts]

theorem pokeVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (pokeVatTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (pokeVatTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (pokeVatTargetWord σ I)
  have htarget : pokeVatTargetWord σ I = pokeVatTargetWord τ I :=
    pokeVatTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem pokeVatCodeSize_ne_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (pokeVatTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (pokeVatTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  exact hne (pokeVatCodeSize_zero_accountMapEquiv hAccounts.symm hzero)

theorem pokeVatAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    pokeVatAddress σ I = AccountAddress.ofUInt256 (pokeVatTargetWord σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem pokeVatEvmAddress_eq_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (pokeVatAddress σ_solm I) =
      AccountAddress.ofUInt256 (pokeVatTargetWord σ_evm I) := by
  have haddr : pokeVatAddress σ_solm I = pokeVatAddress σ_evm I :=
    (pokeVatAddress_accountMapEquiv hAccounts).symm
  rw [haddr, pokeVatAddress_eq_target σ_evm I]
  exact spotEvmAddress_accountAddress _

theorem poke_extCodeSizeWord_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
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

theorem pokePipCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    poke_extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := pokePipTargetWord σ I) (addr := pokePipAddress σ I)
      (pokePipAddress_eq_target σ I) hzero

theorem pokePipCode_pos_of_codeSize_ne_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (pokePipAddress σ I)).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (pokePipAddress σ I)).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) := by
    cases hacc : σ.find? (AccountAddress.ofUInt256 (pokePipTargetWord σ I)) <;>
      simp [initState, State.lookupAccount, Reasoning.Theory.extCodeSizeWord,
        pokePipAddress_eq_target σ I, hacc, Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem pokeVatCode_zero_of_codeSize_zero {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (pokeVatTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    poke_extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := pokeVatTargetWord evm.accountMap evm.executionEnv)
      (addr := pokeVatAddress evm.accountMap evm.executionEnv)
      (pokeVatAddress_eq_target evm.accountMap evm.executionEnv) hzero

theorem pokeVatCode_pos_of_codeSize_ne_zero {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (pokeVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat
        ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat
        ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size)) =
        Reasoning.Theory.extCodeSizeWord evm.accountMap
          (pokeVatTargetWord evm.accountMap evm.executionEnv) := by
    cases hacc :
        evm.accountMap.find?
          (AccountAddress.ofUInt256
            (pokeVatTargetWord evm.accountMap evm.executionEnv)) <;>
      simp [State.lookupAccount, Reasoning.Theory.extCodeSizeWord,
        pokeVatAddress_eq_target evm.accountMap evm.executionEnv, hacc, Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem typedCallViaEVM_zero_substate_irrel {cfg : Config} {evm evm' : EVM.State}
    {A0 : Substate} {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
      (z, evm', out) callPerm)
    (hdepth : evm.executionEnv.depth ≠ 1024) :
    typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) callPerm := by
  rcases hcall with ⟨calldata, henc, hraw⟩
  refine ⟨calldata, henc, ?_⟩
  cases hraw with
  | callMade hvalue hTheta hevm' hvalue' hdepth' =>
      obtain ⟨callGas, A_in, hTheta⟩ := hTheta
      exact callViaEVM.callMade (perm := callPerm) hvalue
        ⟨callGas, A_in, by simpa using hTheta⟩
        (by simpa using hevm')
        (by simpa using hvalue')
        (by simpa using hdepth')
  | callNotMade _hsubstate _hevm' hvalue =>
      exfalso
      apply hvalue
      constructor
      · rw [wordOfInt_zero]
        show (⟨0⟩ : UInt256) ≤ _
        exact Fin.zero_le _
      · exact hdepth

theorem evalExpr_pokeStoragePip {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (henv : evm.executionEnv = I) :
    evalExpr? config { contract := contract, locals := pokeLocals I } evm
      (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm.accountMap I)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := pokeLocals I }) (evm := evm)
    (slot := ilksF (.var "ilk") "pip") (er := pokePipEvaledRef I)
    (t := .address) (loc := addrLoc (pokePipSlotFor I))
    (value := .address (pokePipAddress evm.accountMap I))
    (pokeLocals_get_ilks I)
    (by
      have hkeyLen : (pokeIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using pokeIlkBytes_len32 (I := I) hsz36
      simp [pokePipEvaledRef, pokeIlkKey, pokeIlkValue, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [pokeIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, addrSt])
    (by rfl)
    (by
      cases henv
      simpa [pokePipAddress, pokePipTargetWord, pokePipRawWord, spotSlotWord] using
        spotStorageLocLoad_address_offset0 evm (pokePipSlotFor evm.executionEnv))

theorem evalExpr_pokePipCodeGuard_false {evm : EVM.State} {I : ExecutionEnv}
    (_hsz36 : 36 ≤ I.calldata.size)
    (hpip :
      evalExpr? config { contract := contract, locals := pokeLocals I } evm
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (pokePipAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := pokeLocals I } evm
      (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hpip, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_pokePipCodeGuard_true {evm : EVM.State} {I : ExecutionEnv}
    (_hsz36 : 36 ≤ I.calldata.size)
    (hpip :
      evalExpr? config { contract := contract, locals := pokeLocals I } evm
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (pokePipAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := pokeLocals I } evm
      (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hpip, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExprs_pokePeekArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := pokeLocals I } evm [] = .ok [] := by
  change (pure [] : EvalResult (List Value)) = .ok []
  rfl
end Benchmarks.Dss.Spot

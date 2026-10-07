import Reasoning.SolcRoutines
import Benchmarks.Dss.Vow.Deny

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `rely(address)` -/

abbrev relyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev relyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev relyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (relyUsr I))] }

abbrev relySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (relyUsr I))

abbrev liveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

theorem relySlotFor_eq (I : ExecutionEnv) :
    relySlotFor I = solcMappingSlot ⟨0⟩ (relyKey I) := by
  unfold relySlotFor relyUsr relyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem vowLiveGuardEval_true {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hload : Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
      ⟨12⟩ = ⟨1⟩ := by
    simpa [solcSlotWordAt] using hlive
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState σ σ₀ g A I) liveRef = .ok liveEvaledRef := by
    simp [liveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar (hbackend := rfl)
    (t := .int uint256Int) (loc := wordLoc ⟨12⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw, liveEvaledRef])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem vowLiveGuardEval_false {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : solcSlotWordAt ⟨12⟩ σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  let w := Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner ⟨12⟩
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hlive (by simpa [w, solcSlotWordAt] using hw)
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState σ σ₀ g A I) liveRef = .ok liveEvaledRef := by
    simp [liveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar (hbackend := rfl)
    (t := .int uint256Int) (loc := wordLoc ⟨12⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw, liveEvaledRef])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

/-! ### `live` guard and store-one bytecode helpers -/

@[reducible] def vowLiveGuardTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  p10 + ⟨1⟩

@[reducible] def vowLiveGuardWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.EQ, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)

abbrev vowNotLiveRawWord : UInt256 :=
  ⟨26750464447179039505881069157⟩

theorem RD.vowLiveGuardOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata σ k C)
    (hwf : vowLiveGuardWf code pc okPc)
    (hlive : solcSlotWord σ ee ⟨12⟩ = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R) mem (UInt256.ofNat 3) rdata
      σ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨12⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have hliveRaw :
      (σ.get? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rd4
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have rd7 := rd7₀
  rw [uInt256_eq_self] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  exact ⟨_, _, rd10.jumpiT hd10 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.vowLiveGuardRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata σ k C)
    (hwf : vowLiveGuardWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (vowLiveGuardTailPc pc) ⟨12⟩
      vowNotLiveRawWord ⟨160⟩ .PUSH12 12)
    (hlive : solcSlotWord σ ee ⟨12⟩ ≠ ⟨1⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨12⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have hliveRaw :
      (σ.get? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.get? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hliveRaw h1.symm)
  have rd7 := rd7₀
  rw [heq0] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  have rdTail₀ := rd10.jumpiNT hd10 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [vowLiveGuardTailPc] using rdTail₀) htail
    (by decide) (by rfl) hmem hread64 (by simpa only [List.length_cons] using hov)


/-! ### Dispatch, ABI, reachability, and body proof -/

theorem vowDispatch_rely {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    dispatchMsg contract I.calldata = some relyTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition, healTransition,
      humpTransition, kissTransition, liveTransition])
    (post := [sinTransition, sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := relyTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes, healSelectorBytes,
        humpSelectorBytes, kissSelectorBytes, liveSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, relySelectorBytes]
    exact hsel

theorem vowDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (relyUsr I))) := by
  simpa [config, relyTransition, relyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem vowDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem vowReachRelyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        ⟨517⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vowSelWord I = ⟨1710941022⟩ :=
    vowSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨1710941022⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc 3))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowHighBody 3 (by omega) ⟨517⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem vowRelyBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "usr" (.address (relyUsr I))))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨517⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let key := relyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := vowCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (relyUsr I))
  have hslot : relySlotFor I = slot := by
    simp [slot, key, relySlotFor_eq]
  have hcallerWord : solcSlotWordAt callerSlot σ I = solcSlotWordAt callerSlot σ I := rfl
  have hliveWord : solcSlotWordAt ⟨12⟩ σ I = solcSlotWordAt ⟨12⟩ σ I := rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨517⟩) (ret := ⟨412⟩)
    (decoded := ⟨539⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vowBytecode) (decoded := ⟨539⟩) (ret := ⟨412⟩) (routine := ⟨2294⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  by_cases hauthEvm : solcSlotWordAt callerSlot σ I = ⟨1⟩
  · have hauthSolm : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, solcSlotWordAt] using hauthEvm
    obtain ⟨_, _, hafterAuth⟩ := RD.solcAuthCheckOk
      (code := vowBytecode) (pc := ⟨2294⟩) (okPc := ⟨2383⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold solcAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    by_cases hliveEvm : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩
    · have hliveSolm : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ := by
        rw [← hliveWord]
        exact hliveEvm
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (relySlotFor I) ⟨1⟩
      have hguardAuth := vowAuthGuardEval_true
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hguardLive := vowLiveGuardEval_true
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hliveSolm
      have hassign :
          assignStorageRef? config { contract := contract, locals := locals } evm0
            .storage (wardsRef (.var "usr")) (.int 1) =
              .ok ({ contract := contract, locals := locals }, evm1) := by
        have her :
            evalStorageRef config { contract := contract, locals := locals } evm0
              (wardsRef (.var "usr")) = .ok (relyEvaledRef I) := by
          simp [evm0, relyEvaledRef, relyUsr, wardsRef, evalStorageRef,
            evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
            EvalResult.ofOption, EvalResult.bind, pure, bind, locals]
        have hstore :
            storageLocStore evm0 (wordLoc (relySlotFor I)) (.int 1) = some evm1 := by
          simpa [evm1] using storageLocStore_uint256 evm0 (relySlotFor I) ⟨1⟩
        exact assignStorageRef_storage_scalar (hbackend := rfl)
          (hleaf := Or.inl ⟨_, rfl⟩)
          (ty := .elem (.int uint256Int)) (loc := wordLoc (relySlotFor I))
          (hbase := by simp [locals, wardsRef])
          (her := her)
          (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
          (hloc := by
            simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw,
              relyEvaledRef, relySlotFor])
          (hstore := hstore)
      have hpre : ∀ r, ExecBlock config { contract := contract, locals := locals } evm0
          [.assign .storage (wardsRef (.var "usr")) (.intLit 1)] r →
          ExecBlock config { contract := contract, locals := locals } evm0
            [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
              .require (.binary .eq (.storage liveRef) (.intLit 1)),
              .assign .storage (wardsRef (.var "usr")) (.intLit 1) ] r := by
        intro r hrest
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
        exact hrest
      have hbody :
          ExecTransitionBody config contract evm0 locals relyTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0, evm1] using
          ExecFuncBody.execBlockOK (hpre _ (ExecBlock.consNormal
            (ExecStmt.assign (by simp [evalExpr?, pure]) hassign) ExecBlock.nil))
      have hliveSolc : solcSlotWord σ I ⟨12⟩ = ⟨1⟩ := by
        simpa [solcSlotWordAt] using hliveEvm
      obtain ⟨_, _, hstorePc⟩ := RD.vowLiveGuardOk
        (code := vowBytecode) (pc := ⟨2383⟩) (okPc := ⟨2453⟩) (key := key)
        (ret := ⟨412⟩) (R := [sel]) hafterAuth
        (by
          unfold vowLiveGuardWf
          repeat' first | apply And.intro | native_decide)
        hliveSolc (by jump_dest) (by simp)
      have hmemAuth :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hcanonKey : key.toNat < EVM.addressModulus := by
        dsimp [key, relyKey]
        rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
        exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
      have hstore := RD.solcMapping0StoreOneSplit
        (code := vowBytecode) (pc := ⟨2453⟩) (key := key) (ret := ⟨412⟩) (R := [sel])
        hstorePc
        (by
          unfold solcMapping0StoreOneWf
          repeat' first | apply And.intro | native_decide)
        (by jump_dest) hmemAuth hcanonKey (by simp)
      by_cases hperm : I.perm = true
      swap
      · have hpf : I.perm = false := by simpa using hperm
        exact (permSplit_false hpf hstore).reEquivStaticHalt hcode hdispatch hdecode
          (by
            simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0] using
              ExecFuncBody.execBlockStatic (hpre _ (ExecBlock.consStatic
                (ExecStmt.assignStatic (by simp [evalExpr?, pure]) hassign
                  (by simp [evm0, initState]; exact hpf)))))
      obtain ⟨_, _, hretPc⟩ := permSplit_true hperm hstore
      have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
      have hret :
          RDret vowBytecode (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (sstoreAccountMap I.codeOwner σ slot ⟨1⟩) ByteArray.empty := by
        simpa [slot] using RD.stop hretPc' (by native_decide) (by simp)
      have haccounts :
          sstoreAccountMap I.codeOwner σ slot ⟨1⟩ = evm1.accountMap := by
        simp [evm1, evm0, initState, storageStore_accountMap, hslot]
      have henc : returnEquiv ByteArray.empty none relyTransition.returnType := by
        rw [show relyTransition.returnType = [] by rfl]
        exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
      exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
        haccounts henc
    · have hliveSolm : solcSlotWordAt ⟨12⟩ σ I ≠ ⟨1⟩ := by
        intro hsolm
        exact hliveEvm (by rw [hliveWord, hsolm])
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
        have hguardAuth := vowAuthGuardEval_true
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := vowLiveGuardEval_false
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hliveSolm
        have hblock :
            ExecBlock config { contract := contract, locals := locals } evm0
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                .require (.binary .eq (.storage liveRef) (.intLit 1)),
                .assign .storage (wardsRef (.var "usr")) (.intLit 1) ]
              .reverted := by
          refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
          · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
          exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
        simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0] using
          ExecFuncBody.execBlockRevert hblock
      have hliveSolc : solcSlotWord σ I ⟨12⟩ ≠ ⟨1⟩ := by
        simpa [solcSlotWordAt] using hliveEvm
      have hmemAuth :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hread64 :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
          solcFreePtrMem_read64
      have hrev := RD.vowLiveGuardRevert
        (code := vowBytecode) (pc := ⟨2383⟩) (okPc := ⟨2453⟩) (key := key)
        (ret := ⟨412⟩) (R := [sel]) hafterAuth
        (by
          unfold vowLiveGuardWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold solcErrorStringRevertTailWf vowLiveGuardTailPc vowNotLiveRawWord
          repeat' first | apply And.intro | native_decide)
        hliveSolc hmemAuth hread64 (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : solcSlotWordAt callerSlot σ I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
      have hguard := vowAuthGuardEval_false
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .assign .storage (wardsRef (.var "usr")) (.intLit 1)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, solcSlotWordAt] using hauthEvm
    have hrev := RD.vowAuthCheckRevert
      (code := vowBytecode) (pc := ⟨2294⟩) (okPc := ⟨2383⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold solcAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf solcAuthTailPc vowNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowRelyBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := by omega
  exact vowRelyBodyCore hcode hwv hsz36 hsize (vowDispatch_rely hsel)
    (vowDecode_rely_ok hsz36)
    (vowReachRelyBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

theorem vowRelyShort {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hreach :=
    vowReachRelyBody (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨517⟩) (ret := ⟨412⟩)
    (decoded := ⟨539⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_rely hsel)
    (vowDecode_rely_none_short hsz4 hshort)

end Benchmarks.Dss.Vow

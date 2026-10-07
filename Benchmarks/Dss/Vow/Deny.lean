import Reasoning.SolcRoutines
import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `deny(address)` -/

abbrev denyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev denyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev denyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (denyUsr I))] }

abbrev denySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (denyUsr I))

theorem denySlotFor_eq (I : ExecutionEnv) :
    denySlotFor I = solcMappingSlot ⟨0⟩ (denyKey I) := by
  unfold denySlotFor denyUsr denyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

abbrev vowCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

abbrev vowCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

theorem vowCallerWardsEvaledRef_ok {σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef config { contract := contract, locals := locals }
      (initState σ σ₀ g A I) (wardsRef sender) =
        .ok (vowCallerWardsEvaledRef I) := by
  simp [vowCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem vowAuthGuardEval_true {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := vowCallerWardsEvaledRef_ok (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload : Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
      (vowCallerWardsSlot I) = ⟨1⟩ := by
    simpa [solcSlotWordAt] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar (hbackend := rfl)
    (t := .int uint256Int) (loc := wordLoc (vowCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw,
        vowCallerWardsEvaledRef, vowCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem vowAuthGuardEval_false {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : solcSlotWordAt (vowCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := vowCallerWardsEvaledRef_ok (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
      (vowCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, solcSlotWordAt] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar (hbackend := rfl)
    (t := .int uint256Int) (loc := wordLoc (vowCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw,
        vowCallerWardsEvaledRef, vowCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

/-! ### Auth and store bytecode helpers -/


abbrev vowNotAuthorizedRawWord : UInt256 :=
  ⟨1882396589317237868685917121345356193241433⟩


theorem RD.vowAuthCheckRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcAuthTailPc pc) ⟨18⟩
      vowNotAuthorizedRawWord ⟨114⟩ .PUSH18 18)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 :=
  Reasoning.Reach.RD.solcAuthCheckRevert18 h hwf htail hauth hov


/-! ### Dispatch, ABI, reachability, and body proof -/

theorem vowDispatch_deny {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩) :
    dispatchMsg contract I.calldata = some denyTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition])
    (post := [dumpTransition, fessTransition, fileUintTransition, fileAddressTransition,
      flapTransition, flapperTransition, flogTransition, flopTransition, flopperTransition,
      healTransition, humpTransition, kissTransition, liveTransition, relyTransition,
      sinTransition, sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := denyTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, denySelectorBytes]
    exact hsel

theorem vowDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (denyUsr I))) := by
  simpa [config, denyTransition, denyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem vowDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  simpa [config, denyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem vowReachDenyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        ⟨608⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vowSelWord I = ⟨2622662641⟩ :=
    vowSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨2622662641⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc 2))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighLowBody 2 (by omega) ⟨608⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

theorem vowDenyBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "usr" (.address (denyUsr I))))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨608⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let key := denyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := vowCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (denyUsr I))
  have hslot : denySlotFor I = slot := by
    simp [slot, key, denySlotFor_eq]
  have hcallerWord : solcSlotWordAt callerSlot σ I = solcSlotWordAt callerSlot σ I := rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨608⟩) (ret := ⟨412⟩)
    (decoded := ⟨630⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vowBytecode) (decoded := ⟨630⟩) (ret := ⟨412⟩) (routine := ⟨3474⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  by_cases hauthEvm : solcSlotWordAt callerSlot σ I = ⟨1⟩
  · have hauthSolm : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (denySlotFor I) ⟨0⟩
    have hguard := vowAuthGuardEval_true
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (locals := locals)
      (by simp [locals]) hauthSolm
    have hassign :
        assignStorageRef? config { contract := contract, locals := locals } evm0
          .storage (wardsRef (.var "usr")) (.int 0) =
            .ok ({ contract := contract, locals := locals }, evm1) := by
      have her :
          evalStorageRef config { contract := contract, locals := locals } evm0
            (wardsRef (.var "usr")) = .ok (denyEvaledRef I) := by
        simp [evm0, denyEvaledRef, denyUsr, wardsRef, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, locals]
      have hstore :
          storageLocStore evm0 (wordLoc (denySlotFor I)) (.int 0) = some evm1 := by
        simpa [evm1] using storageLocStore_uint256 evm0 (denySlotFor I) ⟨0⟩
      exact assignStorageRef_storage_scalar (hbackend := rfl)
          (hleaf := Or.inl ⟨_, rfl⟩)
        (ty := .elem (.int uint256Int)) (loc := wordLoc (denySlotFor I))
        (hbase := by simp [locals, wardsRef])
        (her := her)
        (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (hloc := by
          simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw,
            denyEvaledRef, denySlotFor])
        (hstore := hstore)
    have hbody :
        ExecTransitionBody config contract evm0 locals denyTransition.body
          (.returned { contract := contract, locals := locals } evm1 none) := by
      have hblock := nonpayableRequireAssignStorageBlock
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0) (evm' := evm1)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rhs := .intLit 0) (ref := wardsRef (.var "usr")) (value := .int 0)
        (by simp [evm0, initState]; exact hwv)
        hguard (by simp [evalExpr?, pure]) hassign
      simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0, evm1] using
        ExecFuncBody.execBlockOK hblock
    have hauthSolc : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, solcSlotWordAt] using hauthEvm
    obtain ⟨_, _, hokPc⟩ := RD.solcAuthCheckOk
      (code := vowBytecode) (pc := ⟨3474⟩) (okPc := ⟨3563⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, denyKey] using hroutine)
      (by
        unfold solcAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    have hmemAuth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
      twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    have hcanonKey : key.toNat < EVM.addressModulus := by
      dsimp [key, denyKey]
      rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
      exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
    have hstore := RD.solcMapping0StoreZeroSplit
      (code := vowBytecode) (pc := ⟨3563⟩) (key := key) (ret := ⟨412⟩) (R := [sel])
      hokPc
      (by
        unfold solcMapping0StoreZeroWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) hmemAuth hcanonKey (by simp)
    by_cases hperm : I.perm = true
    swap
    · have hpf : I.perm = false := by simpa using hperm
      exact (permSplit_false hpf hstore).reEquivStaticHalt hcode hdispatch hdecode
        (by
          simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0] using
            ExecFuncBody.execBlockStatic (nonpayableRequireAssignStorageBlockStatic
              (cfg := config) (solm := { contract := contract, locals := locals })
              (evm := evm0)
              (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
              (rhs := .intLit 0) (ref := wardsRef (.var "usr")) (value := .int 0)
              (rest := [])
              (by simp [evm0, initState]; exact hwv)
              hguard (by simp [evalExpr?, pure]) hassign
              (by simp [evm0, initState]; exact hpf)))
    obtain ⟨_, _, hretPc⟩ := permSplit_true hperm hstore
    have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
    have hret :
        RDret vowBytecode (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (sstoreAccountMap I.codeOwner σ slot ⟨0⟩) ByteArray.empty := by
      simpa [slot] using RD.stop hretPc' (by native_decide) (by simp)
    have haccounts :
        sstoreAccountMap I.codeOwner σ slot ⟨0⟩ = evm1.accountMap := by
      simp [evm1, evm0, initState, storageStore_accountMap, hslot]
    have henc : returnEquiv ByteArray.empty none denyTransition.returnType := by
      rw [show denyTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
      haccounts henc
  · have hauthSolm : solcSlotWordAt callerSlot σ I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals denyTransition.body .reverted := by
      have hguard := vowAuthGuardEval_false
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 0)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, solcSlotWordAt] using hauthEvm
    have hrev := RD.vowAuthCheckRevert
      (code := vowBytecode) (pc := ⟨3474⟩) (okPc := ⟨3563⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, denyKey] using hroutine)
      (by
        unfold solcAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf solcAuthTailPc vowNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowDenyBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := by omega
  exact vowDenyBodyCore hcode hwv hsz36 hsize (vowDispatch_deny hsel)
    (vowDecode_deny_ok hsz36)
    (vowReachDenyBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

theorem vowDenyShort {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hreach :=
    vowReachDenyBody (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨608⟩) (ret := ⟨412⟩)
    (decoded := ⟨630⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_deny hsel)
    (vowDecode_deny_none_short hsz4 hshort)

end Benchmarks.Dss.Vow

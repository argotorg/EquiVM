import Benchmarks.Dss.Cat.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `rely(address)` — LOW-HIGH dispatch arm 1, entry ⟨445⟩

Cat's `rely` has NO live-guard (unlike Vow's rely): its transition is exactly
`nonpayable ++ auth ++ [.assign .storage (wardsRef (.var "usr")) (.intLit 1)]`, i.e. structurally
identical to `deny` but storing `1` instead of `0`. -/

abbrev relyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev relyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev relyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (relyUsr I))] }

abbrev relySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (relyUsr I))

theorem relySlotFor_eq (I : ExecutionEnv) :
    relySlotFor I = solcMappingSlot ⟨0⟩ (relyKey I) := by
  unfold relySlotFor relyUsr relyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

/-! ### Dispatch, ABI, reachability -/

theorem catDispatch_rely {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    dispatchMsg contract I.calldata = some relyTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition,
      ilksTransition, litterTransition, liveTransition])
    (post := [vatTransition, vowTransition, wardsTransition])
    (ti := relyTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes, fileIlkFlipSelectorBytes,
        fileIlkUintSelectorBytes, fileUintSelectorBytes, ilksSelectorBytes, litterSelectorBytes,
        liveSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, relySelectorBytes]
    exact hsel

theorem catDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (relyUsr I))) := by
  simpa [config, relyTransition, relyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem catDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem catReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨445⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : catSelWord I = ⟨1710941022⟩ :=
    catSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨1710941022⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc 1))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact catReachLowHighBody 1 (by omega) ⟨445⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

/-! ### Body core -/

theorem catRelyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "usr" (.address (relyUsr I))))
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨445⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := relyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := catCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (relyUsr I))
  have hslot : relySlotFor I = slot := by
    simp [slot, key, relySlotFor_eq]
  have hcallerWord : catSlotWord callerSlot σ_evm I = catSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨445⟩) (ret := ⟨302⟩)
    (decoded := ⟨467⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := catBytecode) (decoded := ⟨467⟩) (ret := ⟨302⟩) (routine := ⟨2715⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  by_cases hauthEvm : catSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : catSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (relySlotFor I) ⟨1⟩
    have hbody :
        ExecTransitionBody config contract evm0 locals relyTransition.body
          (.returned { contract := contract, locals := locals } evm1 none) := by
      have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
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
        exact assignStorageRef_storage_scalar
          (ty := .elem (.int uint256Int)) (loc := wordLoc (relySlotFor I))
          (hbase := by simp [locals, wardsRef])
          (her := her)
          (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
          (hloc := by
            funext evm
            simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
              relyEvaledRef, relySlotFor])
          (hstore := hstore)
      have hblock := nonpayableRequireAssignStorageBlock
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0) (evm' := evm1)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rhs := .intLit 1) (ref := wardsRef (.var "usr")) (value := .int 1)
        (by simp [evm0, initState]; exact hwv)
        hguard (by simp [evalExpr?, pure]) hassign
      simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0, evm1] using
        ExecFuncBody.execBlockOK hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    obtain ⟨_, _, hokPc⟩ := RD.catAuthCheckOk
      (code := catBytecode) (pc := ⟨2715⟩) (okPc := ⟨2804⟩) (key := key)
      (ret := ⟨302⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold catAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    have hmemAuth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
      twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    have hcanonKey : key.toNat < EVM.addressModulus := by
      dsimp [key, relyKey]
      rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
      exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
    obtain ⟨_, _, hretPc⟩ := RD.catRelyStoreOne
      (code := catBytecode) (pc := ⟨2804⟩) (key := key) (ret := ⟨302⟩) (R := [sel])
      hokPc
      (by
        unfold catRelyStoreOneWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) hperm hmemAuth hcanonKey (by simp)
    have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
    have hret :
        RDret catBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩) ByteArray.empty := by
      simpa [slot] using RD.stop hretPc' (by native_decide) (by simp)
    have hcreated :
        (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩).1 = evm1.createdAccounts := by
      simp [evm1, evm0, initState, storageStore_createdAccounts]
    have haccounts :
        accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩).2
          evm1.accountMap := by
      simpa [evm1, evm0, initState, storageStore_accountMap, hslot] using
        accountMapEquiv_sstoreAccountMap I.codeOwner slot ⟨1⟩ hAccounts
    have henc : returnEquiv ByteArray.empty none relyTransition.returnType := by
      rw [show relyTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      hcreated haccounts henc
  · have hauthSolm : catSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
      have hguard := catAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 1)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    have hrev := RD.catAuthCheckRevert
      (code := catBytecode) (pc := ⟨2715⟩) (okPc := ⟨2804⟩) (key := key)
      (ret := ⟨302⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold catAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf catAuthTailPc catNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem catRelyShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    catReachRelyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := catBytecode) (sel := catSelWord I) (entry := ⟨445⟩) (ret := ⟨302⟩)
    (decoded := ⟨467⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (catDispatch_rely hsel)
    (catDecode_rely_none_short hsz4 hshort)

theorem catRelyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ (by native_decide) hsel
  by_cases hshort : I.calldata.size < 36
  · exact catRelyShort hcode hsize hperm hwv hsz hshort hsel hAccounts
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    exact catRelyBodyCore hcode hwv hperm hsz36 hsize (catDispatch_rely hsel)
      (catDecode_rely_ok hsz36)
      (catReachRelyBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      hAccounts

end Benchmarks.Dss.Cat

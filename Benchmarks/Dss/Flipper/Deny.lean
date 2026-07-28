import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## `deny(address)` -/

theorem flipperDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata =
        some (flipperUsrStore I) := by
  simpa [config, denyTransition, flipperUsrStore, flipperUsrValue, flipperUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem flipperDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  simpa [config, denyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem flipperReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 5)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨757⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x9c52a7f1⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨0x9c52a7f1⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc 1))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachLowLowBody 1 (by omega) ⟨757⟩ hcode hwv hsz hsize hroot hlow
    heq0 htake (by jump_dest) (by native_decide)

theorem flipperDenyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (flipperUsrStore I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨757⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := flipperUsrKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := flipperCallerWardsSlot I
  let locals : Store := flipperUsrStore I
  have hslot : flipperUsrSlotFor I = slot := by
    simp [slot, key, flipperUsrSlotFor_eq]
  have hcallerWord : flipperSlotWord callerSlot σ_evm I = flipperSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨757⟩) (ret := ⟨323⟩)
    (decoded := ⟨779⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := flipperBytecode) (decoded := ⟨779⟩) (ret := ⟨323⟩) (routine := ⟨5233⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  by_cases hauthEvm : flipperSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : flipperSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (flipperUsrSlotFor I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract evm0 locals denyTransition.body
          (.returned { contract := contract, locals := locals } evm1 none) := by
      have hguard := flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (locals := locals) (by simp [locals, flipperUsrStore]) hauthSolm
      have hassign :
          assignStorageRef? config { contract := contract, locals := locals } evm0
            .storage (wardsRef (.var "usr")) (.int 0) =
              .ok ({ contract := contract, locals := locals }, evm1) := by
        have her :
            evalStorageRef config { contract := contract, locals := locals } evm0
              (wardsRef (.var "usr")) = .ok (flipperUsrEvaledRef I) := by
          simp [evm0, flipperUsrEvaledRef, flipperUsr, flipperUsrStore, wardsRef,
            evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
            valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind, locals]
        have hstore :
            storageLocStore evm0 (wordLoc (flipperUsrSlotFor I)) (.int 0) = some evm1 := by
          simpa [evm1] using flipperStorageLocStore_uint256 evm0 (flipperUsrSlotFor I) ⟨0⟩
        exact assignStorageRef_storage_scalar
          (ty := .elem (.int uint256Int)) (loc := wordLoc (flipperUsrSlotFor I))
          (hbase := by simp [locals, flipperUsrStore, wardsRef])
          (her := her)
          (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
          (hloc := by
            funext evm
            simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
              flipperUsrEvaledRef, flipperUsrSlotFor])
          (hstore := hstore)
      have hblock := nonpayableRequireAssignStorageBlock
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0) (evm' := evm1)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rhs := .intLit 0) (ref := wardsRef (.var "usr")) (value := .int 0)
        (by simp [evm0, initState]; exact hwv)
        hguard (by simp [evalExpr?, pure]) hassign
      simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0, evm1, locals,
        flipperUsrStore] using ExecFuncBody.execBlockOK hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, flipperCallerWardsSlot, flipperSlotWord] using hauthEvm
    obtain ⟨_, _, hafterAuth⟩ := RD.flipperAuthCheckOk
      (code := flipperBytecode) (pc := ⟨5233⟩) (okPc := ⟨5315⟩) (key := key)
      (ret := ⟨323⟩) (R := [sel])
      (by simpa [key, flipperUsrKey] using hroutine)
      (by
        unfold flipperAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    have hmemAuth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
      twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    have hcanonKey : key.toNat < EVM.addressModulus := by
      dsimp [key, flipperUsrKey]
      rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
      exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
    obtain ⟨_, _, hretPc⟩ := RD.flipperMappingStoreZero
      (code := flipperBytecode) (pc := ⟨5315⟩) (key := key) (ret := ⟨323⟩) (R := [sel])
      hafterAuth
      (by
        unfold flipperMappingStoreZeroWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) hperm hmemAuth hcanonKey (by simp)
    have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
    have hret :
        RDret flipperBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨0⟩) ByteArray.empty := by
      simpa [slot] using RD.stop hretPc' (by native_decide) (by simp)
    have hcreated :
        (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨0⟩).1 = evm1.createdAccounts := by
      simp [evm1, evm0, initState, storageStore_createdAccounts]
    have haccounts :
        accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨0⟩).2
          evm1.accountMap := by
      simpa [evm1, evm0, initState, storageStore_accountMap, hslot] using
        accountMapEquiv_sstoreAccountMap I.codeOwner slot ⟨0⟩ hAccounts
    have henc : returnEquiv ByteArray.empty none denyTransition.returnType := by
      rw [show denyTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      hcreated haccounts henc
  · have hauthSolm : flipperSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals denyTransition.body .reverted := by
      have hguard := flipperAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (locals := locals) (by simp [locals, flipperUsrStore]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 0)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0, locals,
        flipperUsrStore] using ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, flipperCallerWardsSlot, flipperSlotWord] using hauthEvm
    have hrev := RD.flipperAuthCheckRevert
      (pc := ⟨5233⟩) (okPc := ⟨5315⟩) (key := key) (ret := ⟨323⟩) (R := [sel])
      (by simpa [key, flipperUsrKey] using hroutine)
      (by
        unfold flipperAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold flipperAuthCodecopyRevertTailWf flipperAuthTailPc
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDenyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨757⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨757⟩) (ret := ⟨323⟩)
    (decoded := ⟨779⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (flipperDecode_deny_none_short hsz4 hshort)

theorem flipperDenyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 5) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    flipperDispatchDeny hsel
  have hreach := flipperReachDenyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact flipperDenyBodyCoreOk hcode hwv hperm hsz36 hsize hdispatch
      (flipperDecode_deny_ok hsz36) hreach hAccounts
  · exact flipperDenyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flipper

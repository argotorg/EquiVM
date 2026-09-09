import Benchmarks.Dss.Cure.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cure

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

theorem cureDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 2)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes]
  decide +native

theorem cureDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (denyUsr I))) := by
  simpa [config, denyTransition, denyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem cureDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  simpa [config, denyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem cureReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 2)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨732⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x9c52a7f1⟩ :=
    cureSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨0x9c52a7f1⟩
      (by decide +native) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h54⟩ := cureReachHighUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; decide +native) (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨732⟩ 0 h54 (fun j hj => cureHighUpperArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

abbrev cureDenyEventTopic : UInt256 :=
  ⟨0x184450df2e323acec0ed3b5c7531b81f9b4cdef7914dfd4c0a4317416bb5251b⟩

theorem RD.cureDenyStoreZero {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3517⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨0⟩) k' C' := by
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hmaskLiteral' :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    exact hmaskLiteral
  have rdMasked := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov)]
  rw [hmaskLiteral'] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by
      simpa only [List.length_cons] using hov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw dup3 (by decide +native) (by
      simpa only [List.length_cons] using hov),
    raw swap1 (by decide +native) (by
      simpa only [List.length_cons] using hov)]
  obtain ⟨_, _, rdAfterStore⟩ := rdBeforeStore.sstore hperm (by decide +native)
    (by simp only [List.length_cons]; omega)
  have hread64' :
      (twoWordHashMem key ⟨0⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨0⟩ hmem hread64
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (twoWordHashMem key ⟨0⟩ mem).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩
        then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
          ((twoWordHashMem key ⟨0⟩ mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by
      rw [twoWordHashMem_size_96 key ⟨0⟩ hmem]
      decide +native)]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from rfl, hread64']
    decide +native
  have rdMload := rdAfterStore.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
    mem_cost hmload64 (by decide +native) (by evm_ov)
  have rdTopic := rdMload.pushConst cureDenyEventTopic
    (op := .PUSH32) (width := 32) (by decide) (by decide +native) (by evm_ov)
  have rdLogPrefix := evm_run rdTopic with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rdLogged := RD.cureLog2 0 (UInt256.ofNat 3) rdLogPrefix
    (by decide +native) hperm mem_cost (by decide +native) (by evm_ov)
  have rdPop := rdLogged.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rdPop.jump (by decide +native) hret (by evm_ov)⟩

theorem cureDenyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let sel := cureSelWord I
  let key := denyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := cureCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (denyUsr I))
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    cureDispatchDeny hsel
  have hreach := cureReachDenyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
          (transitionSignature denyTransition).paramTypes I.calldata =
            some ((∅ : Store).insert "usr" (.address (denyUsr I))) :=
      cureDecode_deny_ok hsz36
    have hslot : denySlotFor I = slot := by
      simp [slot, key, denySlotFor_eq]
    have hcallerWord : cureSlotWord callerSlot σ_evm I = cureSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have hliveWord : cureSlotWord ⟨1⟩ σ_evm I = cureSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
      (code := cureBytecode) (sel := sel) (entry := ⟨732⟩) (ret := ⟨484⟩)
      (decoded := ⟨754⟩) hreach
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by jump_dest) hsz36 hsize
    obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
      (code := cureBytecode) (decoded := ⟨754⟩) (ret := ⟨484⟩) (routine := ⟨3356⟩)
      (R := [sel]) hdecoded
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by jump_dest) (by simp)
    by_cases hauthEvm : cureSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : cureSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
        (code := cureBytecode) (pc := ⟨3356⟩) (okPc := ⟨3446⟩) (key := key)
        (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, denyKey] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | decide +native)
        hauthSolc (by jump_dest) (by simp)
      by_cases hliveEvm : cureSlotWord ⟨1⟩ σ_evm I = ⟨1⟩
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨1⟩ := by
          rw [← hliveWord]
          exact hliveEvm
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (denySlotFor I) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract evm0 locals denyTransition.body
              (.returned { contract := contract, locals := locals } evm1 none) := by
          have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hauthSolm
          have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hliveSolm
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
            exact assignStorageRef_storage_scalar
              (ty := .elem (.int uint256Int)) (loc := wordLoc (denySlotFor I))
              (hbase := by simp [locals, wardsRef])
              (her := her)
              (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
              (hloc := by
                funext evm
                simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
                  denyEvaledRef, denySlotFor])
              (hstore := hstore)
          have hblock :
              ExecBlock config { contract := contract, locals := locals } evm0
                [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                  .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                  .require (.binary .eq (.storage liveRef) (.intLit 1)),
                  .assign .storage (wardsRef (.var "usr")) (.intLit 0) ]
                (.ok { contract := contract, locals := locals } evm1) := by
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
            · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
            exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassign)
              ExecBlock.nil
          simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0, evm1] using
            ExecFuncBody.execBlockOK hblock
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ = ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
        obtain ⟨_, _, hstorePc⟩ := RD.cureLiveGuardOk
          (code := cureBytecode) (pc := ⟨3446⟩) (okPc := ⟨3517⟩) (key := key)
          (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | decide +native)
          hliveSolc (by jump_dest) (by simp)
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hcanonKey : key.toNat < EVM.addressModulus := by
          dsimp [key, denyKey]
          rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
          exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
        obtain ⟨_, _, hretPc⟩ := RD.cureDenyStoreZero
          (g := Sat256.ofUInt256 g) (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
          hstorePc (by jump_dest) hperm hmemAuth hread64 hcanonKey (by simp)
        have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
        have hret :
            RDret cureBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨0⟩) ByteArray.empty := by
          simpa [slot] using RD.stop hretPc' (by decide +native) (by simp)
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
          exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          hcreated haccounts henc
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I ≠ ⟨1⟩ := by
          intro hsolm
          exact hliveEvm (by rw [hliveWord, hsolm])
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody : ExecTransitionBody config contract evm0 locals denyTransition.body .reverted := by
          have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hauthSolm
          have hguardLive := cureLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hliveSolm
          have hblock :
              ExecBlock config { contract := contract, locals := locals } evm0
                [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                  .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                  .require (.binary .eq (.storage liveRef) (.intLit 1)),
                  .assign .storage (wardsRef (.var "usr")) (.intLit 0) ]
                .reverted := by
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
            · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
            exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
          simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0] using
            ExecFuncBody.execBlockRevert hblock
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ ≠ ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hrev := RD.cureLiveGuardRevert
          (code := cureBytecode) (pc := ⟨3446⟩) (okPc := ⟨3517⟩) (key := key)
          (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | decide +native)
          (by
            unfold solcErrorStringRevertTailWf cureLiveGuardTailPc cureNotLiveRawWord
            repeat' first | apply And.intro | decide +native)
          hliveSolc hmemAuth hread64 (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : cureSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals denyTransition.body .reverted := by
        have hguard := cureAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hblock := nonpayableSecondRequireReverts
          (cfg := config) (solm := { contract := contract, locals := locals })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest := [
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .assign .storage (wardsRef (.var "usr")) (.intLit 0)])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0] using
          ExecFuncBody.execBlockRevert hblock
      have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      have hrev := RD.cureAuthCheckRevert
        (code := cureBytecode) (pc := ⟨3356⟩) (okPc := ⟨3446⟩) (key := key)
        (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, denyKey] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | decide +native)
        (by
          unfold solcErrorStringRevertTailWf cureAuthTailPc cureNotAuthorizedRawWord
          repeat' first | apply And.intro | decide +native)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hlt :
        UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
      change I.calldata.size - 4 < 32
      omega
    have hrev := RD.solcExternalStaticArgsShortReverts
      (code := cureBytecode) (sel := sel) (entry := ⟨732⟩) (ret := ⟨484⟩)
      (decoded := ⟨754⟩) (need := ⟨32⟩) hreach
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) hlt
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (cureDecode_deny_none_short hsz4 (by omega))

end Benchmarks.Dss.Cure

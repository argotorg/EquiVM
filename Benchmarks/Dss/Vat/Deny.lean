import Benchmarks.Dss.Vat.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vat

/-! ## `deny(address)` -/

theorem vatDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (relyUsr I))) := by
  simpa [config, denyTransition, relyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem vatDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  simpa [config, denyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem vatDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 5)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes]
  native_decide

theorem vatReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 5)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1169⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x9c52a7f1⟩ :=
    vatSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨0x9c52a7f1⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms163Body 0 (by omega) ⟨1169⟩ hcode hwv hsz hsize
    hroot hhigh hhighlow heq0 htake (by jump_dest) (by native_decide)

@[reducible] def vatDenyStoreZeroWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.AND, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.DUP2, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p22 = some (.DUP2, .none)
  ∧ decode code p23 = some (.KECCAK256, .none)
  ∧ decode code p24 = some (.SSTORE, .none)
  ∧ decode code p25 = some (.JUMP, .none)

theorem RD.vatDenyStoreZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatDenyStoreZeroWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨0⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd25⟩
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonKey
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd19 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd20 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdOut⟩ := rdSlot.sstore hperm hd24 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd25 hret (by evm_ov)⟩

theorem vatDenyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "usr" (.address (relyUsr I))))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1169⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := relyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := vatCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (relyUsr I))
  have hslot : relySlotFor I = slot := by
    simp [slot, key, relySlotFor_eq]
  have hcallerWord : vatSlotWord callerSlot σ_evm I = vatSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1169⟩) (ret := ⟨524⟩)
    (decoded := ⟨1191⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨1191⟩) (ret := ⟨524⟩) (routine := ⟨5362⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  by_cases hauthEvm : vatSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : vatSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
    obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
      (code := vatBytecode) (pc := ⟨5362⟩) (okPc := ⟨5444⟩) (key := key)
      (ret := ⟨524⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold vatAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    by_cases hliveEvm : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩
    · have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
        rw [← hliveWord]
        exact hliveEvm
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (relySlotFor I) ⟨0⟩
      have hbody :
          ExecTransitionBody config contract evm0 locals denyTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hliveSolm
        have hassign :
            assignStorageRef? config { contract := contract, locals := locals } evm0
              .storage (wardsRef (.var "usr")) (.int 0) =
                .ok ({ contract := contract, locals := locals }, evm1) := by
          have her :
              evalStorageRef config { contract := contract, locals := locals } evm0
                (wardsRef (.var "usr")) = .ok (relyEvaledRef I) := by
            simp [evm0, relyEvaledRef, relyUsr, wardsRef, evalStorageRef,
              evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
              EvalResult.ofOption, EvalResult.bind, pure, bind, locals]
          have hstore :
              storageLocStore evm0 (wordLoc (relySlotFor I)) (.int 0) = some evm1 := by
            simpa [evm1] using vatStorageLocStore_uint256 evm0 (relySlotFor I) ⟨0⟩
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
        simpa [ExecTransitionBody, denyTransition, nonpayable, auth, requireLive, evm0, evm1] using
          ExecFuncBody.execBlockOK hblock
      have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
        simpa [vatSlotWord] using hliveEvm
      obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
        (code := vatBytecode) (pc := ⟨5444⟩) (okPc := ⟨5514⟩) (key := key)
        (ret := ⟨524⟩) (R := [sel]) hafterAuth
        (by
          unfold vatLiveGuardWf
          repeat' first | apply And.intro | native_decide)
        hliveSolc (by jump_dest) (by simp)
      have hmemAuth :
          (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hcanonKey : key.toNat < EVM.addressModulus := by
        dsimp [key, relyKey]
        rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
        exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
      obtain ⟨_, _, hretPc⟩ := RD.vatDenyStoreZero
        (code := vatBytecode) (pc := ⟨5514⟩) (key := key) (ret := ⟨524⟩) (R := [sel])
        hstorePc
        (by
          unfold vatDenyStoreZeroWf
          repeat' first | apply And.intro | native_decide)
        (by jump_dest) hperm hmemAuth hcanonKey (by simp)
      have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
      have hret :
          RDret vatBytecode (Sat256.ofUInt256 g)
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
    · have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hliveEvm (by rw [hliveWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals denyTransition.body .reverted := by
        have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := vatLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
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
        simpa [ExecTransitionBody, denyTransition, nonpayable, auth, requireLive, evm0] using
          ExecFuncBody.execBlockRevert hblock
      have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ ≠ ⟨1⟩ := by
        simpa [vatSlotWord] using hliveEvm
      have hmemAuth :
          (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hread64 :
          (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
          solcFreePtrMem_read64
      have hrev := RD.vatLiveGuardRevert
        (code := vatBytecode) (pc := ⟨5444⟩) (okPc := ⟨5514⟩) (key := key)
        (ret := ⟨524⟩) (R := [sel]) hafterAuth
        (by
          unfold vatLiveGuardWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold solcErrorStringRevertTailWf vatLiveGuardTailPc vatNotLiveRawWord
          repeat' first | apply And.intro | native_decide)
        hliveSolc hmemAuth hread64 (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : vatSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals denyTransition.body .reverted := by
      have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
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
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
    have hrev := RD.vatAuthCheckRevert
      (pc := ⟨5362⟩) (okPc := ⟨5444⟩) (key := key)
      (ret := ⟨524⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold vatAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold vatAuthRevertTailWf vatAuthTailPc
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatDenyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1169⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1169⟩) (ret := ⟨524⟩)
    (decoded := ⟨1191⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (vatDecode_deny_none_short hsz4 hshort)

theorem vatDenyBodyCore : VatBodyTheorem 5 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 5) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    vatDispatchDeny hsel
  have hreach := vatReachDenyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatDenyBodyCoreOk hcode hwv hperm hsz36 hsize hdispatch
      (vatDecode_deny_ok hsz36) hreach hAccounts
  · exact vatDenyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat

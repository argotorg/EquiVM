import Benchmarks.Dss.Vat.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vat

/-! ## `cage()` -/

theorem vatDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vatDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 1)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes]
  decide +native

theorem vatReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 1)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨855⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x69245009⟩ :=
    vatSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms272Body 0 (by omega) ⟨855⟩ hcode hwv hsz hsize
    hroot hlow hlowhigh heq0 htake (by jump_dest) (by decide +native)

@[reducible] def vatCageStoreLiveZeroWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨10⟩, 1))
  ∧ decode code p5 = some (.SSTORE, .none)
  ∧ decode code p6 = some (.JUMP, .none)

theorem RD.vatCageStoreLiveZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatCageStoreLiveZeroWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨10⟩ ⟨0⟩) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd5, hd6⟩
  have rdStore := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push1 ⟨10⟩ hd3 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdStore.sstore hperm hd5 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd6 hret (by evm_ov)⟩

theorem vatCageBodyCore : VatBodyTheorem 1 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 1) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vatDispatchCage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vatDecode_cage hsz4
  have hreach := vatReachCageBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  obtain ⟨_, _, hroutine⟩ := RD.solcGetterThunk
    (code := vatBytecode) (entry := ⟨855⟩) (returnPc := ⟨524⟩) (routine := ⟨2868⟩)
    hreach
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest)
  let callerSlot := vatCallerWardsSlot I
  have hcallerWord : vatSlotWord callerSlot σ_evm I = vatSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  by_cases hauthEvm : vatSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : vatSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨10⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody config contract evm0 ∅ cageTransition.body
          (.returned { contract := contract, locals := ∅ } evm1 none) := by
      have hguard := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := ∅)
        (by simp) hauthSolm
      have hassign :
          assignStorageRef? config { contract := contract, locals := ∅ } evm0
            .storage liveRef (.int 0) =
              .ok ({ contract := contract, locals := ∅ }, evm1) := by
        have her :
            evalStorageRef config { contract := contract, locals := ∅ } evm0 liveRef =
              .ok vatLiveEvaledRef := by
          simp [evm0, vatLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps,
            EvalResult.bind, pure, bind]
        have hstore :
            storageLocStore evm0 (wordLoc ⟨10⟩) (.int 0) = some evm1 := by
          simpa [evm1] using vatStorageLocStore_uint256 evm0 ⟨10⟩ ⟨0⟩
        exact assignStorageRef_storage_scalar
          (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨10⟩)
          (hbase := by simp [liveRef])
          (her := her)
          (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
          (hloc := by
            funext evm
            simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
              vatLiveEvaledRef])
          (hstore := hstore)
      have hblock :
          ExecBlock config { contract := contract, locals := ∅ } evm0
            [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
              .assign .storage liveRef (.intLit 0) ]
            (.ok { contract := contract, locals := ∅ } evm1) := by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
        exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassign)
          ExecBlock.nil
      simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0, evm1] using
        ExecFuncBody.execBlockOK hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
    obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
      (code := vatBytecode) (pc := ⟨2868⟩) (okPc := ⟨2950⟩) (key := ⟨524⟩)
      (ret := vatSelWord I) (R := [])
      (by simpa using hroutine)
      (by
        unfold vatAuthCheckWf
        repeat' first | apply And.intro | decide +native)
      hauthSolc (by jump_dest) (by simp)
    obtain ⟨_, _, hretPc⟩ := RD.vatCageStoreLiveZero
      (code := vatBytecode) (pc := ⟨2950⟩) (ret := ⟨524⟩) (R := [vatSelWord I])
      (by simpa using hafterAuth)
      (by
        unfold vatCageStoreLiveZeroWf
        repeat' first | apply And.intro | decide +native)
      (by jump_dest) hperm (by simp)
    have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
    have hret :
        RDret vatBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner σ_evm ⟨10⟩ ⟨0⟩) ByteArray.empty := by
      simpa using RD.stop hretPc' (by decide +native) (by simp)
    have hcreated :
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨10⟩ ⟨0⟩).1 = evm1.createdAccounts := by
      simp [evm1, evm0, initState, storageStore_createdAccounts]
    have haccounts :
        accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm ⟨10⟩ ⟨0⟩).2
          evm1.accountMap := by
      simpa [evm1, evm0, initState, storageStore_accountMap] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ ⟨0⟩ hAccounts
    have henc : returnEquiv ByteArray.empty none cageTransition.returnType := by
      rw [show cageTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      hcreated haccounts henc
  · have hauthSolm : vatSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 ∅ cageTransition.body .reverted := by
      have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := ∅)
        (by simp) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := ∅ })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [ .assign .storage liveRef (.intLit 0) ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
    have hrev := RD.vatAuthCheckRevert
      (pc := ⟨2868⟩) (okPc := ⟨2950⟩) (key := ⟨524⟩)
      (ret := vatSelWord I) (R := [])
      (by simpa using hroutine)
      (by
        unfold vatAuthCheckWf
        repeat' first | apply And.intro | decide +native)
      (by
        unfold vatAuthRevertTailWf vatAuthTailPc
        repeat' first | apply And.intro | decide +native)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vat

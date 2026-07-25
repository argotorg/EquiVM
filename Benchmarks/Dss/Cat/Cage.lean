import Benchmarks.Dss.Cat.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `cage()` — LOW-HIGH dispatch arm 2, entry ⟨483⟩

No arguments: `cageTransition.body = nonpayable ++ auth ++ [.assign .storage liveRef (.intLit 0)]`.
The entry `483 = JUMPDEST PUSH2 302 PUSH2 2833 JUMP` jumps straight to the auth-check at ⟨2833⟩
(stack `[302, sel]`); the auth-ok arm runs the SCALAR store `live := 0` at ⟨2922⟩ (slot 2, no
keccak) and returns via the void finalizer ⟨302⟩. -/

/-! ### Dispatch, ABI, reachability -/

theorem catDispatch_cage {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    dispatchMsg contract I.calldata = some cageTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition])
    (post := [clawTransition, denyTransition, fileAddressTransition, fileIlkFlipTransition,
      fileIlkUintTransition, fileUintTransition, ilksTransition, litterTransition, liveTransition,
      relyTransition, vatTransition, vowTransition, wardsTransition])
    (ti := cageTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x69, 0x24, 0x50, 0x09]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, cageSelectorBytes]
    exact hsel

theorem catDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem catReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨483⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : catSelWord I = ⟨1763987465⟩ :=
    catSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨1763987465⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc 2))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact catReachLowHighBody 2 (by omega) ⟨483⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

/-! ### Body core -/

theorem catCageBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := catCallerWardsSlot I
  let locals : Store := ∅
  have hcallerWord : catSlotWord callerSlot σ_evm I = catSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  -- Entry ⟨483⟩ jumps straight to the auth-check ⟨2833⟩ with stack `[302, sel]`.
  obtain ⟨_, _, hentry⟩ := hreach
  have hauthReach :
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩ (⟨302⟩ :: [sel])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) _ _ :=
    (((hentry.jumpdest (by native_decide) (by evm_ov)).push2 ⟨302⟩ (by native_decide) (by evm_ov)).push2
        ⟨2833⟩ (by native_decide) (by evm_ov)).jump (by native_decide) (by jump_dest) (by evm_ov)
  by_cases hauthEvm : catSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : catSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨2⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody config contract evm0 locals cageTransition.body
          (.returned { contract := contract, locals := locals } evm1 none) := by
      have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hassign :
          assignStorageRef? config { contract := contract, locals := locals } evm0
            .storage liveRef (.int 0) =
              .ok ({ contract := contract, locals := locals }, evm1) := by
        have her :
            evalStorageRef config { contract := contract, locals := locals } evm0
              liveRef = .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
          simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
        have hstore :
            storageLocStore evm0 (wordLoc ⟨2⟩) (.int 0) = some evm1 := by
          simpa [evm1] using storageLocStore_uint256 evm0 ⟨2⟩ ⟨0⟩
        exact assignStorageRef_storage_scalar
          (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨2⟩)
          (hbase := by simp [locals, liveRef])
          (her := her)
          (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
          (hloc := by
            funext evm
            simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
          (hstore := hstore)
      have hblock := nonpayableRequireAssignStorageBlock
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0) (evm' := evm1)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rhs := .intLit 0) (ref := liveRef) (value := .int 0)
        (by simp [evm0, initState]; exact hwv)
        hguard (by simp [evalExpr?, pure]) hassign
      simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0, evm1] using
        ExecFuncBody.execBlockOK hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    obtain ⟨_, _, hokPc⟩ := RD.catAuthCheckOk
      (code := catBytecode) (pc := ⟨2833⟩) (okPc := ⟨2922⟩) (key := ⟨302⟩)
      (ret := sel) (R := [])
      hauthReach
      (by
        unfold catAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    obtain ⟨_, _, hretPc⟩ := RD.catStoreLiveZero
      (code := catBytecode) (pc := ⟨2922⟩) (ret := ⟨302⟩) (R := [sel])
      hokPc
      (by
        unfold catStoreLiveZeroWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) hperm (by simp)
    have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
    have hret :
        RDret catBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ ⟨0⟩) ByteArray.empty :=
      RD.stop hretPc' (by native_decide) (by simp)
    have hcreated :
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ ⟨0⟩).1 = evm1.createdAccounts := by
      simp [evm1, evm0, initState, storageStore_createdAccounts]
    have haccounts :
        accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ ⟨0⟩).2
          evm1.accountMap := by
      simpa [evm1, evm0, initState, storageStore_accountMap] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ ⟨0⟩ hAccounts
    have henc : returnEquiv ByteArray.empty none cageTransition.returnType := by
      rw [show cageTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      hcreated haccounts henc
  · have hauthSolm : catSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals cageTransition.body .reverted := by
      have hguard := catAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.assign .storage liveRef (.intLit 0)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    have hrev := RD.catAuthCheckRevert
      (code := catBytecode) (pc := ⟨2833⟩) (okPc := ⟨2922⟩) (key := ⟨302⟩)
      (ret := sel) (R := [])
      hauthReach
      (by
        unfold catAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf catAuthTailPc catNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem catCageBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ (by native_decide) hsel
  exact catCageBodyCore hcode hwv hperm (catDispatch_cage hsel)
    (catDecode_cage hsz)
    (catReachCageBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end Benchmarks.Dss.Cat

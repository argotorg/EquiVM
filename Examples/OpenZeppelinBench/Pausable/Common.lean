import Examples.OpenZeppelinBench.Pausable.Trusted
import Examples.OpenZeppelinBench.Pausable.Storage
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Refinement
import Reasoning.Solc
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## PausableBench-wide dispatch, ABI, and return helpers -/

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev pausableSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- PausableBench's five selector arms begin at pc 30 (`unpause`). -/
abbrev pausableFirstArmPc : UInt256 := ⟨30⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop := (sel == I.calldata.extract 0 4) = true

/-- PausableBench function selectors, indexed in bytecode dispatch-arm order. -/
def pausableSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩  -- unpause()
  | 1 => ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩  -- paused()
  | 2 => ⟨#[0x84, 0x56, 0xcb, 0x59]⟩  -- pause()
  | 3 => ⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩  -- guardedWhenNotPaused()
  | _ => ⟨#[0xdd, 0xf7, 0x03, 0x09]⟩  -- guardedWhenPaused()

/-- All five selector arms decode as `DUP1; PUSH4; EQ; PUSH2; JUMPI`. -/
theorem pausableArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed pausableBenchBytecode
      (nthArmPc pausableBenchBytecode pausableFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### Shared source-level storage and ABI helpers -/

def pausableSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem pausableSenderWord_toNat (I : ExecutionEnv) :
    (pausableSenderWord I).toNat = I.source.val := by
  unfold pausableSenderWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem pausableSenderWord_canonical (I : ExecutionEnv) :
    (pausableSenderWord I).toNat < EVM.addressModulus := by
  rw [pausableSenderWord_toNat]
  exact I.source.isLt

noncomputable def pausableEventMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (pausableSenderWord I)).write 0 solcFreePtrMem 128 32

theorem pausableEventMem_size (I : ExecutionEnv) : (pausableEventMem I).size = 160 := by
  simpa [pausableEventMem, solcReturnMem] using solcReturnMem_size (pausableSenderWord I)

theorem pausableEventMem_read64 (I : ExecutionEnv) :
    (pausableEventMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [pausableEventMem, solcReturnMem] using solcReturnMem_read64 (pausableSenderWord I)

theorem pausableEventMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pausableEventMem I).size ∨
        (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((pausableEventMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      (⟨128⟩ : UInt256) := by
  exact mloadFreePtrValue (by rw [pausableEventMem_size]; decide) (by decide)
    (pausableEventMem_read64 I)

theorem pausableBoolReturnEncoding (w : UInt256) :
    encodeReturnValue? boolTy (wordToElem .bool (UInt256.land w ⟨255⟩)) =
      some (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (UInt256.land w ⟨255⟩)))) := by
  by_cases hval : (UInt256.land w ⟨255⟩).val = 0
  · have hz : UInt256.land w ⟨255⟩ = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    have hnorm : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by decide
    simpa [boolTy, wordToElem, hz, hnorm] using boolFalseReturnEncoding
  · have hz : UInt256.land w ⟨255⟩ ≠ ⟨0⟩ := by
      intro hx
      apply hval
      rw [hx]
    have hiz : UInt256.isZero (UInt256.land w ⟨255⟩) = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have hnorm : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by decide
    simpa [boolTy, wordToElem, hval, hiz, hnorm] using boolTrueReturnEncoding

theorem pausableEvalPausedFalse (evm : EVM.State) (locals : Store)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage pausedRef) =
      .ok (.bool false) := by
  have hstorageZero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ =
        ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hzero
  have her : evalStorageRef config { contract := contract, locals := locals } evm pausedRef =
      .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her) (hty := hty)
    (hloc := by rfl), pausableStorageLocLoad_bool_offset0_false evm ⟨0⟩ hstorageZero]

theorem pausableEvalPausedTrue (evm : EVM.State) (locals : Store)
    (hnz : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage pausedRef) =
      .ok (.bool true) := by
  have hstorageNz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠
        ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hnz
  have her : evalStorageRef config { contract := contract, locals := locals } evm pausedRef =
      .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her) (hty := hty)
    (hloc := by rfl), pausableStorageLocLoad_bool_offset0_true evm ⟨0⟩ hstorageNz]

theorem pausableEvalWhenNotPausedTrue (evm : EVM.State) (locals : Store)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pausableEvalPausedFalse evm locals hzero hlocals,
    evalUnaryOp?]
  rfl

theorem pausableEvalWhenNotPausedFalse (evm : EVM.State) (locals : Store)
    (hnz : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, pausableEvalPausedTrue evm locals hnz hlocals,
    evalUnaryOp?]
  rfl

/-- Arm `j`'s selector equality agrees with the calldata byte comparison. -/
theorem pausableArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat pausableBenchBytecode
          (nthArmPc pausableBenchBytecode pausableFirstArmPc j))
        (pausableSelWord I)
      = if (pausableSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

/-- Selector identification for the linear dispatcher. -/
theorem pausableMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (pausableSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat pausableBenchBytecode
          (nthArmPc pausableBenchBytecode pausableFirstArmPc j))
        (pausableSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat pausableBenchBytecode
          (nthArmPc pausableBenchBytecode pausableFirstArmPc i))
        (pausableSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = pausableSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [pausableArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [pausableArmEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- Standard solc prologue/guards/selector-load, then linear dispatch to a body entry. -/
theorem pausableReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi4 : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = pausableBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat pausableBenchBytecode
          (nthArmPc pausableBenchBytecode pausableFirstArmPc j))
        (pausableSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat pausableBenchBytecode
          (nthArmPc pausableBenchBytecode pausableFirstArmPc i))
        (pausableSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J pausableBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt pausableBenchBytecode
        (nthArmPc pausableBenchBytecode pausableFirstArmPc i) = bodyPC) :
    ∃ k C, RD pausableBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := pausableFirstArmPc) (bodyPC := bodyPC) (i := i)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => pausableArmsWellFormed j (le_trans hj hi4)) heq0 htake
    hjd hbody

/-! ## Shared dispatch and revert traces -/

theorem pausableDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [guardedWhenNotPausedTransition, guardedWhenPausedTransition, pauseTransition,
      pausedTransition, unpauseTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, guardedWhenNotPausedSelectorBytes]; rfl
    · rw [selectorOf, guardedWhenPausedSelectorBytes]; rfl
    · rw [selectorOf, pauseSelectorBytes]; rfl
    · rw [selectorOf, pausedSelectorBytes]; rfl
    · rw [selectorOf, unpauseSelectorBytes]; rfl) h

theorem pausableDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 5 → (pausableSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne
  intro t ht
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, guardedWhenNotPausedSelectorBytes]
    simpa [pausableSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, guardedWhenPausedSelectorBytes]
    simpa [pausableSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, pauseSelectorBytes]; simpa [pausableSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, pausedSelectorBytes]; simpa [pausableSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, unpauseSelectorBytes]; simpa [pausableSelBytes] using hnm 0 (by omega)

theorem pausableBodyReverts_nonPayable
    (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem pausableX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = pausableBenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt pausableBenchBytecode)
    (opC := solcGuardTgtOp pausableBenchBytecode)
    (wC := solcGuardTgtWidth pausableBenchBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pausableX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = pausableBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt pausableBenchBytecode)
    (opC := solcGuardTgtOp pausableBenchBytecode)
    (wC := solcGuardTgtWidth pausableBenchBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc pausableBenchBytecode)
    (rtgt := solcCalldataRevertTgt pausableBenchBytecode)
    (opR := solcCalldataRevertTgtOp pausableBenchBytecode)
    (wR := solcCalldataRevertTgtWidth pausableBenchBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem pausableX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = pausableBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 5 → (pausableSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat pausableBenchBytecode
          (nthArmPc pausableBenchBytecode pausableFirstArmPc j))
        (pausableSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [pausableArmEq I hsz j hj]
    rw [hnm j hj]
    rfl
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt pausableBenchBytecode)
    (opC := solcGuardTgtOp pausableBenchBytecode)
    (wC := solcGuardTgtWidth pausableBenchBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (bodyPc := solcDispatchBodyPc pausableBenchBytecode)
    (selLoadTgt := solcCalldataRevertTgt pausableBenchBytecode)
    (opR := solcCalldataRevertTgtOp pausableBenchBytecode)
    (wR := solcCalldataRevertTgtWidth pausableBenchBytecode)
    h1 hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ :=
    solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide) (by simp)
  have h4 : RD pausableBenchBytecode I g (initState cA gh bl σ σ₀ g A I)
      pausableFirstArmPc [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k3 C3 := by
    simpa [pausableFirstArmPc, pausableSelWord, solcFirstArmPcFromPrefix,
      solcSelectorWord, solcSelectorLoadPc, solcCalldataJumpiPc, solcCalldataRevertPushPc,
      solcDispatchBodyPc] using h3
  have h5 := h4
    |>.selectorArmNotTakenAuto (pausableArmsWellFormed 0 (by omega)) (heq0 0 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (pausableArmsWellFormed 1 (by omega)) (heq0 1 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (pausableArmsWellFormed 2 (by omega)) (heq0 2 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (pausableArmsWellFormed 3 (by omega)) (heq0 3 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (pausableArmsWellFormed 4 (by omega)) (heq0 4 (by omega))
        (by simp)
  have h85 : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨85⟩ [pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨k3 + 5 + 5 + 5 + 5 + 5, C3 + 22 + 22 + 22 + 22 + 22, ?_⟩
    simpa [pausableFirstArmPc, nthArmPc, selArmNextPc, armTgtWidth, armTgt,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h5
  obtain ⟨_, _, h85rd⟩ := h85
  exact evm_run h85rd with [
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem pausableNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (pausableX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (pausableBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem pausableShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (pausableX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (pausableDispatch_none_short hsz)

theorem pausableNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 5 → (pausableSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (pausableX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (pausableDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (pausableX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (pausableDispatch_none_short hshort)

end OpenZeppelinBench.Pausable

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory OpenZeppelinBench.Pausable

/-! ## PausableBench shared modifier routines -/

set_option maxHeartbeats 1000000 in
theorem RD.pausableReturnBoolTrue105 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD pausableBenchBytecode ee g s0 ⟨105⟩ (⟨1⟩ :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    RDret pausableBenchBytecode g s0 acc (UInt256.toByteArray ⟨1⟩) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem ⟨1⟩) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 ⟨1⟩) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨1⟩) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.pausableWhenNotPausedPass {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD pausableBenchBytecode ee g s0 ⟨332⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hzero : pausedWord σ ee = ⟨0⟩)
    (hret : (D_J pausableBenchBytecode 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD pausableBenchBytecode ee g s0 ret R mem aw rdata (cA, σ) k' C' := by
  have rd334 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd335₀⟩ := rd334.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd335⟩ : ∃ k' C',
      RD pausableBenchBytecode ee g s0 ⟨335⟩
        (pausedRawWord σ ee :: ret :: R) mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [pausedRawWord] using rd335₀⟩
  have rd339₀ := evm_run rd335 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (pausedRawWord σ ee) = pausedWord σ ee := by
    rw [Reasoning.Theory.u256_land_comm]
    rfl
  have rd339 := rd339₀
  rw [hmask, hzero] at rd339
  have rd157 := evm_run rd339 with [push2 ⟨157⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd157 with [jumpdest, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.pausableWhenNotPausedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD pausableBenchBytecode ee g s0 ⟨332⟩ (ret :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hnz : pausedWord σ ee ≠ ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev pausableBenchBytecode g s0 := by
  have rd334 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd335₀⟩ := rd334.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd335⟩ : ∃ k' C',
      RD pausableBenchBytecode ee g s0 ⟨335⟩
        (pausedRawWord σ ee :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [pausedRawWord] using rd335₀⟩
  have rd339₀ := evm_run rd335 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (pausedRawWord σ ee) = pausedWord σ ee := by
    rw [Reasoning.Theory.u256_land_comm]
    rfl
  have rd339 := rd339₀
  rw [hmask, isZero_eq_zero_of_ne hnz] at rd339
  have rd343 := evm_run rd339 with [push2 ⟨157⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0xd93c0665⟩ : UInt256) ⟨224⟩
  have rd356 := evm_run rd343 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0xd93c0665⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd366 := evm_run rd356 with [
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 errSel) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd366.rev 0 (by decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.pausableWhenPausedPass {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD pausableBenchBytecode ee g s0 ⟨367⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hnz : pausedWord σ ee ≠ ⟨0⟩)
    (hret : (D_J pausableBenchBytecode 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD pausableBenchBytecode ee g s0 ret R mem aw rdata (cA, σ) k' C' := by
  have rd369 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd370₀⟩ := rd369.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd370⟩ : ∃ k' C',
      RD pausableBenchBytecode ee g s0 ⟨370⟩
        (pausedRawWord σ ee :: ret :: R) mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [pausedRawWord] using rd370₀⟩
  have rd373₀ := evm_run rd370 with [push1 ⟨255⟩, and]
  have hmask : UInt256.land ⟨255⟩ (pausedRawWord σ ee) = pausedWord σ ee := by
    rw [Reasoning.Theory.u256_land_comm]
    rfl
  have rd373 := rd373₀
  rw [hmask] at rd373
  have rd157 := evm_run rd373 with [push2 ⟨157⟩, jumpiT hnz (by jump_dest)]
  exact ⟨_, _, evm_run rd157 with [jumpdest, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.pausableWhenPausedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD pausableBenchBytecode ee g s0 ⟨367⟩ (ret :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hzero : pausedWord σ ee = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev pausableBenchBytecode g s0 := by
  have rd369 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd370₀⟩ := rd369.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd370⟩ : ∃ k' C',
      RD pausableBenchBytecode ee g s0 ⟨370⟩
        (pausedRawWord σ ee :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [pausedRawWord] using rd370₀⟩
  have rd373₀ := evm_run rd370 with [push1 ⟨255⟩, and]
  have hmask : UInt256.land ⟨255⟩ (pausedRawWord σ ee) = pausedWord σ ee := by
    rw [Reasoning.Theory.u256_land_comm]
    rfl
  have rd373 := rd373₀
  rw [hmask, hzero] at rd373
  have rd377 := evm_run rd373 with [push2 ⟨157⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x8dfc202b⟩ : UInt256) ⟨224⟩
  have rd390 := evm_run rd377 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x8dfc202b⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd400 := evm_run rd390 with [
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 errSel) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd400.rev 0 (by decide) mem_cost (by evm_ov)

end Reasoning.Reach

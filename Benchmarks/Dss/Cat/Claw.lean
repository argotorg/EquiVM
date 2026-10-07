import Benchmarks.Dss.Cat.Storage
import Benchmarks.Dss.Cat.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `claw(uint256 rad)` — HIGH-HIGH dispatch arm 2, entry ⟨704⟩

`clawTransition.body = nonpayable ++ auth ++
  [.internalCall "sub" [.storage litterRef, .var "rad"] "litterNew",
   .assign .storage litterRef (.var "litterNew")]`.

Effect: `litter (slot 6) := sub(litter, rad) = litter - rad`, reverting if `rad > litter` or auth
fails.  Entry `704` decodes the single `uint256` arg (jump to `726`, routine `3259`), runs the
`wards[caller]` auth-check (ok arm `3348`), then the SLOAD-scalar-slot → `_sub @3762` → SSTORE-back
store, returning via the void finalizer `302`. -/

abbrev clawRad (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev clawLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "rad" (.int (Int.ofNat (clawRad I).toNat))

/-! ### Decode-to-routine bridge (`726 → 3259`) -/

theorem RD.catClawDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 ⟨726⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hwf : code = catBytecode)
    (hroutine : (D_J code 0).contains ⟨3259⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨3259⟩ (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd727 := h.jumpdest (by native_decide) (by evm_ov)
  have rd728 := rd727.pop (by native_decide) (by evm_ov)
  have rd729 := rd728.calldataload (by native_decide) (by evm_ov)
  have rd732 := rd729.push2 ⟨3259⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd732.jump (by native_decide) hroutine (by evm_ov)⟩

/-! ### `_sub(a, b)` routine (`@3762`): `[a, b, ret, R] → [b - a, R]` -/

theorem RD.catClawSubReturns {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    (h : RD catBytecode ee g s0 ⟨3762⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hle : a.toNat ≤ b.toNat)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ret ((UInt256.sub b a) :: R) mem aw rdata σ k' C' := by
  have hgt : UInt256.gt (UInt256.sub b a) b = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat hle]; omega)
  have rdPre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3756⟩ (by native_decide) (by evm_ov)]
  have rd3756 := rdPre.jumpiT (by native_decide) (by rw [hgt]; decide) (by jump_dest) (by evm_ov)
  have rdEnd := evm_run rd3756 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdEnd.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.catClawSubReverts {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    (h : RD catBytecode ee g s0 ⟨3762⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hunder : b.toNat < a.toNat)
    (hov : R.length + 6 ≤ 1024) :
    RDrev catBytecode g s0 := by
  have haLt : a.toNat < UInt256.size := a.val.isLt
  have hgt : UInt256.gt (UInt256.sub b a) b = ⟨1⟩ :=
    ugt_one (by rw [usub_toNat_underflow hunder]; omega)
  have rdPre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3756⟩ (by native_decide) (by evm_ov)]
  have rdRev := rdPre.jumpiNT (by native_decide) (by rw [hgt]; decide) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdRev
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

/-! ### Store routine (`3348 → 302`): SLOAD litter, `_sub rad`, SSTORE back -/

theorem RD.catClawStoreLitterSplit {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rad ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : ℕ}
    (h : RD catBytecode ee g s0 ⟨3348⟩ (rad :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hle : rad.toNat ≤ (solcSlotWord σ ee ⟨6⟩).toNat)
    (hov : R.length + 8 ≤ 1024) :
    (ee.perm = true ∧
      ∃ k' C', RD catBytecode ee g s0 ret R mem aw rdata
        (sstoreAccountMap ee.codeOwner σ ⟨6⟩ (UInt256.sub (solcSlotWord σ ee ⟨6⟩) rad)) k' C') ∨
      (ee.perm = false ∧ RDstatic catBytecode g s0) := by
  have rd3349 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3352 := rd3349.push2 ⟨3360⟩ (by native_decide) (by evm_ov)
  have rd3354 := rd3352.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3355⟩ := rd3354.sload (by native_decide) (by evm_ov)
  have rd3356 := rd3355.dup3 (by native_decide) (by evm_ov)
  have rd3359 := rd3356.push2 ⟨3762⟩ (by native_decide) (by evm_ov)
  have rd3762 := rd3359.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3360⟩ := RD.catClawSubReturns rd3762 hle (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd3360jd := rd3360.jumpdest (by native_decide) (by evm_ov)
  have rd3361 := rd3360jd.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have hstoreDec : decode catBytecode ⟨3363⟩ = some (.SSTORE, none) := by
    native_decide
  by_cases hperm : ee.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd3361.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd3364⟩ := rd3361.sstore hperm hstoreDec
    (by simp only [List.length_cons]; omega)
  have rd3365 := rd3364.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3365.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.catClawStoreLitterRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rad ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : ℕ}
    (h : RD catBytecode ee g s0 ⟨3348⟩ (rad :: ret :: R) mem aw rdata σ k C)
    (hunder : (solcSlotWord σ ee ⟨6⟩).toNat < rad.toNat)
    (hov : R.length + 8 ≤ 1024) :
    RDrev catBytecode g s0 := by
  have rd3349 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3352 := rd3349.push2 ⟨3360⟩ (by native_decide) (by evm_ov)
  have rd3354 := rd3352.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3355⟩ := rd3354.sload (by native_decide) (by evm_ov)
  have rd3356 := rd3355.dup3 (by native_decide) (by evm_ov)
  have rd3359 := rd3356.push2 ⟨3762⟩ (by native_decide) (by evm_ov)
  have rd3762 := rd3359.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.catClawSubReverts rd3762 hunder (by simp only [List.length_cons]; omega)

/-! ### Dispatch, ABI, reachability -/

theorem catDispatch_claw {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩) :
    dispatchMsg contract I.calldata = some clawTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition])
    (post := [denyTransition, fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition,
      fileUintTransition, ilksTransition, litterTransition, liveTransition, relyTransition,
      vatTransition, vowTransition, wardsTransition])
    (ti := clawTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, clawSelectorBytes]
    exact hsel

theorem catDecode_claw_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (clawTransition.params.map Param.name)
      (transitionSignature clawTransition).paramTypes I.calldata = some (clawLocals I) := by
  simpa [config, clawTransition, clawRad, clawLocals, uint256] using
    (decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "rad") hsz36)

theorem catDecode_claw_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (clawTransition.params.map Param.name)
      (transitionSignature clawTransition).paramTypes I.calldata = none := by
  simpa [config, clawTransition, uint256] using
    (decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "rad") hsz4 hshort)

theorem catReachClawBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩) :
    ∃ k C, RD catBytecode I g (initState σ σ₀ g A I)
        ⟨704⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : catSelWord I = ⟨3865913243⟩ :=
    catSelWord_eq_of_beq I hsz 0xe6 0x6d 0x27 0x9b ⟨3865913243⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc 2))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact catReachHighHighBody 2 (by omega) ⟨704⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

/-! ### Body core -/

theorem catClawBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some clawTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (clawTransition.params.map Param.name)
        (transitionSignature clawTransition).paramTypes I.calldata = some (clawLocals I))
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨704⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let callerSlot := catCallerWardsSlot I
  have hcallerWord : solcSlotWordAt callerSlot σ I = solcSlotWordAt callerSlot σ I :=
    rfl
  have hword : solcSlotWord σ I ⟨6⟩ = solcSlotWord σ I ⟨6⟩ :=
    rfl
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  -- Bridge entry ⟨704⟩ → decoded ⟨726⟩ → routine ⟨3259⟩.
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨704⟩) (ret := ⟨302⟩)
    (decoded := ⟨726⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.catClawDecodeToRoutine
    (code := catBytecode) (ret := ⟨302⟩) (R := [sel]) hdecoded rfl (by jump_dest) (by simp)
  by_cases hauthEvm : solcSlotWordAt callerSlot σ I = ⟨1⟩
  · -- AUTH OK.
    have hauthSolm : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
      exact hauthEvm
    have hauthSolc : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, solcSlotWordAt] using hauthEvm
    obtain ⟨_, _, hokPc⟩ := RD.solcAuthCheckOk
      (code := catBytecode) (pc := ⟨3259⟩) (okPc := ⟨3348⟩) (key := clawRad I)
      (ret := ⟨302⟩) (R := [sel])
      (by simpa [clawRad] using hroutine)
      (by
        unfold solcAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    -- Shared Solm-side prologue facts.
    have hcv := evalCallvalueEq_true (cfg := config)
      (solm := { contract := contract, locals := clawLocals I }) (evm := evm0)
      (by simp [evm0, initState]; exact hwv)
    have hguard := catAuthGuardEval_true
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (locals := clawLocals I) (by simp [clawLocals]) hauthSolm
    have hlitterRef :
        evalStorageRef config { contract := contract, locals := clawLocals I } evm0 litterRef =
          .ok ({ base := "litter", steps := [] } : EvaledStorageRef) := by
      simp [litterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    have hlitterExpr :
        evalExpr? config { contract := contract, locals := clawLocals I } evm0 (.storage litterRef) =
          .ok (.int (Int.ofNat (solcSlotWord σ I ⟨6⟩).toNat)) := by
      rw [evalExpr_storage_scalar (hbackend := rfl) (t := .int uint256Int) (loc := wordLoc ⟨6⟩)
        (hbase := by simp [clawLocals, litterRef])
        (her := hlitterRef)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by
          simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw])]
      rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
      simp [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord]
    have hradExpr :
        evalExpr? config { contract := contract, locals := clawLocals I } evm0 (.var "rad") =
          .ok (.int (Int.ofNat (clawRad I).toNat)) :=
      evalExpr_varUInt256 (by rw [clawLocals, store_get_self])
    have hargs :
        evalExprs? config { contract := contract, locals := clawLocals I } evm0
          [.storage litterRef, .var "rad"] =
            .ok [.int (Int.ofNat (solcSlotWord σ I ⟨6⟩).toNat),
              .int (Int.ofNat (clawRad I).toNat)] := by
      simp [evalExprs?, hlitterExpr, hradExpr, EvalResult.bind, bind, pure]
    have hbind :
        bindParams? subFunction.params
            [.int (Int.ofNat (solcSlotWord σ I ⟨6⟩).toNat),
              .int (Int.ofNat (clawRad I).toNat)] =
          some (uintBinaryLocals (solcSlotWord σ I ⟨6⟩) (clawRad I)) := by
      simp [subFunction, uint256, bindParams?, uintBinaryLocals]
    by_cases hle : (clawRad I).toNat ≤ (solcSlotWord σ I ⟨6⟩).toNat
    · -- `rad ≤ litter`: success.
      have hstoreSplit := RD.catClawStoreLitterSplit
        (ret := ⟨302⟩) (R := [sel]) hokPc (by jump_dest)
        (by rw [hword]; exact hle) (by simp)
      let diff := UInt256.sub (solcSlotWord σ I ⟨6⟩) (clawRad I)
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ diff
      have hbodySplit :
          ExecTransitionBody config contract evm0 (clawLocals I) clawTransition.body
            (.returned
              (resumeAfterInternalCall { contract := contract, locals := clawLocals I } "litterNew"
                (some [.int (Int.ofNat diff.toNat)])) evm1 none) ∧
          (I.perm = false →
            ExecTransitionBody config contract evm0 (clawLocals I) clawTransition.body
              .staticViolation) := by
        have hsubBody := execSubFunctionReturn evm0
          (x := solcSlotWord σ I ⟨6⟩) (y := clawRad I) (diff := diff) rfl hle
        have hcall := internalCallFunctionReturn
          (cfg := config) (caller := { contract := contract, locals := clawLocals I })
          (evm := evm0) (calleeEvm := evm0) (name := "sub") (retVar := "litterNew")
          (args := [.storage litterRef, .var "rad"])
          (argVals := [.int (Int.ofNat (solcSlotWord σ I ⟨6⟩).toNat),
            .int (Int.ofNat (clawRad I).toNat)])
          (callee := subFunction)
          (locals := uintBinaryLocals (solcSlotWord σ I ⟨6⟩) (clawRad I))
          (calleeSolm :=
            { contract := contract,
              locals := uintBinaryLocalsZ (solcSlotWord σ I ⟨6⟩) (clawRad I) diff })
          (value := some [.int (Int.ofNat diff.toNat)])
          hargs (by rfl) hbind hsubBody
        have hlitterNew :
            evalExpr? config
              (resumeAfterInternalCall { contract := contract, locals := clawLocals I } "litterNew"
                (some [.int (Int.ofNat diff.toNat)])) evm0 (.var "litterNew") =
              .ok (.int (Int.ofNat diff.toNat)) :=
          evalExpr_varUInt256 (by
            simp [collapseReturns])
        have hassign :
            assignStorageRef? config
              (resumeAfterInternalCall { contract := contract, locals := clawLocals I } "litterNew"
                (some [.int (Int.ofNat diff.toNat)])) evm0 .storage litterRef
              (.int (Int.ofNat diff.toNat)) =
                .ok (resumeAfterInternalCall { contract := contract, locals := clawLocals I }
                  "litterNew" (some [.int (Int.ofNat diff.toNat)]), evm1) := by
          have hstore :
              storageLocStore evm0 (wordLoc ⟨6⟩) (.int (Int.ofNat diff.toNat)) = some evm1 := by
            simpa [evm1] using storageLocStore_uint256 evm0 ⟨6⟩ diff
          have hassignRef :
              evalStorageRef config
                (resumeAfterInternalCall { contract := contract, locals := clawLocals I } "litterNew"
                  (some [.int (Int.ofNat diff.toNat)])) evm0 litterRef =
                .ok ({ base := "litter", steps := [] } : EvaledStorageRef) := by
            simp [litterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
          exact assignStorageRef_storage_scalar (hbackend := rfl)
            (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩) (hleaf := by first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
            (hbase := by simp [resumeAfterInternalCall, collapseReturns, clawLocals, litterRef])
            (her := hassignRef)
            (hty := by
              simp [storageTypeAt?, resumeAfterInternalCall, contract, storageDecls, uint256St])
            (hloc := by
              simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw])
            (hstore := hstore)
        have hprefix : ∀ r,
            ExecStmt config
              (resumeAfterInternalCall { contract := contract, locals := clawLocals I }
                "litterNew" (some [.int (Int.ofNat diff.toNat)])) evm0
              (.assign .storage litterRef (.var "litterNew")) r →
            ExecBlock config { contract := contract, locals := clawLocals I } evm0
              clawTransition.body r := by
          intro r h
          refine ExecBlock.consNormal (ExecStmt.requireTrue hcv) ?_
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
          refine ExecBlock.consNormal hcall ?_
          exact execBlock_singleton h
        refine ⟨?_, fun hperm ↦ ?_⟩
        · exact ExecFuncBody.execBlockOK (hprefix _ (ExecStmt.assign hlitterNew hassign))
        · exact ExecFuncBody.execBlockStatic (hprefix _ (ExecStmt.assignStatic hlitterNew hassign
            (by simp [evm0, initState]; exact hperm)))
      rcases hstoreSplit with ⟨_, _, _, hretPc⟩ | ⟨hperm, hstatic⟩
      swap
      · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode (hbodySplit.2 hperm)
      have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
      have hret :
          RDret catBytecode (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (sstoreAccountMap I.codeOwner σ ⟨6⟩
              (UInt256.sub (solcSlotWord σ I ⟨6⟩) (clawRad I))) ByteArray.empty :=
        RD.stop hretPc' (by native_decide) (by simp)
      have haccounts :
          sstoreAccountMap I.codeOwner σ ⟨6⟩
            (UInt256.sub (solcSlotWord σ I ⟨6⟩) (clawRad I)) = evm1.accountMap := by
        simp [evm1, evm0, initState, storageStore_accountMap, diff, hword]
      have henc : returnEquiv ByteArray.empty none clawTransition.returnType := by
        rw [show clawTransition.returnType = [] by rfl]
        exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
      exact hret.reEquivExecutionGen hcode hdispatch hdecode hbodySplit.1
        haccounts henc
    · -- `rad > litter`: sub underflows, revert.
      replace hle := Nat.not_le.mp hle
      have hrev := RD.catClawStoreLitterRevert
        (ret := ⟨302⟩) (R := [sel]) hokPc (by rw [hword]; exact hle) (by simp)
      have hbody :
          ExecTransitionBody config contract evm0 (clawLocals I) clawTransition.body .reverted := by
        have hsubRev := execSubFunctionRevert evm0
          (x := solcSlotWord σ I ⟨6⟩) (y := clawRad I) hle
        have hcallRev := internalCallFunctionRevert
          (cfg := config) (caller := { contract := contract, locals := clawLocals I })
          (evm := evm0) (name := "sub") (retVar := "litterNew")
          (args := [.storage litterRef, .var "rad"])
          (argVals := [.int (Int.ofNat (solcSlotWord σ I ⟨6⟩).toNat),
            .int (Int.ofNat (clawRad I).toNat)])
          (callee := subFunction)
          (locals := uintBinaryLocals (solcSlotWord σ I ⟨6⟩) (clawRad I))
          hargs (by rfl) hbind hsubRev
        have hblock :
            ExecBlock config { contract := contract, locals := clawLocals I } evm0
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                .internalCall "sub" [.storage litterRef, .var "rad"] "litterNew",
                .assign .storage litterRef (.var "litterNew") ]
              .reverted := by
          refine ExecBlock.consNormal (ExecStmt.requireTrue hcv) ?_
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
          exact ExecBlock.consRevert hcallRev
        simpa [ExecTransitionBody, clawTransition, nonpayable, auth] using
          ExecFuncBody.execBlockRevert hblock
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · -- AUTH FAIL.
    have hauthSolm : solcSlotWordAt callerSlot σ I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    have hauthSolc : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, solcSlotWordAt] using hauthEvm
    have hbody :
        ExecTransitionBody config contract evm0 (clawLocals I) clawTransition.body .reverted := by
      have hguard := catAuthGuardEval_false
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := clawLocals I)
        (by simp [clawLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := clawLocals I })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.internalCall "sub" [.storage litterRef, .var "rad"] "litterNew",
          .assign .storage litterRef (.var "litterNew")])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, clawTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hrev := RD.catAuthCheckRevert
      (code := catBytecode) (pc := ⟨3259⟩) (okPc := ⟨3348⟩) (key := clawRad I)
      (ret := ⟨302⟩) (R := [sel])
      (by simpa [clawRad] using hroutine)
      (by
        unfold solcAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf solcAuthTailPc catNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem catClawShort {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hreach :=
    catReachClawBody (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := catBytecode) (sel := catSelWord I) (entry := ⟨704⟩) (ret := ⟨302⟩)
    (decoded := ⟨726⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (catDispatch_claw hsel)
    (catDecode_claw_none_short hsz4 hshort)

theorem catClawBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩ (by native_decide) hsel
  by_cases hshort : I.calldata.size < 36
  · exact catClawShort hcode hsize hwv hsz hshort hsel
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    exact catClawBodyCore hcode hwv hsz36 hsize (catDispatch_claw hsel)
      (catDecode_claw_ok hsz36)
      (catReachClawBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

end Benchmarks.Dss.Cat

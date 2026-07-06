import Benchmarks.Dss.Pot.Rely
import Benchmarks.Dss.Pot.Arith

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## `cage()` — auth writer, `live = 0; dsr = ONE` (scalars slot 8, slot 3). Group @114 arm 1.

No parameters (empty decode), and two scalar stores (not a mapping store). Reuses the shared
`wards[caller] == 1` auth reasoning from `Rely.lean`. -/

/-- Post-state: `live(8) := 0` then `dsr(3) := ONE`. -/
abbrev cagePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩)
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩).executionEnv.codeOwner
    ⟨3⟩ potRay

theorem potDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-! ### Solm-side auth evaluation (empty locals) -/

theorem evalStorageRef_cage_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := (∅ : Store) } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_cage_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [wardsRef])
      (her := evalStorageRef_cage_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using potStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_cage_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simp [wardsRef])
      (her := evalStorageRef_cage_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact potStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

/-! ### Solm-side scalar stores -/

theorem evalStorageRef_cage_live (evm : EVM.State) (_I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := (∅ : Store) } evm liveRef
      = .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_cage_dsr (evm : EVM.State) (_I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := (∅ : Store) } evm dsrRef
      = .ok ({ base := "dsr", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, dsrRef, EvalResult.bind, pure, bind]

theorem cageLiveAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := (∅ : Store) } evm
      .storage liveRef (.int 0) =
        .ok ({ contract := contract, locals := (∅ : Store) },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp)
      (her := evalStorageRef_cage_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using potStorageLocStore_uint256 evm ⟨8⟩ ⟨0⟩

theorem cageDsrAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := (∅ : Store) } evm
      .storage dsrRef (.int one) =
        .ok ({ contract := contract, locals := (∅ : Store) },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ potRay) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨3⟩)
      (hbase := by simp)
      (her := evalStorageRef_cage_dsr evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  rw [one_eq_potRay_toNat]
  exact potStorageLocStore_uint256 evm ⟨3⟩ potRay

theorem potCageBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody config contract evm ∅ cageTransition.body
      (.returned { contract := contract, locals := (∅ : Store) } (cagePostState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  show ExecBlock config { contract := contract, locals := (∅ : Store) } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
      .assign .storage liveRef (.intLit 0),
      .assign .storage dsrRef (.intLit one) ]
    (.ok { contract := contract, locals := (∅ : Store) } (cagePostState evm))
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_cage_auth_true evm I hsrc hauth)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (cageLiveAssign evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (cageDsrAssign _ I)) ExecBlock.nil

theorem potCageBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm ∅ cageTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage liveRef (.intLit 0), .assign .storage dsrRef (.intLit one)])
      hwv
      (evalExpr_cage_auth_false evm I hsrc hauth)

/-! ### EVM-side trace -/

theorem potReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 1)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨500⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x69245009⟩ :=
    potSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j; rw [hword]; native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc 1))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG114Body 1 (by omega) ⟨500⟩ hcode hwv hsz hsize hroot h43 heq0 htake
    (by jump_dest) (by native_decide)

/-- Entry `@500`: no decode — push return addr `301`, push logic `1490`, jump. -/
theorem potCageX_entered {cA σ I} {g : Sat256} {s0 : State} {sel : UInt256}
    (hreach : ∃ k C, RD potBytecode I g s0 ⟨500⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1490⟩ [⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k, C, h⟩ := hreach
  have rd501 := h.jumpdest (by native_decide) (by evm_ov)
  have rd504 := rd501.push2 ⟨301⟩ (by native_decide) (by evm_ov)
  have rd507 := rd504.push2 ⟨1490⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd507.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem potCageX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨1490⟩
      [⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1579⟩
      [⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1496pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1497 := rd1496pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1501pre := evm_run rd1497 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1502 := rd1501pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1505pre := evm_run rd1502 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1506 := rd1505pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1507, C1507, rd1507raw⟩ := rd1506.sload (by native_decide) (by evm_ov)
  have rd1507 : RD potBytecode I g s0 ⟨1507⟩
      (relyAuthWord σ I :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1507 C1507 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1507raw
  have rd1510pre := evm_run rd1507 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1510pre
  have rd1513 := rd1510pre.pushConst (⟨1579⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1513.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem potCageX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨1490⟩
      [⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1496pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1497 := rd1496pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1501pre := evm_run rd1497 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1502 := rd1501pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1505pre := evm_run rd1502 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1506 := rd1505pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1507, C1507, rd1507raw⟩ := rd1506.sload (by native_decide) (by evm_ov)
  have rd1507 : RD potBytecode I g s0 ⟨1507⟩
      (relyAuthWord σ I :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1507 C1507 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1507raw
  have rd1510pre := evm_run rd1507 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1510pre
  have rd1513 := rd1510pre.pushConst (⟨1579⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1514 := rd1513.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1514⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x141bdd0bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x506f742f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd1514
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem potCageX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD potBytecode I g s0 ⟨1579⟩
      [⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret potBytecode g s0
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨8⟩ ⟨0⟩) ⟨3⟩ potRay)
      ByteArray.empty := by
  have rd1580 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1582 := rd1580.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1584 := rd1582.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1585⟩ := rd1584.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1598 := rd1585.pushConst potRay (width := 12) (op := .PUSH12)
    (by decide) (by native_decide) (by evm_ov)
  have rd1600 := rd1598.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1601⟩ := rd1600.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := rd1601.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd302 := rd301.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd302 (by native_decide) (by evm_ov)

theorem potX_cage_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨500⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret potBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨8⟩ ⟨0⟩) ⟨3⟩ potRay)
      ByteArray.empty := by
  obtain ⟨_, _, rd1490⟩ := potCageX_entered hreach
  obtain ⟨_, _, rd1579⟩ := potCageX_authorized (I := I) hauth rd1490
  exact potCageX_storeAuthorized hperm rd1579

theorem potX_cage_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨500⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1490⟩ := potCageX_entered hreach
  exact potCageX_unauthorized (I := I) hauth rd1490

theorem potCageBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨500⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body
        (.returned { contract := contract, locals := (∅ : Store) } (cagePostState evmSolm) none) := by
    simpa [evmSolm, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potCageBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (potX_cage_ok (g := Sat256.ofUInt256 g) hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [cagePostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [cagePostState, evmSolm, initState, storageStore_accountMap,
          storageStore_executionEnv] using
          accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner ⟨8⟩ ⟨0⟩ ⟨3⟩ potRay
            hAccounts)
      (by
        simpa [cageTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem potCageBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨500⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potCageBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (potX_cage_unauthorized (g := Sat256.ofUInt256 g) hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potCageBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (potSelBytes 1) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    potDispatchCage hsel
  have hreach := potReachCageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
  · exact potCageBodyCoreOk hcode hsize _hperm hwv hauth hdispatch
      (potDecode_cage hsz4) hreach hAccounts
  · exact potCageBodyCoreUnauthorized hcode hsize hwv hauth hdispatch
      (potDecode_cage hsz4) hreach hAccounts

end Benchmarks.Dss.Pot

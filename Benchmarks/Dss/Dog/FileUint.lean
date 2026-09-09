import Benchmarks.Dss.Dog.Dispatch
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Dog

/-! ## `file(bytes32,uint256)` -/

abbrev fileUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileUintHoleBytes : List UInt8 :=
  [72, 111, 108, 101] ++ zeroPad28

abbrev fileUintLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileUintWhat I))).insert
    "data" (.int (Int.ofNat (fileUintData I).toNat))

abbrev dogFileUintLogTopic : UInt256 :=
  ⟨105627225169409785158710363763375725481095598661489361122320324215644262229191⟩

theorem fileUintHoleBytes_length : fileUintHoleBytes.length = 32 := by
  decide +native

theorem fileUintWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileUintWhat I).length = 32 := by
  simp [fileUintWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileUintWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileUintWhat I) = calldataWord I.calldata 4 := by
  simpa [fileUintWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileUintWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileUintWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileUintWhatWord_eq (I := I) hsz36).symm

theorem fileUintWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileUintWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileUintWhat I)
    (fileUintWhat_length (I := I) hsz36)
  rw [fileUintWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileUintWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileUintWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem dogDecode_fileUint_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata =
        some (fileUintLocals I) := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileUintLocals, fileUintWhat, fileUintData, abiBytes32, abiBytes32Width, abiUInt256] using
    dogDecodeCalldataWithMode_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68

theorem dogDecode_fileUint_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    dogDecodeCalldataWithMode_legacyBytes32_uint256_none_short (cd := I.calldata)
      (x := "what") (y := "data") hsz4 hshort

theorem fileUintLocals_get_what (I : ExecutionEnv) :
    (fileUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileUintWhat I)) := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileUintLocals_get_data (I : ExecutionEnv) :
    (fileUintLocals I).get? "data" =
      some (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [fileUintLocals, store_get_self]

theorem evalExpr_fileUintData {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileUintData I).toNat))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileUintWhatEq_true {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I = bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileUintWhatEq_false {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I ≠ bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileUintHoleStorage (v : DogImmutables) (evm : EVM.State)
    {locals : Store} (data : UInt256) (hbase : locals.get? "Hole" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ data
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage HoleRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef (config v) { contract := contract v, locals := locals } evm HoleRef =
        .ok { base := "Hole", steps := [] } := by
    simp [HoleRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨4⟩) (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨4⟩ data
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨4⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem fileUintHoleSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintHoleBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩ (fileUintData I)
    ExecTransitionBody (config v) (contract v) evm0 locals fileUintTransition.body
      (.returned { contract := contract v, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") HoleParamLit) = .ok (.bool true) := by
    simpa [HoleParamLit, fileUintHoleBytes] using
      (evalExpr_fileUintWhatEq_true (v := v) (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintHoleBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileUintData (v := v) (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage HoleRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract v, locals := locals }, evm1) := by
    simpa [evm1] using
      (assign_fileUintHoleStorage v evm0 (locals := locals) (fileUintData I)
        (by simp [locals, fileUintLocals]))
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [.assign .storage HoleRef (.var "data")]
        (.ok { contract := contract v, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileUintTransition.body (.ok { contract := contract v, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileUintUnrecognizedSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotHole : fileUintWhat I ≠ fileUintHoleBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") HoleParamLit) = .ok (.bool false) := by
    simpa [HoleParamLit, fileUintHoleBytes] using
      (evalExpr_fileUintWhatEq_false (v := v) (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintHoleBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotHole)
  have hreqFalse :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileUintTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem dogReachFileUintBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 8)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨315⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0x29ae8114⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by decide +native) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootTgt : armTgt code (⟨32⟩ : UInt256) = ⟨162⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hlowTgt : armTgt code (⟨163⟩ : UInt256) = ⟨222⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h162 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨162⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [hrootTgt] using
      RD.selectorSplitTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot
        (by
          rw [hrootTgt]
          exact dogPatchedDJumpPrefix1405 ⟨162⟩ hpatch (by decide +native))
        (by simp)
  have h163 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨163⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa using
      h162.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by simp only [List.length_singleton]; omega)
  have hlow :
      UInt256.gt (armSelNat code (⟨163⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨163⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h222 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨222⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [hlowTgt] using
      RD.selectorSplitTakenAuto h163 (dogLowSplitWellFormed hpatch) hlow
        (by
          rw [hlowTgt]
          exact dogPatchedDJumpPrefix1405 ⟨222⟩ hpatch (by decide +native))
        (by simp)
  have h223 := h222.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
      decide +native)
    (by simp only [List.length_singleton]; omega)
  have hfileIlkUint : UInt256.eq (dogSelectorWord 7) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hfileUint : UInt256.eq (dogSelectorWord 8) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have h234 := by
    simpa [selArmNextPc] using
      h223.selectorArmNotTaken (selNat := dogSelectorWord 7) (tgt := (⟨272⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hfileIlkUint
        (by simp)
  have h315 := by
    simpa using
      h234.selectorArmTaken (selNat := dogSelectorWord 8) (tgt := (⟨315⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hfileUint
        (dogPatchedDJumpPrefix1405 ⟨315⟩ hpatch (by decide +native))
        (by simp)
  exact ⟨_, _, h315⟩

theorem RD.dogFileUintDecodeToRoutine {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret de sel : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨337⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J code 0).contains ⟨1236⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1236⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd338 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd339 := rd338.pop
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd340 := rd339.dup1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd341 := rd340.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd342 := rd341.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd344 := rd342.push1 ⟨32⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd345 := rd344.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd346 := rd345.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd349 := rd346.push2 ⟨1236⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd349.jump
        (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
        hroutine (by evm_ov)⟩

theorem RD.dogFileUintToSwitch {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨315⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1325⟩
      (fileUintData I :: calldataWord I.calldata 4 :: ⟨313⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨315⟩) (ret := ⟨313⟩)
    (decoded := ⟨337⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (dogPatchedDJumpPrefix1405 ⟨337⟩ hpatch (by decide +native)) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.dogFileUintDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedDJumpPrefix1405 ⟨1236⟩ hpatch (by decide +native))
    (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.dogAuthCheckOk
    (code := code) (pc := ⟨1236⟩) (okPc := ⟨1325⟩)
    (key := fileUintData I) (ret := calldataWord I.calldata 4) (R := [⟨313⟩, sel])
    (by simpa [fileUintData] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
    hauth (dogPatchedDJumpPrefix1405 ⟨1325⟩ hpatch (by decide +native)) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.dogFileUintAuthRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨315⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨315⟩) (ret := ⟨313⟩)
    (decoded := ⟨337⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (dogPatchedDJumpPrefix1405 ⟨337⟩ hpatch (by decide +native)) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.dogFileUintDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedDJumpPrefix1405 ⟨1236⟩ hpatch (by decide +native))
    (by simp)
  exact RD.dogAuthCheckRevert
    (code := code) (pc := ⟨1236⟩) (okPc := ⟨1325⟩)
    (key := fileUintData I) (ret := calldataWord I.calldata 4) (R := [⟨313⟩, sel])
    (by simpa [fileUintData] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
    (by
      unfold solcErrorStringRevertTailWf dogAuthTailPc dogNotAuthorizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
    hauth (by simp)

theorem RD.dogFileUintStoreHoleLog {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1325⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileUintHoleBytes)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (sel :: R) (writeWord mem 128 data)
      (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨4⟩ data) k' C' := by
  have rd1326 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd1335 := evm_run rd1326 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw push4 ⟨1215261797⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨224⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov)]
  have hconst : UInt256.shiftLeft ⟨1215261797⟩ ⟨224⟩ =
      ABI.bytesToWord fileUintHoleBytes := by
    decide +native
  rw [hmatch, ← hconst] at rd1335
  have rd1336 := rd1335.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  rw [uInt256_eq_self] at rd1336
  have rd1337 := rd1336.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1337
  have rd1340 := rd1337.push2 ⟨1099⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd1341 := rd1340.jumpiNT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rdStorePrefix := evm_run rd1341 with [
    raw push1 ⟨4⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rdStorePrefix.sstore hperm
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rdMloadPrefix := evm_run rdStore with [
    raw push1 ⟨64⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdMload := rdMloadPrefix.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    mem_cost
    (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
    (by decide +native) (by evm_ov)
  have rdMstorePrefix := evm_run rdMload with [
    raw dup3
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdMstore := rdMstorePrefix.mstore 6 (writeWord mem 128 data)
    (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    mem_cost (by rfl) (by decide +native) (by evm_ov)
  have hread64' :
      (writeWord mem 128 data).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [writeWord_read_preserved mem 128 64 data
      (by rw [hmem]; decide +native)
      (Or.inl ⟨by norm_num, by rw [hmem]⟩)]
    exact hread64
  have rdMload2Prefix := rdMstore.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rdMload2 := rdMload2Prefix.mload 0 ⟨128⟩ (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    mem_cost
    (mloadFreePtrValue
      (by
        have hsz := writeWord_size mem 128 data (by rw [hmem]; decide +native)
        rw [hsz, hmem]
        decide)
      (by decide) hread64')
    (by decide +native) (by evm_ov)
  have rdTopicStack := evm_run rdMload2 with [
    raw dup4
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdTopic := rdTopicStack.pushConst dogFileUintLogTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by simp only [List.length_cons]; omega)
  have rdLogStack := evm_run rdTopic with [
    raw swap2
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
          (by exact dogPrefixWindowLe1405_of_true (by decide +native))
          (by exact dogPrefixWindowLt64_of_true (by decide +native))]
        decide +native)
      (by evm_ov)]
  have rdLog := RD.log2 0 (UInt256.ofNat 5) rdLogStack
    (by
      rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
        (by exact dogPrefixWindowLe1405_of_true (by decide +native))
        (by exact dogPrefixWindowLt64_of_true (by decide +native))]
      decide +native)
    hperm mem_cost (by decide +native) (by evm_ov)
  have rdPop1 := rdLog.pop
    (by
      rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
        (by exact dogPrefixWindowLe1405_of_true (by decide +native))
        (by exact dogPrefixWindowLt64_of_true (by decide +native))]
      decide +native)
    (by evm_ov)
  have rdPop2 := rdPop1.pop
    (by
      rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
        (by exact dogPrefixWindowLe1405_of_true (by decide +native))
        (by exact dogPrefixWindowLt64_of_true (by decide +native))]
      decide +native)
    (by evm_ov)
  exact ⟨_, _, rdPop2.jump
    (by
      rw [dogDecodePatchedEqPrefix1405 hpatch (by decide +native)
        (by exact dogPrefixWindowLe1405_of_true (by decide +native))
        (by exact dogPrefixWindowLt64_of_true (by decide +native))]
      decide +native)
    hret (by evm_ov)⟩

theorem RD.dogFileUintUnrecognizedRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1325⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileUintHoleBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  have rd1326 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd1335 := evm_run rd1326 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw push4 ⟨1215261797⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨224⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov)]
  have hconst : UInt256.shiftLeft ⟨1215261797⟩ ⟨224⟩ =
      ABI.bytesToWord fileUintHoleBytes := by
    decide +native
  rw [hconst] at rd1335
  have rd1336 := rd1335.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileUintHoleBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd1336
  have rd1337 := rd1336.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1337
  have rd1340 := rd1337.push2 ⟨1099⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd1099 := rd1340.jumpiT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    one_ne_zero_uint (dogPatchedDJumpPrefix1405 ⟨1099⟩ hpatch (by decide +native))
    (by evm_ov)
  have rd1100 := rd1099.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  exact RD.dogErrorStringRevertTailDirect
    (pc := ⟨1100⟩) (len := ⟨27⟩) (word := dogFileUnrecognizedRawWord)
    (op := .PUSH32) (width := 32) rd1100
    (by
      unfold dogErrorStringRevertTailDirectWf dogFileUnrecognizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
    (by decide) hmem hread64 (by simp only [List.length_cons]; omega)

theorem RD.dogFileUintSuccess {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨315⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintHoleBytes) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨4⟩ (fileUintData I)) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.dogFileUintToSwitch hpatch hreach hsz68 hsize hauth
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileUintHoleBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, hretPc⟩ := RD.dogFileUintStoreHoleLog
    (v := v) (code := code) (data := fileUintData I)
    (what := calldataWord I.calldata 4) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hswitch hword (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by decide +native))
    hperm hmemAuth hread64 (by simp)
  have hretPc' := hretPc.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
      decide +native)
    (by evm_ov)
  exact RD.stop hretPc'
    (by
      change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
      rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
      decide +native)
    (by simp only [List.length_singleton]; omega)

theorem RD.dogFileUintUnrecognizedParamRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨315⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotHole : fileUintWhat I ≠ fileUintHoleBytes) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.dogFileUintToSwitch hpatch hreach hsz68 hsize hauth
  have hneq :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintHoleBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotHole fileUintHoleBytes_length
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  exact RD.dogFileUintUnrecognizedRevert
    (v := v) (code := code) (data := fileUintData I)
    (what := calldataWord I.calldata 4) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hswitch hneq hmemAuth hread64 (by simp)

theorem dogFileUintBodyCoreOk
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata = some (fileUintLocals I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨315⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileUintData I
  let callerSlot := dogCallerWardsSlot I
  let locals := fileUintLocals I
  have hcallerWord : dogSlotWord callerSlot σ_evm I = dogSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have henc : returnEquiv ByteArray.empty none fileUintTransition.returnType := by
    rw [show fileUintTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  by_cases hauthEvm : dogSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : dogSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    by_cases hwhat : fileUintWhat I = fileUintHoleBytes
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩ data
      have hbody :
          ExecTransitionBody (config v) (contract v) evm0 locals fileUintTransition.body
            (.returned { contract := contract v, locals := locals } evm1 none) := by
        simpa [evm0, evm1, locals, data] using
          (fileUintHoleSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hwhat)
      have hret := RD.dogFileUintSuccess hpatch hreach hperm hsz68 hsize hauthSolc hwhat
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ data).1 = evm1.createdAccounts := by
        simp [evm1, evm0, initState, storageStore_createdAccounts]
      have haccounts :
          accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ data)
            evm1.accountMap := by
        simpa [evm1, evm0, initState, storageStore_accountMap, data] using
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩ data hAccounts
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccounts henc
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evm0 locals fileUintTransition.body
            .reverted := by
        simpa [evm0, locals] using
          (fileUintUnrecognizedSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hwhat)
      have hrev := RD.dogFileUintUnrecognizedParamRevert
        hpatch hreach hsz68 hsize hauthSolc hwhat
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : dogSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody :
        ExecTransitionBody (config v) (contract v) evm0 locals fileUintTransition.body
          .reverted := by
      have hguard := dogAuthGuardEval_false (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fileUintLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config v) (solm := { contract := contract v, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .ite
            (.binary .eq (.var "what") HoleParamLit)
            [ .assign .storage HoleRef (.var "data") ]
            [ .require (.boolLit false) ] ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, fileUintTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    have hrev := RD.dogFileUintAuthRevert hpatch hreach hsz68 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem dogFileUintBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg (contract v) I.calldata = some fileUintTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨315⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨315⟩) (ret := ⟨313⟩)
    (decoded := ⟨337⟩) (need := ⟨64⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_fileUint_none_short (v := v) hsz4 hshort)

theorem dogFileUintBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 8))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 8) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some fileUintTransition :=
    dogDispatchFileUint hsel
  have hreach := dogReachFileUintBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact dogFileUintBodyCoreOk hpatch hcode hwv hperm hsz68 hsize hdispatch
      (dogDecode_fileUint_ok (v := v) hsz68) hreach hAccounts
  · exact dogFileUintBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog

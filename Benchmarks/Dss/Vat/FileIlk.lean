import Benchmarks.Dss.Vat.FileLine
import Benchmarks.Dss.Vat.Ilks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Vat

/-! ## `file(bytes32,bytes32,uint256)` -/

abbrev fileIlkIlk (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileIlkWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev fileIlkIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileIlkWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileIlkData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fileIlkIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (fileIlkIlk I)

abbrev fileIlkIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (fileIlkIlk I)

abbrev fileIlkLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (fileIlkIlkValue I)).insert "what"
    (.fixedBytes bytes32Width (fileIlkWhat I))).insert "data"
    (.int (Int.ofNat (fileIlkData I).toNat))

abbrev fileIlkSpotBytes : List UInt8 :=
  [115, 112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileIlkLineBytes : List UInt8 :=
  [108, 105, 110, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileIlkDustBytes : List UInt8 :=
  [100, 117, 115, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileIlkSpotWord : UInt256 :=
  UInt256.shiftLeft (⟨0x73706f74⟩ : UInt256) ⟨224⟩

abbrev fileIlkLineWord : UInt256 :=
  UInt256.shiftLeft (⟨0x6c696e65⟩ : UInt256) ⟨224⟩

abbrev fileIlkDustWord : UInt256 :=
  UInt256.shiftLeft (⟨0x64757374⟩ : UInt256) ⟨224⟩

abbrev fileIlkSpotSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkIlkKey I) + ⟨2⟩

abbrev fileIlkLineSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkIlkKey I) + ⟨3⟩

abbrev fileIlkDustSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkIlkKey I) + ⟨4⟩

theorem fileIlkIlk_length {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    (fileIlkIlk I).length = 32 := by
  unfold fileIlkIlk
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  omega

theorem fileIlkWhat_length {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    (fileIlkWhat I).length = 32 := by
  unfold fileIlkWhat
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  omega

theorem keyValueToWord_fileIlkIlkKey {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    keyValueToWord (fileIlkIlkKey I) = fileIlkIlkWord I := by
  have hlen32 : (fileIlkIlk I).length = 32 := fileIlkIlk_length (I := I) hsz100
  have hword : ABI.bytesToWord (fileIlkIlk I) = fileIlkIlkWord I := by
    simpa [fileIlkIlk, fileIlkIlkWord] using
      (decode_word_at_eq I.calldata 4 (by omega) (by norm_num))
  have hbytes : fileIlkIlk I = EVM.Word.toBytesBE (fileIlkIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkIlk I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [fileIlkIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (fileIlkIlkWord I)

theorem fileIlkSpotSlotFor_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    fileIlkSpotSlotFor I = solcMappingSlot ⟨2⟩ (fileIlkIlkWord I) + ⟨2⟩ := by
  unfold fileIlkSpotSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkIlkKey hsz100]

theorem fileIlkLineSlotFor_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    fileIlkLineSlotFor I = solcMappingSlot ⟨2⟩ (fileIlkIlkWord I) + ⟨3⟩ := by
  unfold fileIlkLineSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkIlkKey hsz100]

theorem fileIlkDustSlotFor_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    fileIlkDustSlotFor I = solcMappingSlot ⟨2⟩ (fileIlkIlkWord I) + ⟨4⟩ := by
  unfold fileIlkDustSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkIlkKey hsz100]

theorem fileIlkSpotBytes_length : fileIlkSpotBytes.length = 32 := by
  rfl

theorem fileIlkLineBytes_length : fileIlkLineBytes.length = 32 := by
  rfl

theorem fileIlkDustBytes_length : fileIlkDustBytes.length = 32 := by
  rfl

theorem fileIlkSpotBytes_word : ABI.bytesToWord fileIlkSpotBytes = fileIlkSpotWord := by
  decide +native

theorem fileIlkLineBytes_word : ABI.bytesToWord fileIlkLineBytes = fileIlkLineWord := by
  decide +native

theorem fileIlkDustBytes_word : ABI.bytesToWord fileIlkDustBytes = fileIlkDustWord := by
  decide +native

theorem fileIlkWhatWord_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    ABI.bytesToWord (fileIlkWhat I) = fileIlkWhatWord I := by
  simpa [fileIlkWhat, fileIlkWhatWord] using
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)

theorem fileIlkWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8} {w : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hlen : bs.length = 32) (hbs : ABI.bytesToWord bs = w)
    (hword : fileIlkWhatWord I = w) :
    fileIlkWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkWhat I)
    (fileIlkWhat_length (I := I) hsz100)
  rw [fileIlkWhatWord_eq (I := I) hsz100, hword, ← hbs] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hlen)

theorem fileIlkWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8} {w : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hbs : ABI.bytesToWord bs = w)
    (hwhat : fileIlkWhat I = bs) :
    fileIlkWhatWord I = w := by
  rw [← hbs, ← hwhat]
  exact (fileIlkWhatWord_eq (I := I) hsz100).symm

theorem fileIlkLocals_get_ilk (I : ExecutionEnv) :
    (fileIlkLocals I).get? "ilk" = some (fileIlkIlkValue I) := by
  rw [fileIlkLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem fileIlkLocals_get_what (I : ExecutionEnv) :
    (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)) := by
  rw [fileIlkLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileIlkLocals_get_data (I : ExecutionEnv) :
    (fileIlkLocals I).get? "data" =
      some (.int (Int.ofNat (fileIlkData I).toNat)) := by
  rw [fileIlkLocals, store_get_self]

theorem fileIlkLocals_get_wards (I : ExecutionEnv) :
    (fileIlkLocals I).get? "wards" = none := by
  simp [fileIlkLocals]

theorem fileIlkLocals_get_live (I : ExecutionEnv) :
    (fileIlkLocals I).get? "live" = none := by
  simp [fileIlkLocals]

theorem fileIlkLocals_get_ilks (I : ExecutionEnv) :
    (fileIlkLocals I).get? "ilks" = none := by
  simp [fileIlkLocals]

theorem evalExpr_fileIlkData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileIlkData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileIlkData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileIlkData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileIlkWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {lit : Expr} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkWhat I)))
    (hlit : lit = .fixedBytesLit bytes32Width bs)
    (hwhat : fileIlkWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") lit) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkWhat I))
    rw [hget]
    rfl
  subst hlit
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileIlkWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {lit : Expr} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkWhat I)))
    (hlit : lit = .fixedBytesLit bytes32Width bs)
    (hwhat : fileIlkWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") lit) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkWhat I))
    rw [hget]
    rfl
  subst hlit
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_fileIlkField {evm : EVM.State} {I : ExecutionEnv} {field : Ident}
    {er : EvaledStorageRef}
    (hsz100 : 100 ≤ I.calldata.size)
    (hfield : er = { base := "ilks", steps := [.mindex (fileIlkIlkKey I), .field field] }) :
    evalStorageRef config { contract := contract, locals := fileIlkLocals I } evm
      (ilksF (.var "ilk") field) = .ok er := by
  have hlen : (fileIlkIlk I).length = bytes32Width.val + 1 := by
    simpa [bytes32Width] using fileIlkIlk_length (I := I) hsz100
  subst hfield
  have hvar :
      evalExpr? config { contract := contract, locals := fileIlkLocals I } evm (.var "ilk") =
        .ok (fileIlkIlkValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((fileIlkLocals I).get? "ilk") =
      .ok (fileIlkIlkValue I)
    rw [fileIlkLocals_get_ilk I]
    rfl
  simp [fileIlkIlkKey, fileIlkIlkValue, ilksF, hvar,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, pure, bind, hlen]

theorem assign_fileIlkSpotStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz100 : 100 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (fileIlkSpotSlotFor I) (fileIlkData I)
    assignStorageRef? config { contract := contract, locals := fileIlkLocals I } evm
      .storage (ilksF (.var "ilk") "spot") (.int (Int.ofNat (fileIlkData I).toNat)) =
        .ok ({ contract := contract, locals := fileIlkLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "ilks", steps := [.mindex (fileIlkIlkKey I), .field "spot"] } :
        EvaledStorageRef))
      (loc := wordLoc (fileIlkSpotSlotFor I))
      (hbase := fileIlkLocals_get_ilks I)
      (her := evalStorageRef_fileIlkField (I := I) (field := "spot") hsz100 rfl)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm'] using vatStorageLocStore_uint256 evm (fileIlkSpotSlotFor I) (fileIlkData I)

theorem assign_fileIlkLineStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz100 : 100 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (fileIlkLineSlotFor I) (fileIlkData I)
    assignStorageRef? config { contract := contract, locals := fileIlkLocals I } evm
      .storage (ilksF (.var "ilk") "line") (.int (Int.ofNat (fileIlkData I).toNat)) =
        .ok ({ contract := contract, locals := fileIlkLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "ilks", steps := [.mindex (fileIlkIlkKey I), .field "line"] } :
        EvaledStorageRef))
      (loc := wordLoc (fileIlkLineSlotFor I))
      (hbase := fileIlkLocals_get_ilks I)
      (her := evalStorageRef_fileIlkField (I := I) (field := "line") hsz100 rfl)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm'] using vatStorageLocStore_uint256 evm (fileIlkLineSlotFor I) (fileIlkData I)

theorem assign_fileIlkDustStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz100 : 100 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (fileIlkDustSlotFor I) (fileIlkData I)
    assignStorageRef? config { contract := contract, locals := fileIlkLocals I } evm
      .storage (ilksF (.var "ilk") "dust") (.int (Int.ofNat (fileIlkData I).toNat)) =
        .ok ({ contract := contract, locals := fileIlkLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "ilks", steps := [.mindex (fileIlkIlkKey I), .field "dust"] } :
        EvaledStorageRef))
      (loc := wordLoc (fileIlkDustSlotFor I))
      (hbase := fileIlkLocals_get_ilks I)
      (her := evalStorageRef_fileIlkField (I := I) (field := "dust") hsz100 rfl)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm'] using vatStorageLocStore_uint256 evm (fileIlkDustSlotFor I) (fileIlkData I)

private theorem fileIlkLine_ne_spot : fileIlkLineBytes ≠ fileIlkSpotBytes := by
  decide +native

private theorem fileIlkDust_ne_spot : fileIlkDustBytes ≠ fileIlkSpotBytes := by
  decide +native

private theorem fileIlkDust_ne_line : fileIlkDustBytes ≠ fileIlkLineBytes := by
  decide +native

theorem vatFileIlkSourceBodySpot {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hwhat : fileIlkWhat I = fileIlkSpotBytes) :
    let locals := fileIlkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkSpotSlotFor I) (fileIlkData I)
    ExecTransitionBody config contract evm0 locals fileIlkTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "wards" = none; exact fileIlkLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "live" = none; exact fileIlkLocals_get_live I)
    hlive
  have hcond := evalExpr_fileIlkWhatEq_true (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hwhat
  have hdata := evalExpr_fileIlkData (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "data" =
      some (.int (Int.ofNat (fileIlkData I).toNat)); exact fileIlkLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "spot") (.int (Int.ofNat (fileIlkData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileIlkSpotStorage evm0 I hsz100
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "spot") (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, fileIlkTransition, nonpayable, auth, requireLive, locals,
    evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem vatFileIlkSourceBodyLine {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hwhat : fileIlkWhat I = fileIlkLineBytes) :
    let locals := fileIlkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkLineSlotFor I) (fileIlkData I)
    ExecTransitionBody config contract evm0 locals fileIlkTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "wards" = none; exact fileIlkLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "live" = none; exact fileIlkLocals_get_live I)
    hlive
  have hspotNe : fileIlkWhat I ≠ fileIlkSpotBytes := by
    intro hbad
    exact fileIlkLine_ne_spot (by rw [← hwhat, hbad])
  have hspot := evalExpr_fileIlkWhatEq_false (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hspotNe
  have hline := evalExpr_fileIlkWhatEq_true (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hwhat
  have hdata := evalExpr_fileIlkData (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "data" =
      some (.int (Int.ofNat (fileIlkData I).toNat)); exact fileIlkLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "line") (.int (Int.ofNat (fileIlkData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileIlkLineStorage evm0 I hsz100
  have hlineThen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "line") (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") ilkLineParamLit)
          [.assign .storage (ilksF (.var "ilk") "line") (.var "data")]
          [.ite (.binary .eq (.var "what") dustParamLit)
            [.assign .storage (ilksF (.var "ilk") "dust") (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hline hlineThen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hspot helse) ExecBlock.nil
  simpa [ExecTransitionBody, fileIlkTransition, nonpayable, auth, requireLive, locals,
    evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem vatFileIlkSourceBodyDust {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hwhat : fileIlkWhat I = fileIlkDustBytes) :
    let locals := fileIlkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkDustSlotFor I) (fileIlkData I)
    ExecTransitionBody config contract evm0 locals fileIlkTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "wards" = none; exact fileIlkLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "live" = none; exact fileIlkLocals_get_live I)
    hlive
  have hspotNe : fileIlkWhat I ≠ fileIlkSpotBytes := by
    intro hbad
    exact fileIlkDust_ne_spot (by rw [← hwhat, hbad])
  have hlineNe : fileIlkWhat I ≠ fileIlkLineBytes := by
    intro hbad
    exact fileIlkDust_ne_line (by rw [← hwhat, hbad])
  have hspot := evalExpr_fileIlkWhatEq_false (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hspotNe
  have hline := evalExpr_fileIlkWhatEq_false (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hlineNe
  have hdust := evalExpr_fileIlkWhatEq_true (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hwhat
  have hdata := evalExpr_fileIlkData (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "data" =
      some (.int (Int.ofNat (fileIlkData I).toNat)); exact fileIlkLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "dust") (.int (Int.ofNat (fileIlkData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileIlkDustStorage evm0 I hsz100
  have hdustThen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "dust") (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hdustElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dustParamLit)
            [.assign .storage (ilksF (.var "ilk") "dust") (.var "data")]
            [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hdust hdustThen) ExecBlock.nil
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") ilkLineParamLit)
          [.assign .storage (ilksF (.var "ilk") "line") (.var "data")]
          [.ite (.binary .eq (.var "what") dustParamLit)
            [.assign .storage (ilksF (.var "ilk") "dust") (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hline hdustElse) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hspot helse) ExecBlock.nil
  simpa [ExecTransitionBody, fileIlkTransition, nonpayable, auth, requireLive, locals,
    evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem vatFileIlkSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := fileIlkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileIlkTransition.body .reverted := by
  intro locals evm0
  have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "wards" = none; exact fileIlkLocals_get_wards I)
    hauth
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, fileIlkTransition, nonpayable, auth, requireLive, locals, evm0]
    using ExecFuncBody.execBlockRevert hblock

theorem vatFileIlkSourceBodyNotLive {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I ≠ ⟨1⟩) :
    let locals := fileIlkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileIlkTransition.body .reverted := by
  intro locals evm0
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "wards" = none; exact fileIlkLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "live" = none; exact fileIlkLocals_get_live I)
    hlive
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
  simpa [ExecTransitionBody, fileIlkTransition, nonpayable, auth, requireLive, locals, evm0]
    using ExecFuncBody.execBlockRevert hblock

theorem vatFileIlkSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hspotNe : fileIlkWhat I ≠ fileIlkSpotBytes)
    (hlineNe : fileIlkWhat I ≠ fileIlkLineBytes)
    (hdustNe : fileIlkWhat I ≠ fileIlkDustBytes) :
    let locals := fileIlkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileIlkTransition.body .reverted := by
  intro locals evm0
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "wards" = none; exact fileIlkLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileIlkLocals I).get? "live" = none; exact fileIlkLocals_get_live I)
    hlive
  have hspot := evalExpr_fileIlkWhatEq_false (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hspotNe
  have hline := evalExpr_fileIlkWhatEq_false (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hlineNe
  have hdust := evalExpr_fileIlkWhatEq_false (evm := evm0) (I := I) (locals := locals)
    (by change (fileIlkLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkWhat I)); exact fileIlkLocals_get_what I)
    (by rfl) hdustNe
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hbad :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hdustElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dustParamLit)
            [.assign .storage (ilksF (.var "ilk") "dust") (.var "data")]
            [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hdust hbad)
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") ilkLineParamLit)
          [.assign .storage (ilksF (.var "ilk") "line") (.var "data")]
          [.ite (.binary .eq (.var "what") dustParamLit)
            [.assign .storage (ilksF (.var "ilk") "dust") (.var "data")]
            [.require (.boolLit false)]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hline hdustElse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hspot helse)
  simpa [ExecTransitionBody, fileIlkTransition, nonpayable, auth, requireLive, locals, evm0]
    using ExecFuncBody.execBlockRevert hblock

theorem decodeABIValues_bytes32_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [bytes32, bytes32, uint256] bytes 0 0 96 96 DecodeMode.legacySolc05 =
      some ([.fixedBytes bytes32Width (bytes.take 32),
        .fixedBytes bytes32Width ((bytes.drop 32).take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hge64 : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  simp [decodeABIValues?, bytes32, uint256, bytes32Width, uint256Int, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, readWord?, decodeABIWord?, hlen0,
    hlen32, hge32, hge64]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 64).take 32)).val.isLt

theorem decodeABIValues_bytes32_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [bytes32, bytes32, uint256] bytes 0 0 96 96 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, bytes32, uint256, bytes32Width, uint256Int, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hnot : ¬ 32 ≤ bytes.length - 32 := by
        rw [List.length_take, List.length_drop] at htake32n
        omega
      simp [hnot]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hge32 : 32 ≤ bytes.length - 32 := by
        omega
      have hnot : ¬ 32 ≤ bytes.length - 64 := by
        omega
      simp [readWord?, readBytes?, hge32, hnot]

theorem decodeCalldata_legacyBytes32_bytes32_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z] [bytes32, bytes32, uint256] cd =
      some ((((∅ : Store).insert x
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.fixedBytes bytes32Width ((cd.toList.drop 36).take 32))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, uint256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, bytes32, uint256] = some 96 by decide +native]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword68]

theorem decodeCalldata_legacyBytes32_bytes32_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z] [bytes32, bytes32, uint256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, uint256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, bytes32, uint256] = some 96 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_bytes32_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem vatDecode_fileIlk_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
      (transitionSignature fileIlkTransition).paramTypes I.calldata =
        some (fileIlkLocals I) := by
  simpa [config, fileIlkTransition, fileIlkLocals, fileIlkIlkValue, fileIlkIlk,
    fileIlkWhat, fileIlkData, bytes32, uint256, bytes32Width, uint256Int] using
    (decodeCalldata_legacyBytes32_bytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "what") (z := "data") hsz100)

theorem vatDecode_fileIlk_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
      (transitionSignature fileIlkTransition).paramTypes I.calldata = none := by
  simpa [config, fileIlkTransition, bytes32, uint256, bytes32Width, uint256Int] using
    (decodeCalldata_legacyBytes32_bytes32_uint256_none_short (cd := I.calldata)
      (x := "ilk") (y := "what") (z := "data") hsz4 hshort)

theorem vatDispatchFileIlk {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 6)) :
    dispatchMsg contract I.calldata = some fileIlkTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileIlkTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes]
  decide +native

theorem vatReachFileIlkBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 6)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨483⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x1a0b287e⟩ :=
    vatSelWord_eq_of_beq I hsz 0x1a 0x0b 0x28 0x7e ⟨0x1a0b287e⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    decide +native
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms419Body 1 (by omega) ⟨483⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by decide +native)

@[reducible] def solcThreeWordExternalLoadAndJumpWf
    (code : ByteArray) (pc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + ⟨1⟩
  let p13 := p12 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p18 := p15 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.CALLDATALOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p7 = some (.DUP2, .none)
  ∧ decode code p8 = some (.ADD, .none)
  ∧ decode code p9 = some (.CALLDATALOAD, .none)
  ∧ decode code p10 = some (.SWAP1, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.ADD, .none)
  ∧ decode code p14 = some (.CALLDATALOAD, .none)
  ∧ decode code p15 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p18 = some (.JUMP, .none)

theorem RD.solcThreeWordExternalLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hwf : solcThreeWordExternalLoadAndJumpWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14,
      hd15, hd18⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.dup1 hd2 (by evm_ov)
  have rd4 := rd3.calldataload hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd7 := rd5.push1 ⟨32⟩ hd5 (by evm_ov)
  have rd8 := rd7.dup2 hd7 (by evm_ov)
  have rd9 := rd8.add hd8 (by evm_ov)
  have rd10 := rd9.calldataload hd9 (by evm_ov)
  have rd12 := rd10.swap1 hd10 (by evm_ov)
  have rd13 := rd12.push1 ⟨64⟩ hd12 (by evm_ov)
  have rd14 := rd13.add hd13 (by evm_ov)
  have rd15 := rd14.calldataload hd14 (by evm_ov)
  have rd18 := rd15.push2 routine hd15 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨68⟩ : UInt256).toNat = 68 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
      using rd18.jump hd18 hroutine (by evm_ov)⟩

theorem vatFileIlkX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1632⟩
        [fileIlkData I, fileIlkWhatWord I, fileIlkIlkWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨483⟩) (ret := ⟨524⟩)
    (decoded := ⟨505⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcThreeWordExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨505⟩) (ret := ⟨524⟩) (routine := ⟨1632⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcThreeWordExternalLoadAndJumpWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileIlkData, fileIlkWhatWord, fileIlkIlkWord] using hroutine⟩

theorem RD.vatFileIlkCleanup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1982⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret R mem (UInt256.ofNat 3) rdata acc k' C' := by
  have rd1983 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1984 := rd1983.pop (by decide +native) (by evm_ov)
  have rd1985 := rd1984.pop (by decide +native) (by evm_ov)
  have rd1986 := rd1985.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1986.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vatFileIlkSkipSpot {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1784⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hwhat : what ≠ fileIlkSpotWord)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨1825⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd1785 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1786 := rd1785.dup2 (by decide +native) (by evm_ov)
  have rd1791 := rd1786.push4 ⟨484187101⟩ (by decide +native) (by evm_ov)
  have rd1793 := rd1791.push1 ⟨226⟩ (by decide +native) (by evm_ov)
  have rd1794 := rd1793.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨484187101⟩ : UInt256) ⟨226⟩ = fileIlkSpotWord := by
    decide +native
  rw [hconst] at rd1794
  have rd1795 := rd1794.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq fileIlkSpotWord what = ⟨0⟩ :=
    u256_eq_of_ne (fun hbad => hwhat hbad.symm)
  rw [heq0] at rd1795
  have rd1796 := rd1795.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1796
  have rd1799 := rd1796.push2 ⟨1825⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1799.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vatFileIlkStoreSpot {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1784⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwhat : what = fileIlkSpotWord)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret R (twoWordHashMem ilk ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨2⟩ ilk + ⟨2⟩) data) k' C' := by
  have rd1785 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1786 := rd1785.dup2 (by decide +native) (by evm_ov)
  have rd1791 := rd1786.push4 ⟨484187101⟩ (by decide +native) (by evm_ov)
  have rd1793 := rd1791.push1 ⟨226⟩ (by decide +native) (by evm_ov)
  have rd1794 := rd1793.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨484187101⟩ : UInt256) ⟨226⟩ = fileIlkSpotWord := by
    decide +native
  rw [hwhat, ← hconst] at rd1794
  have rd1795 := rd1794.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd1795
  have rd1796 := rd1795.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1796
  have rd1799 := rd1796.push2 ⟨1825⟩ (by decide +native) (by evm_ov)
  have rd1800 := rd1799.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1802 := rd1800.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd1803 := rd1802.dup4 (by decide +native) (by evm_ov)
  have rd1804 := rd1803.dup2 (by decide +native) (by evm_ov)
  have rd1805 := rd1804.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1807 := rd1805.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  have rd1809 := rd1807.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd1810 := rd1809.dup2 (by decide +native)
    (by simp [List.length_cons] at hov ⊢; omega)
  have rd1811 := rd1810.swap1 (by decide +native)
    (by simp [List.length_cons] at hov ⊢; omega)
  have rd1812 := rd1811.mstore 0 (twoWordHashMem ilk ⟨2⟩ mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1814 := rd1812.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd1815 := rd1814.swap1 (by decide +native) (by evm_ov)
  have rd1816 := rd1815.swap2 (by decide +native) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨2⟩ ilk hmem
  have rd1817 := rd1816.keccak256 0 (solcMappingSlot ⟨2⟩ ilk) (UInt256.ofNat 3)
    (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd1818 := rd1817.add (by decide +native) (by evm_ov)
  have rd1819 := rd1818.dup2 (by decide +native) (by evm_ov)
  have rd1820 := rd1819.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1821⟩ := rd1820.sstore hperm (by decide +native) (by evm_ov)
  have rd1824 := rd1821.push2 ⟨1982⟩ (by decide +native) (by evm_ov)
  have rd1982 := rd1824.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.vatFileIlkCleanup rd1982 hret (by omega)

theorem RD.vatFileIlkSkipLine {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1825⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hwhat : what ≠ fileIlkLineWord)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨1865⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd1826 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1827 := rd1826.dup2 (by decide +native) (by evm_ov)
  have rd1832 := rd1827.push4 ⟨1818848869⟩ (by decide +native) (by evm_ov)
  have rd1834 := rd1832.push1 ⟨224⟩ (by decide +native) (by evm_ov)
  have rd1835 := rd1834.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨1818848869⟩ : UInt256) ⟨224⟩ = fileIlkLineWord := by
    rfl
  rw [hconst] at rd1835
  have rd1836 := rd1835.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq fileIlkLineWord what = ⟨0⟩ :=
    u256_eq_of_ne (fun hbad => hwhat hbad.symm)
  rw [heq0] at rd1836
  have rd1837 := rd1836.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1837
  have rd1840 := rd1837.push2 ⟨1865⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1840.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vatFileIlkStoreLine {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1825⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwhat : what = fileIlkLineWord)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret R (twoWordHashMem ilk ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨2⟩ ilk + ⟨3⟩) data) k' C' := by
  have rd1826 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1827 := rd1826.dup2 (by decide +native) (by evm_ov)
  have rd1832 := rd1827.push4 ⟨1818848869⟩ (by decide +native) (by evm_ov)
  have rd1834 := rd1832.push1 ⟨224⟩ (by decide +native) (by evm_ov)
  have rd1835 := rd1834.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨1818848869⟩ : UInt256) ⟨224⟩ = fileIlkLineWord := by
    rfl
  rw [hwhat, ← hconst] at rd1835
  have rd1836 := rd1835.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd1836
  have rd1837 := rd1836.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1837
  have rd1840 := rd1837.push2 ⟨1865⟩ (by decide +native) (by evm_ov)
  have rd1841 := rd1840.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1843 := rd1841.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd1844 := rd1843.dup4 (by decide +native) (by evm_ov)
  have rd1845 := rd1844.dup2 (by decide +native) (by evm_ov)
  have rd1846 := rd1845.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1848 := rd1846.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  have rd1850 := rd1848.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd1851 := rd1850.mstore 0 (twoWordHashMem ilk ⟨2⟩ mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1853 := rd1851.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd1854 := rd1853.swap1 (by decide +native) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨2⟩ ilk hmem
  have rd1855 := rd1854.keccak256 0 (solcMappingSlot ⟨2⟩ ilk) (UInt256.ofNat 3)
    (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd1857 := rd1855.push1 ⟨3⟩ (by decide +native) (by evm_ov)
  have rd1858 := rd1857.add (by decide +native) (by evm_ov)
  have rd1859 := rd1858.dup2 (by decide +native) (by evm_ov)
  have rd1860 := rd1859.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1861⟩ := rd1860.sstore hperm (by decide +native) (by evm_ov)
  have rd1864 := rd1861.push2 ⟨1982⟩ (by decide +native) (by evm_ov)
  have rd1982 := rd1864.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨k', C', hout⟩ := RD.vatFileIlkCleanup rd1982 hret (by omega)
  exact ⟨k', C', by
    simpa [u256_add_comm (⟨3⟩ : UInt256) (solcMappingSlot ⟨2⟩ ilk)] using hout⟩

theorem RD.vatFileIlkSkipDust {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1865⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hwhat : what ≠ fileIlkDustWord)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨1905⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd1866 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1867 := rd1866.dup2 (by decide +native) (by evm_ov)
  have rd1872 := rd1867.push4 ⟨421354717⟩ (by decide +native) (by evm_ov)
  have rd1874 := rd1872.push1 ⟨226⟩ (by decide +native) (by evm_ov)
  have rd1875 := rd1874.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨421354717⟩ : UInt256) ⟨226⟩ = fileIlkDustWord := by
    decide +native
  rw [hconst] at rd1875
  have rd1876 := rd1875.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq fileIlkDustWord what = ⟨0⟩ :=
    u256_eq_of_ne (fun hbad => hwhat hbad.symm)
  rw [heq0] at rd1876
  have rd1877 := rd1876.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1877
  have rd1880 := rd1877.push2 ⟨1905⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1880.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vatFileIlkStoreDust {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1865⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwhat : what = fileIlkDustWord)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret R (twoWordHashMem ilk ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨2⟩ ilk + ⟨4⟩) data) k' C' := by
  have rd1866 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1867 := rd1866.dup2 (by decide +native) (by evm_ov)
  have rd1872 := rd1867.push4 ⟨421354717⟩ (by decide +native) (by evm_ov)
  have rd1874 := rd1872.push1 ⟨226⟩ (by decide +native) (by evm_ov)
  have rd1875 := rd1874.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨421354717⟩ : UInt256) ⟨226⟩ = fileIlkDustWord := by
    decide +native
  rw [hwhat, ← hconst] at rd1875
  have rd1876 := rd1875.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd1876
  have rd1877 := rd1876.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1877
  have rd1880 := rd1877.push2 ⟨1905⟩ (by decide +native) (by evm_ov)
  have rd1881 := rd1880.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1883 := rd1881.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd1884 := rd1883.dup4 (by decide +native) (by evm_ov)
  have rd1885 := rd1884.dup2 (by decide +native) (by evm_ov)
  have rd1886 := rd1885.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1888 := rd1886.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  have rd1890 := rd1888.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd1891 := rd1890.mstore 0 (twoWordHashMem ilk ⟨2⟩ mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1893 := rd1891.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd1894 := rd1893.swap1 (by decide +native) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨2⟩ ilk hmem
  have rd1895 := rd1894.keccak256 0 (solcMappingSlot ⟨2⟩ ilk) (UInt256.ofNat 3)
    (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd1897 := rd1895.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  have rd1898 := rd1897.add (by decide +native) (by evm_ov)
  have rd1899 := rd1898.dup2 (by decide +native) (by evm_ov)
  have rd1900 := rd1899.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1901⟩ := rd1900.sstore hperm (by decide +native) (by evm_ov)
  have rd1904 := rd1901.push2 ⟨1982⟩ (by decide +native) (by evm_ov)
  have rd1982 := rd1904.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨k', C', hout⟩ := RD.vatFileIlkCleanup rd1982 hret (by omega)
  exact ⟨k', C', by
    simpa [u256_add_comm (⟨4⟩ : UInt256) (solcMappingSlot ⟨2⟩ ilk)] using hout⟩

theorem RD.vatFileIlkStoreBad {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1865⟩ (data :: what :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwhat : what ≠ fileIlkDustWord)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  obtain ⟨_, _, rdBad⟩ := RD.vatFileIlkSkipDust h hwhat (by omega)
  exact RD.vatFileUnrecognizedRevert
    (data := data) (what := what) (ret := ilk) (R := ret :: R)
    rdBad hmem hread64 (by simpa [List.length_cons] using hov)

theorem vatFileIlkX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨483⟩) (ret := ⟨524⟩)
    (decoded := ⟨505⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem vatFileIlkBodyCoreOkSpot
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hwhat : fileIlkWhat I = fileIlkSpotBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
        (transitionSignature fileIlkTransition).paramTypes I.calldata =
          some (fileIlkLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileIlkLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkSpotSlotFor I) (fileIlkData I)
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]; exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]; exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileIlkTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (vatFileIlkSourceBodySpot (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz100 hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := vatFileIlkX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨1632⟩) (okPc := ⟨1714⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
    (code := vatBytecode) (pc := ⟨1714⟩) (okPc := ⟨1784⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hafterAuth
    (by unfold vatLiveGuardWf; repeat' first | apply And.intro | decide +native)
    hliveSolc (by jump_dest) (by simp)
  have hwhatWord : fileIlkWhatWord I = fileIlkSpotWord :=
    fileIlkWhatWord_eq_of_bytes_eq hsz100 fileIlkSpotBytes_word hwhat
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hretPc⟩ := RD.vatFileIlkStoreSpot
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hstorePc hwhatWord (by jump_dest) hperm hmemAuth
    (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  have hslot := fileIlkSpotSlotFor_eq (I := I) hsz100
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm (fileIlkSpotSlotFor I) (fileIlkData I))
        ByteArray.empty := by
    simpa [hslot] using RD.stop hretPc' (by decide +native) (by simp)
  have haccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm (fileIlkSpotSlotFor I) (fileIlkData I))
        evm1.accountMap := by
    simpa [evm1, evm0, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (fileIlkSpotSlotFor I) (fileIlkData I)
        hAccounts
  have henc : returnEquiv ByteArray.empty none fileIlkTransition.returnType := by
    rw [show fileIlkTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    haccounts henc

theorem vatFileIlkBodyCoreOkLine
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hwhat : fileIlkWhat I = fileIlkLineBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
        (transitionSignature fileIlkTransition).paramTypes I.calldata =
          some (fileIlkLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileIlkLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkLineSlotFor I) (fileIlkData I)
  have hspotNe : fileIlkWhat I ≠ fileIlkSpotBytes := by
    intro hbad; exact fileIlkLine_ne_spot (by rw [← hwhat, hbad])
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]; exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]; exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileIlkTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (vatFileIlkSourceBodyLine (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz100 hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := vatFileIlkX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨1632⟩) (okPc := ⟨1714⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
    (code := vatBytecode) (pc := ⟨1714⟩) (okPc := ⟨1784⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hafterAuth
    (by unfold vatLiveGuardWf; repeat' first | apply And.intro | decide +native)
    hliveSolc (by jump_dest) (by simp)
  have hspotWordNe : fileIlkWhatWord I ≠ fileIlkSpotWord := by
    intro hbad
    exact hspotNe (fileIlkWhat_eq_of_word_eq hsz100 fileIlkSpotBytes_length
      fileIlkSpotBytes_word hbad)
  obtain ⟨_, _, hlinePc⟩ := RD.vatFileIlkSkipSpot
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hstorePc hspotWordNe (by simp)
  have hwhatWord : fileIlkWhatWord I = fileIlkLineWord :=
    fileIlkWhatWord_eq_of_bytes_eq hsz100 fileIlkLineBytes_word hwhat
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hretPc⟩ := RD.vatFileIlkStoreLine
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hlinePc hwhatWord (by jump_dest) hperm hmemAuth
    (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  have hslot := fileIlkLineSlotFor_eq (I := I) hsz100
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm (fileIlkLineSlotFor I) (fileIlkData I))
        ByteArray.empty := by
    simpa [hslot] using RD.stop hretPc' (by decide +native) (by simp)
  have haccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm (fileIlkLineSlotFor I) (fileIlkData I))
        evm1.accountMap := by
    simpa [evm1, evm0, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (fileIlkLineSlotFor I) (fileIlkData I)
        hAccounts
  have henc : returnEquiv ByteArray.empty none fileIlkTransition.returnType := by
    rw [show fileIlkTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    haccounts henc

theorem vatFileIlkBodyCoreOkDust
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hwhat : fileIlkWhat I = fileIlkDustBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
        (transitionSignature fileIlkTransition).paramTypes I.calldata =
          some (fileIlkLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileIlkLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkDustSlotFor I) (fileIlkData I)
  have hspotNe : fileIlkWhat I ≠ fileIlkSpotBytes := by
    intro hbad; exact fileIlkDust_ne_spot (by rw [← hwhat, hbad])
  have hlineNe : fileIlkWhat I ≠ fileIlkLineBytes := by
    intro hbad; exact fileIlkDust_ne_line (by rw [← hwhat, hbad])
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]; exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]; exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileIlkTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (vatFileIlkSourceBodyDust (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz100 hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := vatFileIlkX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨1632⟩) (okPc := ⟨1714⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
    (code := vatBytecode) (pc := ⟨1714⟩) (okPc := ⟨1784⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hafterAuth
    (by unfold vatLiveGuardWf; repeat' first | apply And.intro | decide +native)
    hliveSolc (by jump_dest) (by simp)
  have hspotWordNe : fileIlkWhatWord I ≠ fileIlkSpotWord := by
    intro hbad
    exact hspotNe (fileIlkWhat_eq_of_word_eq hsz100 fileIlkSpotBytes_length
      fileIlkSpotBytes_word hbad)
  obtain ⟨_, _, hlinePc⟩ := RD.vatFileIlkSkipSpot
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hstorePc hspotWordNe (by simp)
  have hlineWordNe : fileIlkWhatWord I ≠ fileIlkLineWord := by
    intro hbad
    exact hlineNe (fileIlkWhat_eq_of_word_eq hsz100 fileIlkLineBytes_length
      fileIlkLineBytes_word hbad)
  obtain ⟨_, _, hdustPc⟩ := RD.vatFileIlkSkipLine
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hlinePc hlineWordNe (by simp)
  have hwhatWord : fileIlkWhatWord I = fileIlkDustWord :=
    fileIlkWhatWord_eq_of_bytes_eq hsz100 fileIlkDustBytes_word hwhat
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hretPc⟩ := RD.vatFileIlkStoreDust
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hdustPc hwhatWord (by jump_dest) hperm hmemAuth
    (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  have hslot := fileIlkDustSlotFor_eq (I := I) hsz100
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm (fileIlkDustSlotFor I) (fileIlkData I))
        ByteArray.empty := by
    simpa [hslot] using RD.stop hretPc' (by decide +native) (by simp)
  have haccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm (fileIlkDustSlotFor I) (fileIlkData I))
        evm1.accountMap := by
    simpa [evm1, evm0, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (fileIlkDustSlotFor I) (fileIlkData I)
        hAccounts
  have henc : returnEquiv ByteArray.empty none fileIlkTransition.returnType := by
    rw [show fileIlkTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    haccounts henc

theorem vatFileIlkBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
        (transitionSignature fileIlkTransition).paramTypes I.calldata =
          some (fileIlkLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileIlkLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I ≠ ⟨1⟩ := by
    intro hbad; exact hauth (by rw [hcallerWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileIlkTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatFileIlkSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := vatFileIlkX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  have hrev := RD.vatAuthCheckRevert
    (pc := ⟨1632⟩) (okPc := ⟨1714⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
    (by unfold vatAuthRevertTailWf vatAuthTailPc; repeat' first | apply And.intro | decide +native)
    hauthSolc (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatFileIlkBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
        (transitionSignature fileIlkTransition).paramTypes I.calldata =
          some (fileIlkLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileIlkLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]; exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I ≠ ⟨1⟩ := by
    intro hbad; exact hlive (by rw [hliveWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileIlkTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatFileIlkSourceBodyNotLive (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm
        hliveSolm)
  obtain ⟨_, _, hdecoded⟩ := vatFileIlkX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨1632⟩) (okPc := ⟨1714⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ ≠ ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hreadAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have hrev := RD.vatLiveGuardRevert
    (code := vatBytecode) (pc := ⟨1714⟩) (okPc := ⟨1784⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hafterAuth
    (by unfold vatLiveGuardWf; repeat' first | apply And.intro | decide +native)
    (by
      unfold solcErrorStringRevertTailWf vatLiveGuardTailPc vatNotLiveRawWord
      repeat' first | apply And.intro | decide +native)
    hliveSolc hmemAuth hreadAuth (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatFileIlkBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hspotNe : fileIlkWhat I ≠ fileIlkSpotBytes)
    (hlineNe : fileIlkWhat I ≠ fileIlkLineBytes)
    (hdustNe : fileIlkWhat I ≠ fileIlkDustBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileIlkTransition.params.map Param.name)
        (transitionSignature fileIlkTransition).paramTypes I.calldata =
          some (fileIlkLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileIlkLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]; exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]; exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileIlkTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatFileIlkSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm
        hliveSolm hspotNe hlineNe hdustNe)
  obtain ⟨_, _, hdecoded⟩ := vatFileIlkX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨1632⟩) (okPc := ⟨1714⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
    (code := vatBytecode) (pc := ⟨1714⟩) (okPc := ⟨1784⟩)
    (key := fileIlkData I) (ret := fileIlkWhatWord I)
    (R := [fileIlkIlkWord I, ⟨524⟩, sel]) hafterAuth
    (by unfold vatLiveGuardWf; repeat' first | apply And.intro | decide +native)
    hliveSolc (by jump_dest) (by simp)
  have hspotWordNe : fileIlkWhatWord I ≠ fileIlkSpotWord := by
    intro hbad
    exact hspotNe (fileIlkWhat_eq_of_word_eq hsz100 fileIlkSpotBytes_length
      fileIlkSpotBytes_word hbad)
  obtain ⟨_, _, hlinePc⟩ := RD.vatFileIlkSkipSpot
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hstorePc hspotWordNe (by simp)
  have hlineWordNe : fileIlkWhatWord I ≠ fileIlkLineWord := by
    intro hbad
    exact hlineNe (fileIlkWhat_eq_of_word_eq hsz100 fileIlkLineBytes_length
      fileIlkLineBytes_word hbad)
  obtain ⟨_, _, hdustPc⟩ := RD.vatFileIlkSkipLine
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hlinePc hlineWordNe (by simp)
  have hdustWordNe : fileIlkWhatWord I ≠ fileIlkDustWord := by
    intro hbad
    exact hdustNe (fileIlkWhat_eq_of_word_eq hsz100 fileIlkDustBytes_length
      fileIlkDustBytes_word hbad)
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hreadAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have hrev := RD.vatFileIlkStoreBad
    (data := fileIlkData I) (what := fileIlkWhatWord I) (ilk := fileIlkIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hdustPc hdustWordNe hmemAuth hreadAuth (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatFileIlkBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨483⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatFileIlkX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (vatDecode_fileIlk_none_short hsz4 hshort)

theorem vatFileIlkBodyCore : VatBodyTheorem 6 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileIlkTransition :=
    vatDispatchFileIlk hsel
  have hreach := vatReachFileIlkBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩
    · by_cases hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩
      · by_cases hspot : fileIlkWhat I = fileIlkSpotBytes
        · exact vatFileIlkBodyCoreOkSpot hcode hsize hperm hwv hsz100 hauth hlive hspot
            hdispatch (vatDecode_fileIlk_ok hsz100) hreach hAccounts
        · by_cases hline : fileIlkWhat I = fileIlkLineBytes
          · exact vatFileIlkBodyCoreOkLine hcode hsize hperm hwv hsz100 hauth hlive hline
              hdispatch (vatDecode_fileIlk_ok hsz100) hreach hAccounts
          · by_cases hdust : fileIlkWhat I = fileIlkDustBytes
            · exact vatFileIlkBodyCoreOkDust hcode hsize hperm hwv hsz100 hauth hlive hdust
                hdispatch (vatDecode_fileIlk_ok hsz100) hreach hAccounts
            · exact vatFileIlkBodyCoreUnrecognized hcode hsize hwv hsz100 hauth hlive
                hspot hline hdust hdispatch (vatDecode_fileIlk_ok hsz100) hreach hAccounts
      · exact vatFileIlkBodyCoreNotLive hcode hsize hwv hsz100 hauth hlive hdispatch
          (vatDecode_fileIlk_ok hsz100) hreach hAccounts
    · exact vatFileIlkBodyCoreUnauthorized hcode hsize hwv hsz100 hauth hdispatch
        (vatDecode_fileIlk_ok hsz100) hreach hAccounts
  · exact vatFileIlkBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat

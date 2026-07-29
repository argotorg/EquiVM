import Benchmarks.Dss.Dog.Dispatch
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Dog

/-! ## `digs(bytes32,uint256)` -/

abbrev digsIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev digsIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev digsRad (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev digsIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (digsIlkBytes I)

abbrev digsIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (digsIlkBytes I)

abbrev digsLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (digsIlkValue I)).insert "rad"
    (.int (Int.ofNat (digsRad I).toNat))

abbrev digsLocalsDirtNew (I : ExecutionEnv) (dirtNew : UInt256) : Store :=
  (digsLocals I).insert "DirtNew" (.int (Int.ofNat dirtNew.toNat))

abbrev digsLocalsDirtNewIlkDirtNew
    (I : ExecutionEnv) (dirtNew ilkDirtNew : UInt256) : Store :=
  (digsLocalsDirtNew I dirtNew).insert "ilkDirtNew"
    (.int (Int.ofNat ilkDirtNew.toNat))

abbrev digsDirtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (digsIlkKey I), .field "dirt"] }

abbrev digsDirtSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (digsIlkKey I) + ⟨3⟩

abbrev dogDigsLogTopic : UInt256 :=
  ⟨38419356880049523883767881105734011175726579421031910001661450038485492137354⟩

abbrev uintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev uintBinaryLocalsZ (x y z : UInt256) : Store :=
  (uintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

theorem dogDecode_digs_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (digsTransition.params.map Param.name)
      (transitionSignature digsTransition).paramTypes I.calldata =
        some (digsLocals I) := by
  simpa [config, digsTransition, bytes32, bytes32Width, uint256, uint256Int,
    digsLocals, digsIlkValue, digsIlkBytes, digsRad, abiBytes32, abiBytes32Width,
    abiUInt256] using
    dogDecodeCalldataWithMode_legacyBytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "rad") hsz68

theorem dogDecode_digs_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode (digsTransition.params.map Param.name)
      (transitionSignature digsTransition).paramTypes I.calldata = none := by
  simpa [config, digsTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    dogDecodeCalldataWithMode_legacyBytes32_uint256_none_short (cd := I.calldata)
      (x := "ilk") (y := "rad") hsz4 hshort

theorem digsIlkBytes_len {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (digsIlkBytes I).length = bytes32Width.val + 1 := by
  unfold digsIlkBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem digsIlkBytes_len32 {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (digsIlkBytes I).length = 32 := by
  have hlen := digsIlkBytes_len (I := I) hsz68
  simpa [bytes32Width] using hlen

theorem keyValueToWord_digsIlkKey {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    keyValueToWord (digsIlkKey I) = digsIlkWord I := by
  have hlen32 : (digsIlkBytes I).length = 32 :=
    digsIlkBytes_len32 (I := I) hsz68
  have hword : ABI.bytesToWord (digsIlkBytes I) = digsIlkWord I := by
    simpa [digsIlkBytes, digsIlkWord] using
      (decode_word_at_eq_any I.calldata 4 (by omega))
  have hbytes : digsIlkBytes I = EVM.Word.toBytesBE (digsIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := digsIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [digsIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (digsIlkWord I)

theorem digsDirtSlotFor_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    digsDirtSlotFor I = solcMappingSlot ⟨1⟩ (digsIlkWord I) + ⟨3⟩ := by
  unfold digsDirtSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_digsIlkKey hsz68]

theorem digsLocals_get_ilk (I : ExecutionEnv) :
    (digsLocals I).get? "ilk" = some (digsIlkValue I) := by
  rw [digsLocals, store_get_ne _ _ (by decide), store_get_self]

theorem digsLocals_get_rad (I : ExecutionEnv) :
    (digsLocals I).get? "rad" =
      some (.int (Int.ofNat (digsRad I).toNat)) := by
  rw [digsLocals, store_get_self]

theorem digsLocalsDirtNew_get_ilk (I : ExecutionEnv) (dirtNew : UInt256) :
    (digsLocalsDirtNew I dirtNew).get? "ilk" = some (digsIlkValue I) := by
  rw [digsLocalsDirtNew, store_get_ne _ _ (by decide), digsLocals_get_ilk]

theorem digsLocalsDirtNew_get_rad (I : ExecutionEnv) (dirtNew : UInt256) :
    (digsLocalsDirtNew I dirtNew).get? "rad" =
      some (.int (Int.ofNat (digsRad I).toNat)) := by
  rw [digsLocalsDirtNew, store_get_ne _ _ (by decide), digsLocals_get_rad]

theorem digsLocalsDirtNew_get_DirtNew (I : ExecutionEnv) (dirtNew : UInt256) :
    (digsLocalsDirtNew I dirtNew).get? "DirtNew" =
      some (.int (Int.ofNat dirtNew.toNat)) := by
  rw [digsLocalsDirtNew, store_get_self]

theorem digsLocalsDirtNewIlkDirtNew_get_ilk
    (I : ExecutionEnv) (dirtNew ilkDirtNew : UInt256) :
    (digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew).get? "ilk" =
      some (digsIlkValue I) := by
  rw [digsLocalsDirtNewIlkDirtNew, store_get_ne _ _ (by decide),
    digsLocalsDirtNew_get_ilk]

theorem digsLocalsDirtNewIlkDirtNew_get_ilkDirtNew
    (I : ExecutionEnv) (dirtNew ilkDirtNew : UInt256) :
    (digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew).get? "ilkDirtNew" =
      some (.int (Int.ofNat ilkDirtNew.toNat)) := by
  rw [digsLocalsDirtNewIlkDirtNew, store_get_self]

theorem uintBinaryLocals_get_x (x y : UInt256) :
    (uintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocals, store_get_self]

theorem uintBinaryLocals_get_y (x y : UInt256) :
    (uintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [uintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem uintBinaryLocalsZ_get_x (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_ne _ _ (by decide), uintBinaryLocals_get_x]

theorem uintBinaryLocalsZ_get_z (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_self]

theorem evalExpr_varUInt256 {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_dogSub256_ok {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem evalExpr_dogSub256_revert {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (sub256 x y) =
      .revert := by
  have hneg : (a.toNat : Int) - (b.toNat : Int) < 0 := by
    omega
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hneg]

theorem execSubFunctionReturn {v : DogImmutables} (evm : EVM.State)
    {x y diff : UInt256}
    (hdiff : diff = UInt256.sub x y) (hle : y.toNat ≤ x.toNat) :
    ExecFuncBody (config v) { contract := contract v, locals := uintBinaryLocals x y } evm
      subFunction.body
      (.returned { contract := contract v, locals := uintBinaryLocalsZ x y diff } evm
        (some [.int (Int.ofNat diff.toNat)])) := by
  let locals := uintBinaryLocals x y
  let localsZ := uintBinaryLocalsZ x y diff
  have hx :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (v := v) (evm := evm)
        (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (v := v) (evm := evm)
        (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hzExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat diff.toNat)) :=
    evalExpr_dogSub256_ok hx hy hdiff hle
  have hz :
      evalExpr? (config v) { contract := contract v, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simpa [localsZ] using
      evalExpr_varUInt256 (v := v) (evm := evm)
        (locals := localsZ) (name := "z") (value := diff)
        (uintBinaryLocalsZ_get_z x y diff)
  have hxZ :
      evalExpr? (config v) { contract := contract v, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using
      evalExpr_varUInt256 (v := v) (evm := evm)
        (locals := localsZ) (name := "x") (value := x)
        (uintBinaryLocalsZ_get_x x y diff)
  have hreq :
      evalExpr? (config v) { contract := contract v, locals := localsZ } evm
        (.binary .le (.var "z") (.var "x")) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hz, hxZ, evalBinaryOp?]
    rw [hdiff, usub_toNat hle]
    exact_mod_cast Nat.sub_le x.toNat y.toNat
  have hret :
      evalExprs? (config v) { contract := contract v, locals := localsZ } evm
        [.var "z"] = .ok [.int (Int.ofNat diff.toNat)] := by
    simp [evalExprs?, hz, EvalResult.bind, bind, pure]
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm
        subFunction.body
        (.returned { contract := contract v, locals := localsZ } evm
          (some [.int (Int.ofNat diff.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hzExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
    exact ExecBlock.consReturn (ExecStmt.return hret)
  simpa [ExecFuncBody, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execSubFunctionRevert {v : DogImmutables} (evm : EVM.State)
    {x y : UInt256} (hlt : x.toNat < y.toNat) :
    ExecFuncBody (config v) { contract := contract v, locals := uintBinaryLocals x y } evm
      subFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  have hx :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (v := v) (evm := evm)
        (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (v := v) (evm := evm)
        (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hsub :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .revert :=
    evalExpr_dogSub256_revert hx hy hlt
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm
        subFunction.body .reverted := by
    simpa [subFunction, checkedSubUintInto, locals] using
      ExecBlock.consRevert (ExecStmt.letDeclRevert (ty := some uint256) hsub)
  simpa [ExecFuncBody, locals] using ExecFuncBody.execBlockRevert hblock

theorem evalExpr_digsRad {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "rad" = some (.int (Int.ofNat (digsRad I).toNat))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "rad") =
      .ok (.int (Int.ofNat (digsRad I).toNat)) :=
  evalExpr_varUInt256 (v := v) (evm := evm) h

theorem evalExpr_digsDirtStorage {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hbase : locals.get? "Dirt" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage DirtRef) =
        .ok (.int (Int.ofNat (dogSlotWord ⟨5⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := DirtRef) (er := ({ base := "Dirt", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨5⟩)
    (value := .int (Int.ofNat (dogSlotWord ⟨5⟩ evm.accountMap evm.executionEnv).toNat))
    hbase
    (by simp [DirtRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm ⟨5⟩)

theorem evalExpr_digsIlkDirtStorage {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hsz68 : 68 ≤ I.calldata.size)
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (digsIlkValue I)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage (ilksF (.var "ilk") "dirt")) =
        .ok (.int (Int.ofNat
          (dogSlotWord (digsDirtSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  have hkeyLen : (digsIlkBytes I).length = bytes32Width.val + 1 :=
    digsIlkBytes_len hsz68
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "ilk") =
        .ok (digsIlkValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
      .ok (digsIlkValue I)
    rw [hilk]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "dirt") (er := digsDirtEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (digsDirtSlotFor I))
    (value := .int (Int.ofNat
      (dogSlotWord (digsDirtSlotFor I) evm.accountMap evm.executionEnv).toNat))
    hbase
    (by
      simp [digsDirtEvaledRef, digsIlkKey, digsIlkValue, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen, hvar])
    (by simp [digsIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, uint256St])
    (by rfl)
    (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm (digsDirtSlotFor I))

theorem assign_digsDirtStorage {v : DogImmutables} (evm : EVM.State)
    {locals : Store} (dirtNew : UInt256) (hbase : locals.get? "Dirt" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ dirtNew
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage DirtRef (.int (Int.ofNat dirtNew.toNat)) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  have hstore :
      storageLocStore evm (wordLoc ⟨5⟩) (.int (Int.ofNat dirtNew.toNat)) =
        some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨5⟩ dirtNew
  exact assignStorageRef_storage_scalar
    (er := ({ base := "Dirt", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (hbase := hbase)
    (her := by simp [DirtRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := hstore)

theorem assign_digsIlkDirtStorage {v : DogImmutables} (evm : EVM.State)
    {I : ExecutionEnv} {locals : Store} (hsz68 : 68 ≤ I.calldata.size)
    (ilkDirtNew : UInt256)
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (digsIlkValue I)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (digsDirtSlotFor I) ilkDirtNew
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage (ilksF (.var "ilk") "dirt") (.int (Int.ofNat ilkDirtNew.toNat)) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  have hkeyLen : (digsIlkBytes I).length = bytes32Width.val + 1 :=
    digsIlkBytes_len hsz68
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "ilk") =
        .ok (digsIlkValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
      .ok (digsIlkValue I)
    rw [hilk]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (digsDirtSlotFor I))
          (.int (Int.ofNat ilkDirtNew.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm (digsDirtSlotFor I) ilkDirtNew
  exact assignStorageRef_storage_scalar
    (er := digsDirtEvaledRef I)
    (ty := .elem (.int uint256Int)) (loc := wordLoc (digsDirtSlotFor I))
    (hbase := hbase)
    (her := by
      simp [digsDirtEvaledRef, digsIlkKey, digsIlkValue, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen, hvar])
    (hty := by simp [digsIlkKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, IlkStructTy, uint256St])
    (hloc := by rfl)
    (hstore := hstore)

theorem digsSuccessSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hDirtLe : (digsRad I).toNat ≤ (dogSlotWord ⟨5⟩ σ I).toNat)
    (hIlkLe :
      (digsRad I).toNat ≤
        (dogSlotWord (digsDirtSlotFor I)
          (sstoreAccountMap I.codeOwner σ ⟨5⟩
            (UInt256.sub (dogSlotWord ⟨5⟩ σ I) (digsRad I))) I).toNat) :
    let locals := digsLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let dirt0 := dogSlotWord ⟨5⟩ σ I
    let dirtNew := UInt256.sub dirt0 (digsRad I)
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ dirtNew
    let ilkDirt0 := dogSlotWord (digsDirtSlotFor I) evm1.accountMap evm1.executionEnv
    let ilkDirtNew := UInt256.sub ilkDirt0 (digsRad I)
    let evm2 := Solm.EVM.storageStore evm1 I.codeOwner (digsDirtSlotFor I) ilkDirtNew
    ExecTransitionBody (config v) (contract v) evm0 locals digsTransition.body
      (.returned
        (Frame.mk (contract v) (digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew))
        evm2 none) := by
  intro locals evm0 dirt0 dirtNew evm1 ilkDirt0 ilkDirtNew evm2
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, digsLocals]) hauth
  have hDirtExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt0.toNat)) := by
    simpa [evm0, initState, dirt0, dogSlotWord] using
      (evalExpr_digsDirtStorage (v := v) (evm := evm0) (locals := locals)
        (by simp [locals, digsLocals]))
  have hrad :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (digsRad I).toNat)) := by
    simpa [locals] using
      evalExpr_digsRad (v := v) (evm := evm0) (I := I) (locals := locals)
        (digsLocals_get_rad I)
  have hargs1 :
      evalExprs? (config v) { contract := contract v, locals := locals } evm0
        [.storage DirtRef, .var "rad"] =
          .ok [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] := by
    simp [evalExprs?, hDirtExpr, hrad, EvalResult.bind, bind, pure]
  have hbind1 :
      bindParams? subFunction.params
          [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] =
        some (uintBinaryLocals dirt0 (digsRad I)) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hcall1 :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew")
        (.ok { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm0) := by
    have hbody := execSubFunctionReturn (v := v) evm0 (x := dirt0) (y := digsRad I)
      (diff := dirtNew) (by simp [dirtNew]) (by simpa [dirt0] using hDirtLe)
    simpa [locals, digsLocalsDirtNew, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := { contract := contract v, locals := locals })
        (evm := evm0) (calleeEvm := evm0) (name := "sub") (retVar := "DirtNew")
        (args := [.storage DirtRef, .var "rad"])
        (argVals := [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)])
        (callee := subFunction) (locals := uintBinaryLocals dirt0 (digsRad I))
        (calleeSolm :=
          { contract := contract v, locals := uintBinaryLocalsZ dirt0 (digsRad I) dirtNew })
        (value := some [.int (Int.ofNat dirtNew.toNat)])
        hargs1 (by rfl) hbind1 hbody)
  have hDirtNew :
      evalExpr? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm0
          (.var "DirtNew") = .ok (.int (Int.ofNat dirtNew.toNat)) := by
    exact evalExpr_varUInt256 (v := v) (evm := evm0)
      (digsLocalsDirtNew_get_DirtNew I dirtNew)
  have hassign1 :
      assignStorageRef? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm0
          .storage DirtRef (.int (Int.ofNat dirtNew.toNat)) =
        .ok ({ contract := contract v, locals := digsLocalsDirtNew I dirtNew }, evm1) := by
    simpa [evm1] using
      assign_digsDirtStorage (v := v) evm0 (locals := digsLocalsDirtNew I dirtNew)
        dirtNew (by simp [digsLocalsDirtNew, digsLocals])
  have hassignStmt1 :
      ExecStmt (config v) { contract := contract v, locals := digsLocalsDirtNew I dirtNew }
        evm0 (.assign .storage DirtRef (.var "DirtNew"))
        (.ok { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1) :=
    ExecStmt.assign hDirtNew hassign1
  have hilk1 :
      (digsLocalsDirtNew I dirtNew).get? "ilk" = some (digsIlkValue I) :=
    digsLocalsDirtNew_get_ilk I dirtNew
  have hIlkDirtExpr :
      evalExpr? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1
          (.storage (ilksF (.var "ilk") "dirt")) =
        .ok (.int (Int.ofNat ilkDirt0.toNat)) := by
    simpa [ilkDirt0] using
      (evalExpr_digsIlkDirtStorage (v := v) (evm := evm1) (I := I)
        (locals := digsLocalsDirtNew I dirtNew) hsz68
        (by simp [digsLocalsDirtNew, digsLocals]) hilk1)
  have hrad1 :
      evalExpr? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1
          (.var "rad") = .ok (.int (Int.ofNat (digsRad I).toNat)) := by
    exact evalExpr_digsRad (v := v) (evm := evm1) (I := I)
      (locals := digsLocalsDirtNew I dirtNew) (digsLocalsDirtNew_get_rad I dirtNew)
  have hargs2 :
      evalExprs? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1
          [.storage (ilksF (.var "ilk") "dirt"), .var "rad"] =
        .ok [.int (Int.ofNat ilkDirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] := by
    simp [evalExprs?, hIlkDirtExpr, hrad1, EvalResult.bind, bind, pure]
  have hbind2 :
      bindParams? subFunction.params
          [.int (Int.ofNat ilkDirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] =
        some (uintBinaryLocals ilkDirt0 (digsRad I)) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hIlkLe' : (digsRad I).toNat ≤ ilkDirt0.toNat := by
    have hmap : evm1.accountMap = sstoreAccountMap I.codeOwner σ ⟨5⟩ dirtNew := by
      simpa [evm1, evm0, initState] using
        storageStore_accountMap evm0 I.codeOwner ⟨5⟩ dirtNew
    have henv : evm1.executionEnv = I := by
      simpa [evm1, evm0, initState] using
        storageStore_executionEnv evm0 I.codeOwner ⟨5⟩ dirtNew
    simpa [ilkDirt0, dogSlotWord, hmap, henv, dirtNew, dirt0] using hIlkLe
  have hcall2 :
      ExecStmt (config v) { contract := contract v, locals := digsLocalsDirtNew I dirtNew }
        evm1 (.internalCall "sub" [.storage (ilksF (.var "ilk") "dirt"), .var "rad"]
          "ilkDirtNew")
        (.ok (Frame.mk (contract v) (digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew))
          evm1) := by
    have hbody := execSubFunctionReturn (v := v) evm1 (x := ilkDirt0) (y := digsRad I)
      (diff := ilkDirtNew) (by simp [ilkDirtNew]) hIlkLe'
    simpa [digsLocalsDirtNewIlkDirtNew, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := contract v, locals := digsLocalsDirtNew I dirtNew })
        (evm := evm1) (calleeEvm := evm1) (name := "sub") (retVar := "ilkDirtNew")
        (args := [.storage (ilksF (.var "ilk") "dirt"), .var "rad"])
        (argVals := [.int (Int.ofNat ilkDirt0.toNat),
          .int (Int.ofNat (digsRad I).toNat)])
        (callee := subFunction) (locals := uintBinaryLocals ilkDirt0 (digsRad I))
        (calleeSolm :=
          { contract := contract v,
            locals := uintBinaryLocalsZ ilkDirt0 (digsRad I) ilkDirtNew })
        (value := some [.int (Int.ofNat ilkDirtNew.toNat)])
        hargs2 (by rfl) hbind2 hbody)
  have hIlkDirtNew :
      evalExpr? (config v)
          { contract := contract v,
            locals := digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew } evm1
          (.var "ilkDirtNew") = .ok (.int (Int.ofNat ilkDirtNew.toNat)) := by
    exact evalExpr_varUInt256 (v := v) (evm := evm1)
      (digsLocalsDirtNewIlkDirtNew_get_ilkDirtNew I dirtNew ilkDirtNew)
  have hassign2 :
      assignStorageRef? (config v)
          { contract := contract v,
            locals := digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew } evm1
          .storage (ilksF (.var "ilk") "dirt") (.int (Int.ofNat ilkDirtNew.toNat)) =
        .ok
          (Frame.mk (contract v) (digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew), evm2) := by
    simpa [evm2, evm1, evm0, initState, storageStore_executionEnv] using
      assign_digsIlkDirtStorage (v := v) evm1 (I := I)
        (locals := digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew) hsz68 ilkDirtNew
        (by simp [digsLocalsDirtNewIlkDirtNew, digsLocalsDirtNew, digsLocals])
        (digsLocalsDirtNewIlkDirtNew_get_ilk I dirtNew ilkDirtNew)
  have hassignStmt2 :
      ExecStmt (config v)
          { contract := contract v,
            locals := digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew } evm1
          (.assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew"))
          (.ok
            { contract := contract v,
              locals := digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew } evm2) :=
    ExecStmt.assign hIlkDirtNew hassign2
  have htail :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew",
          .assign .storage DirtRef (.var "DirtNew"),
          .internalCall "sub" [.storage (ilksF (.var "ilk") "dirt"), .var "rad"]
            "ilkDirtNew",
          .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ]
        (.ok
          { contract := contract v,
            locals := digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew } evm2) := by
    exact ExecBlock.consNormal hcall1 <|
      ExecBlock.consNormal hassignStmt1 <|
        ExecBlock.consNormal hcall2 <|
          ExecBlock.consNormal hassignStmt2 ExecBlock.nil
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        digsTransition.body
        (.ok
          { contract := contract v,
            locals := digsLocalsDirtNewIlkDirtNew I dirtNew ilkDirtNew } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact htail
  simpa [ExecTransitionBody, digsTransition, nonpayable, auth, evm0, evm1, evm2, locals,
    dirt0, dirtNew, ilkDirt0, ilkDirtNew] using ExecFuncBody.execBlockOK hblock

theorem digsFirstSubUnderflowSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hDirtLt : (dogSlotWord ⟨5⟩ σ I).toNat < (digsRad I).toNat) :
    let locals := digsLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals digsTransition.body .reverted := by
  intro locals evm0
  let dirt0 := dogSlotWord ⟨5⟩ σ I
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, digsLocals]) hauth
  have hDirtExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt0.toNat)) := by
    simpa [evm0, initState, dirt0, dogSlotWord] using
      (evalExpr_digsDirtStorage (v := v) (evm := evm0) (locals := locals)
        (by simp [locals, digsLocals]))
  have hrad :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (digsRad I).toNat)) := by
    simpa [locals] using
      evalExpr_digsRad (v := v) (evm := evm0) (I := I) (locals := locals)
        (digsLocals_get_rad I)
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := locals } evm0
        [.storage DirtRef, .var "rad"] =
          .ok [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] := by
    simp [evalExprs?, hDirtExpr, hrad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] =
        some (uintBinaryLocals dirt0 (digsRad I)) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hcall :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew") .reverted := by
    have hbody := execSubFunctionRevert (v := v) evm0 (x := dirt0) (y := digsRad I)
      (by simpa [dirt0] using hDirtLt)
    exact internalCallFunctionRevert
      (cfg := config v) (caller := { contract := contract v, locals := locals })
      (evm := evm0) (name := "sub") (retVar := "DirtNew")
      (args := [.storage DirtRef, .var "rad"])
      (argVals := [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)])
      (callee := subFunction) (locals := uintBinaryLocals dirt0 (digsRad I))
      hargs (by rfl) hbind hbody
  have htail :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew",
          .assign .storage DirtRef (.var "DirtNew"),
          .internalCall "sub" [.storage (ilksF (.var "ilk") "dirt"), .var "rad"]
            "ilkDirtNew",
          .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ]
        .reverted :=
    ExecBlock.consRevert hcall
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        digsTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact htail
  simpa [ExecTransitionBody, digsTransition, nonpayable, auth, evm0, locals] using
    ExecFuncBody.execBlockRevert hblock

theorem digsSecondSubUnderflowSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hDirtLe : (digsRad I).toNat ≤ (dogSlotWord ⟨5⟩ σ I).toNat)
    (hIlkLt :
      (dogSlotWord (digsDirtSlotFor I)
        (sstoreAccountMap I.codeOwner σ ⟨5⟩
          (UInt256.sub (dogSlotWord ⟨5⟩ σ I) (digsRad I))) I).toNat <
    (digsRad I).toNat) :
    let locals := digsLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals digsTransition.body .reverted := by
  intro locals evm0
  let dirt0 := dogSlotWord ⟨5⟩ σ I
  let dirtNew := UInt256.sub dirt0 (digsRad I)
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ dirtNew
  let ilkDirt0 := dogSlotWord (digsDirtSlotFor I) evm1.accountMap evm1.executionEnv
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, digsLocals]) hauth
  have hDirtExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt0.toNat)) := by
    simpa [evm0, initState, dirt0, dogSlotWord] using
      (evalExpr_digsDirtStorage (v := v) (evm := evm0) (locals := locals)
        (by simp [locals, digsLocals]))
  have hrad :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (digsRad I).toNat)) := by
    simpa [locals] using
      evalExpr_digsRad (v := v) (evm := evm0) (I := I) (locals := locals)
        (digsLocals_get_rad I)
  have hargs1 :
      evalExprs? (config v) { contract := contract v, locals := locals } evm0
        [.storage DirtRef, .var "rad"] =
          .ok [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] := by
    simp [evalExprs?, hDirtExpr, hrad, EvalResult.bind, bind, pure]
  have hbind1 :
      bindParams? subFunction.params
          [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] =
        some (uintBinaryLocals dirt0 (digsRad I)) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hcall1 :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew")
        (.ok { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm0) := by
    have hbody := execSubFunctionReturn (v := v) evm0 (x := dirt0) (y := digsRad I)
      (diff := dirtNew) (by simp [dirtNew]) (by simpa [dirt0] using hDirtLe)
    simpa [locals, digsLocalsDirtNew, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := { contract := contract v, locals := locals })
        (evm := evm0) (calleeEvm := evm0) (name := "sub") (retVar := "DirtNew")
        (args := [.storage DirtRef, .var "rad"])
        (argVals := [.int (Int.ofNat dirt0.toNat), .int (Int.ofNat (digsRad I).toNat)])
        (callee := subFunction) (locals := uintBinaryLocals dirt0 (digsRad I))
        (calleeSolm :=
          { contract := contract v, locals := uintBinaryLocalsZ dirt0 (digsRad I) dirtNew })
        (value := some [.int (Int.ofNat dirtNew.toNat)])
        hargs1 (by rfl) hbind1 hbody)
  have hDirtNew :
      evalExpr? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm0
          (.var "DirtNew") = .ok (.int (Int.ofNat dirtNew.toNat)) := by
    exact evalExpr_varUInt256 (v := v) (evm := evm0)
      (digsLocalsDirtNew_get_DirtNew I dirtNew)
  have hassign1 :
      assignStorageRef? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm0
          .storage DirtRef (.int (Int.ofNat dirtNew.toNat)) =
        .ok ({ contract := contract v, locals := digsLocalsDirtNew I dirtNew }, evm1) := by
    simpa [evm1] using
      assign_digsDirtStorage (v := v) evm0 (locals := digsLocalsDirtNew I dirtNew)
        dirtNew (by simp [digsLocalsDirtNew, digsLocals])
  have hassignStmt1 :
      ExecStmt (config v) { contract := contract v, locals := digsLocalsDirtNew I dirtNew }
        evm0 (.assign .storage DirtRef (.var "DirtNew"))
        (.ok { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1) :=
    ExecStmt.assign hDirtNew hassign1
  have hilk1 :
      (digsLocalsDirtNew I dirtNew).get? "ilk" = some (digsIlkValue I) :=
    digsLocalsDirtNew_get_ilk I dirtNew
  have hIlkDirtExpr :
      evalExpr? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1
          (.storage (ilksF (.var "ilk") "dirt")) =
        .ok (.int (Int.ofNat ilkDirt0.toNat)) := by
    simpa [ilkDirt0] using
      (evalExpr_digsIlkDirtStorage (v := v) (evm := evm1) (I := I)
        (locals := digsLocalsDirtNew I dirtNew) hsz68
        (by simp [digsLocalsDirtNew, digsLocals]) hilk1)
  have hrad1 :
      evalExpr? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1
          (.var "rad") = .ok (.int (Int.ofNat (digsRad I).toNat)) := by
    exact evalExpr_digsRad (v := v) (evm := evm1) (I := I)
      (locals := digsLocalsDirtNew I dirtNew) (digsLocalsDirtNew_get_rad I dirtNew)
  have hargs2 :
      evalExprs? (config v)
          { contract := contract v, locals := digsLocalsDirtNew I dirtNew } evm1
          [.storage (ilksF (.var "ilk") "dirt"), .var "rad"] =
        .ok [.int (Int.ofNat ilkDirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] := by
    simp [evalExprs?, hIlkDirtExpr, hrad1, EvalResult.bind, bind, pure]
  have hbind2 :
      bindParams? subFunction.params
          [.int (Int.ofNat ilkDirt0.toNat), .int (Int.ofNat (digsRad I).toNat)] =
        some (uintBinaryLocals ilkDirt0 (digsRad I)) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hIlkLt' : ilkDirt0.toNat < (digsRad I).toNat := by
    have hmap : evm1.accountMap = sstoreAccountMap I.codeOwner σ ⟨5⟩ dirtNew := by
      simpa [evm1, evm0, initState] using
        storageStore_accountMap evm0 I.codeOwner ⟨5⟩ dirtNew
    have henv : evm1.executionEnv = I := by
      simpa [evm1, evm0, initState] using
        storageStore_executionEnv evm0 I.codeOwner ⟨5⟩ dirtNew
    simpa [ilkDirt0, dogSlotWord, hmap, henv, dirtNew, dirt0] using hIlkLt
  have hcall2 :
      ExecStmt (config v) { contract := contract v, locals := digsLocalsDirtNew I dirtNew }
        evm1 (.internalCall "sub" [.storage (ilksF (.var "ilk") "dirt"), .var "rad"]
          "ilkDirtNew") .reverted := by
    have hbody := execSubFunctionRevert (v := v) evm1 (x := ilkDirt0) (y := digsRad I)
      hIlkLt'
    exact internalCallFunctionRevert
      (cfg := config v)
      (caller := { contract := contract v, locals := digsLocalsDirtNew I dirtNew })
      (evm := evm1) (name := "sub") (retVar := "ilkDirtNew")
      (args := [.storage (ilksF (.var "ilk") "dirt"), .var "rad"])
      (argVals := [.int (Int.ofNat ilkDirt0.toNat),
        .int (Int.ofNat (digsRad I).toNat)])
      (callee := subFunction) (locals := uintBinaryLocals ilkDirt0 (digsRad I))
      hargs2 (by rfl) hbind2 hbody
  have htail :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew",
          .assign .storage DirtRef (.var "DirtNew"),
          .internalCall "sub" [.storage (ilksF (.var "ilk") "dirt"), .var "rad"]
            "ilkDirtNew",
          .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ]
        .reverted := by
    exact ExecBlock.consNormal hcall1 <|
      ExecBlock.consNormal hassignStmt1 <|
        ExecBlock.consRevert hcall2
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        digsTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact htail
  simpa [ExecTransitionBody, digsTransition, nonpayable, auth, evm0, evm1, locals] using
    ExecFuncBody.execBlockRevert hblock

theorem dogReachDigsBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 6)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨550⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xc87193f4⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xc8 0x71 0x93 0xf4 ⟨0xc87193f4⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hhighTgt : armTgt code (⟨43⟩ : UInt256) = ⟨113⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h113 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [hhighTgt] using
      RD.selectorSplitTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh
        (by
          rw [hhighTgt]
          exact dogPatchedDJumpPrefix1405 ⟨113⟩ hpatch (by native_decide))
        (by simp)
  have h114 := h113.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_singleton]; omega)
  have hhole : UInt256.eq (dogSelectorWord 1) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h125 := by
    simpa [selArmNextPc] using
      h114.selectorArmNotTaken (selNat := dogSelectorWord 1) (tgt := (⟨504⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hhole
        (by simp)
  have hwards : UInt256.eq (dogSelectorWord 16) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h136 := by
    simpa [selArmNextPc] using
      h125.selectorArmNotTaken (selNat := dogSelectorWord 16) (tgt := (⟨512⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hwards
        (by simp)
  have hdigs : UInt256.eq (dogSelectorWord 6) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h550 := by
    simpa using
      h136.selectorArmTaken (selNat := dogSelectorWord 6) (tgt := (⟨550⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hdigs
        (dogPatchedDJumpPrefix1405 ⟨550⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h550⟩

theorem RD.dogDigsDecodeToRoutine {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret de sel : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨572⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J code 0).contains ⟨1936⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1936⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd573 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd574 := rd573.pop
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd575 := rd574.dup1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd576 := rd575.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd577 := rd576.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd579 := rd577.push1 ⟨32⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd580 := rd579.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd581 := rd580.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd584 := rd581.push2 ⟨1936⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd584.jump
        (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
        hroutine (by evm_ov)⟩

theorem RD.dogDigsToSwitch {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨550⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2025⟩
      (digsRad I :: digsIlkWord I :: ⟨313⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨550⟩) (ret := ⟨313⟩)
    (decoded := ⟨572⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨572⟩ hpatch (by native_decide)) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.dogDigsDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.dogAuthCheckOk
    (code := code) (pc := ⟨1936⟩) (okPc := ⟨2025⟩)
    (key := digsRad I) (ret := digsIlkWord I) (R := [⟨313⟩, sel])
    (by simpa [digsRad, digsIlkWord] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    hauth (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.dogDigsAuthRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨550⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨550⟩) (ret := ⟨313⟩)
    (decoded := ⟨572⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨572⟩ hpatch (by native_decide)) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.dogDigsDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  exact RD.dogAuthCheckRevert
    (code := code) (pc := ⟨1936⟩) (okPc := ⟨2025⟩)
    (key := digsRad I) (ret := digsIlkWord I) (R := [⟨313⟩, sel])
    (by simpa [digsRad, digsIlkWord] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (by
      unfold solcErrorStringRevertTailWf dogAuthTailPc dogNotAuthorizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    hauth (by simp)

@[reducible] def solcCheckedSubEmptyRevertWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  solcCheckedSubSuccessWf code pc okPc
  ∧ decode code (solcCheckedArithmeticRevertPc pc) =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) =
      some (.DUP1, .none)
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedSubEmptyRevertAnyWords {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedSubEmptyRevertWf code pc okPc)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hsub, hdRev0, hdRev2, hdRev3⟩
  rcases hsub with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  have rdRev := evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov)]
  exact RD.rev 0 rdRev hdRev3 (fun s _ hstk => memExpRevert0 s hstk) (by evm_ov)

theorem RD.dogDigsFirstSubUnderflow {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {rad ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2025⟩ (rad :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlt : (dogSlotWord ⟨5⟩ σ ee).toNat < rad.toNat)
    (hov : R.length + 13 ≤ 1024) :
    RDrev code g s0 := by
  let dirt := solcSlotWord σ ee ⟨5⟩
  have rd2026 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2029 := rd2026.push2 ⟨2037⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2031 := rd2029.push1 ⟨5⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  obtain ⟨_, _, rd2032Raw⟩ := rd2031.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2032 := by
    simpa [dirt, solcSlotWord] using rd2032Raw
  have rd2033 := rd2032.dup3
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2036 := rd2033.push2 ⟨4542⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd4542 := rd2036.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := code) (pc := ⟨4542⟩) (okPc := ⟨4558⟩)
    (a := dirt) (b := rad) (ret := ⟨2037⟩)
    (R := rad :: ilk :: ret :: sel :: R)
    rd4542
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (by simpa [dirt, dogSlotWord] using hlt)
    (by simp only [List.length_cons]; omega)

theorem RD.dogDigsToSecondSubRoutine {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {rad ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2025⟩ (rad :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hle : rad.toNat ≤ (dogSlotWord ⟨5⟩ σ ee).toNat)
    (hov : R.length + 13 ≤ 1024) :
    let dirt0 := dogSlotWord ⟨5⟩ σ ee
    let dirtNew := UInt256.sub dirt0 rad
    let σ1 := sstoreAccountMap ee.codeOwner σ ⟨5⟩ dirtNew
    let slot := ⟨3⟩ + solcMappingSlot ⟨1⟩ ilk
    let ilkDirt0 := dogSlotWord slot σ1 ee
    ∃ k' C', RD code ee g s0 ⟨4542⟩
      (rad :: ilkDirt0 :: ⟨2068⟩ :: rad :: ilk :: ret :: sel :: R)
      (twoWordHashMem ilk ⟨1⟩ mem) (UInt256.ofNat 3) rdata (cA, σ1) k' C' := by
  intro dirt0 dirtNew σ1 slot ilkDirt0
  have rd2026 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2029 := rd2026.push2 ⟨2037⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2031 := rd2029.push1 ⟨5⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  obtain ⟨_, _, rd2032Raw⟩ := rd2031.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2032 := by
    simpa [dirt0, dogSlotWord, solcSlotWord] using rd2032Raw
  have rd2033 := rd2032.dup3
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2036 := rd2033.push2 ⟨4542⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd4542First := rd2036.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by evm_ov)
  obtain ⟨_, _, rd2037⟩ := RD.solcCheckedSubSuccess
    (code := code) (pc := ⟨4542⟩) (okPc := ⟨4558⟩)
    (a := dirt0) (b := rad) (ret := ⟨2037⟩)
    (R := rad :: ilk :: ret :: sel :: R)
    rd4542First
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (by simpa [dirt0, dogSlotWord] using hle)
    (dogPatchedJumpDest hpatch (by native_decide))
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd2038 := rd2037.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2040 := rd2038.push1 ⟨5⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  obtain ⟨_, _, rd2041Raw⟩ := rd2040.sstore hperm
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2041 := by
    simpa [dirt0, dirtNew, σ1] using rd2041Raw
  have rdMstore0Prefix := evm_run rd2041 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem ilk mem)
    (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem ilk ⟨1⟩ mem)
    (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ ilk :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ ilk hmem
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨1⟩ ilk)
    (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hslot (by native_decide) (by evm_ov)
  have rdSlotPlus := evm_run rdSlot with [
    raw push1 ⟨3⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdLoadedRaw⟩ := rdSlotPlus.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdLoaded := by
    simpa [slot, ilkDirt0, dogSlotWord, solcSlotWord] using rdLoadedRaw
  have rdJump := evm_run rdLoaded with [
    raw push2 ⟨2068⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4542⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, rdJump.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by evm_ov)⟩

theorem RD.dogDigsSecondSubUnderflow {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {rad ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2025⟩ (rad :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hleDirt : rad.toNat ≤ (dogSlotWord ⟨5⟩ σ ee).toNat)
    (hIlkLt :
      (dogSlotWord (⟨3⟩ + solcMappingSlot ⟨1⟩ ilk)
        (sstoreAccountMap ee.codeOwner σ ⟨5⟩
          (UInt256.sub (dogSlotWord ⟨5⟩ σ ee) rad)) ee).toNat < rad.toNat)
    (hov : R.length + 13 ≤ 1024) :
    RDrev code g s0 := by
  let dirt0 := dogSlotWord ⟨5⟩ σ ee
  let dirtNew := UInt256.sub dirt0 rad
  let σ1 := sstoreAccountMap ee.codeOwner σ ⟨5⟩ dirtNew
  let slot := ⟨3⟩ + solcMappingSlot ⟨1⟩ ilk
  let ilkDirt0 := dogSlotWord slot σ1 ee
  obtain ⟨_, _, hsecond⟩ := RD.dogDigsToSecondSubRoutine
    (v := v) (code := code) (rad := rad) (ilk := ilk) (ret := ret) (sel := sel)
    (R := R) hpatch h hperm hmem hleDirt hov
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := code) (pc := ⟨4542⟩) (okPc := ⟨4558⟩)
    (a := ilkDirt0) (b := rad) (ret := ⟨2068⟩)
    (R := rad :: ilk :: ret :: sel :: R)
    (by simpa [dirt0, dirtNew, σ1, slot, ilkDirt0] using hsecond)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (by simpa [dirt0, dirtNew, σ1, slot, ilkDirt0] using hIlkLt)
    (by simp only [List.length_cons]; omega)

theorem RD.dogDigsSecondSubSuccessStoreLog {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {rad ilk ret sel ilkDirt0 : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨4542⟩
      (rad :: ilkDirt0 :: ⟨2068⟩ :: rad :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hle : rad.toNat ≤ ilkDirt0.toNat)
    (hov : R.length + 13 ≤ 1024) :
    let ilkDirtNew := UInt256.sub ilkDirt0 rad
    let slot := ⟨3⟩ + solcMappingSlot ⟨1⟩ ilk
    ∃ k' C', RD code ee g s0 ret (sel :: R)
      (writeWord (twoWordHashMem ilk ⟨1⟩ mem) 128 rad) (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ slot ilkDirtNew) k' C' := by
  intro ilkDirtNew slot
  obtain ⟨_, _, rd2068⟩ := RD.solcCheckedSubSuccess
    (code := code) (pc := ⟨4542⟩) (okPc := ⟨4558⟩)
    (a := ilkDirt0) (b := rad) (ret := ⟨2068⟩)
    (R := rad :: ilk :: ret :: sel :: R)
    h
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    hle
    (dogPatchedJumpDest hpatch (by native_decide))
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd2069 := rd2068.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdMstore0Prefix := evm_run rd2069 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem ilk mem)
    (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem ilk ⟨1⟩ mem)
    (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hhashSize : (twoWordHashMem ilk ⟨1⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨1⟩ hmem
  have hhashRead64 :
      (twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 ilk ⟨1⟩ hmem hread64
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ ilk :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ ilk hmem
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨1⟩ ilk)
    (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨3⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdAfterStoreRaw⟩ := rdBeforeStore.sstore hperm
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdAfterStore := by
    simpa [ilkDirtNew, slot] using rdAfterStoreRaw
  have rdMloadPrefix := evm_run rdAfterStore with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdMload := rdMloadPrefix.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (mloadFreePtrValue (by rw [hhashSize]; decide) (by decide) hhashRead64)
    (by native_decide) (by evm_ov)
  have rdMstorePrefix := evm_run rdMload with [
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdMstore := rdMstorePrefix.mstore 6
    (writeWord (twoWordHashMem ilk ⟨1⟩ mem) 128 rad) (UInt256.ofNat 5)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hread64' :
      (writeWord (twoWordHashMem ilk ⟨1⟩ mem) 128 rad).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    rw [writeWord_read_preserved (twoWordHashMem ilk ⟨1⟩ mem) 128 64 rad
      (by rw [hhashSize]; native_decide)
      (Or.inl ⟨by norm_num, by rw [hhashSize]⟩)]
    exact hhashRead64
  have rdMload2Prefix := rdMstore.swap1
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdMload2 := rdMload2Prefix.mload 0 ⟨128⟩ (UInt256.ofNat 5)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (mloadFreePtrValue
      (by
        have hsz := writeWord_size (twoWordHashMem ilk ⟨1⟩ mem) 128 rad
          (by rw [hhashSize]; native_decide)
        rw [hsz, hhashSize]
        decide)
      (by decide) hread64')
    (by native_decide) (by evm_ov)
  have rdTopicStack := evm_run rdMload2 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdTopic := rdTopicStack.pushConst dogDigsLogTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLogStack := evm_run rdTopic with [
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdLog := RD.log2 0 (UInt256.ofNat 5) rdLogStack
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hperm mem_cost (by native_decide) (by evm_ov)
  have rdPop1 := rdLog.pop
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdPop2 := rdPop1.pop
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  exact ⟨_, _, rdPop2.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hret
    (by evm_ov)⟩

theorem RD.dogDigsFirstSubUnderflowRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨550⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hDirtLt : (dogSlotWord ⟨5⟩ σ I).toNat < (digsRad I).toNat) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.dogDigsToSwitch hpatch hreach hsz68 hsize hauth
  exact RD.dogDigsFirstSubUnderflow
    (v := v) (code := code) (rad := digsRad I) (ilk := digsIlkWord I)
    (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hswitch hDirtLt (by simp)

theorem RD.dogDigsSecondSubUnderflowRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨550⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hDirtLe : (digsRad I).toNat ≤ (dogSlotWord ⟨5⟩ σ I).toNat)
    (hIlkLt :
      (dogSlotWord (⟨3⟩ + solcMappingSlot ⟨1⟩ (digsIlkWord I))
        (sstoreAccountMap I.codeOwner σ ⟨5⟩
          (UInt256.sub (dogSlotWord ⟨5⟩ σ I) (digsRad I))) I).toNat <
        (digsRad I).toNat) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.dogDigsToSwitch hpatch hreach hsz68 hsize hauth
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  exact RD.dogDigsSecondSubUnderflow
    (v := v) (code := code) (rad := digsRad I) (ilk := digsIlkWord I)
    (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hswitch hperm hmemAuth hDirtLe hIlkLt (by simp)

theorem RD.dogDigsSuccess {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨550⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hDirtLe : (digsRad I).toNat ≤ (dogSlotWord ⟨5⟩ σ I).toNat)
    (hIlkLe :
      (digsRad I).toNat ≤
        (dogSlotWord (⟨3⟩ + solcMappingSlot ⟨1⟩ (digsIlkWord I))
          (sstoreAccountMap I.codeOwner σ ⟨5⟩
            (UInt256.sub (dogSlotWord ⟨5⟩ σ I) (digsRad I))) I).toNat) :
    let dirt0 := dogSlotWord ⟨5⟩ σ I
    let dirtNew := UInt256.sub dirt0 (digsRad I)
    let σ1 := sstoreAccountMap I.codeOwner σ ⟨5⟩ dirtNew
    let slot := ⟨3⟩ + solcMappingSlot ⟨1⟩ (digsIlkWord I)
    let ilkDirt0 := dogSlotWord slot σ1 I
    let ilkDirtNew := UInt256.sub ilkDirt0 (digsRad I)
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ1 slot ilkDirtNew) ByteArray.empty := by
  intro dirt0 dirtNew σ1 slot ilkDirt0 ilkDirtNew
  obtain ⟨_, _, hswitch⟩ := RD.dogDigsToSwitch hpatch hreach hsz68 hsize hauth
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64Auth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, hsecond⟩ := RD.dogDigsToSecondSubRoutine
    (v := v) (code := code) (rad := digsRad I) (ilk := digsIlkWord I)
    (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hswitch hperm hmemAuth hDirtLe (by simp)
  have hmemSecond :
      (twoWordHashMem (digsIlkWord I) ⟨1⟩
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 96 :=
    twoWordHashMem_size_96 (digsIlkWord I) ⟨1⟩ hmemAuth
  have hread64Second :
      (twoWordHashMem (digsIlkWord I) ⟨1⟩
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (digsIlkWord I) ⟨1⟩ hmemAuth hread64Auth
  obtain ⟨_, _, hretPc⟩ := RD.dogDigsSecondSubSuccessStoreLog
    (v := v) (code := code) (rad := digsRad I) (ilk := digsIlkWord I)
    (ret := ⟨313⟩) (sel := sel) (ilkDirt0 := ilkDirt0) (R := [])
    hpatch
    (by simpa [dirt0, dirtNew, σ1, slot, ilkDirt0] using hsecond)
    (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by native_decide))
    hperm hmemSecond hread64Second
    (by simpa [dirt0, dirtNew, σ1, slot, ilkDirt0] using hIlkLe)
    (by simp)
  have hretPc' := hretPc.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
      native_decide)
    (by evm_ov)
  exact RD.stop hretPc'
    (by
      change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
      rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_singleton]; omega)

theorem dogDigsBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some digsTransition :=
    dogDispatchDigs hsel
  have hreach := dogReachDigsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · let rad := digsRad I
    let callerSlot := dogCallerWardsSlot I
    let actualSlot := ⟨3⟩ + solcMappingSlot ⟨1⟩ (digsIlkWord I)
    let sourceSlot := digsDirtSlotFor I
    let locals := digsLocals I
    have hdecode :
        decodeCalldataWithMode (config v).abiDecodeMode
          (digsTransition.params.map Param.name)
          (transitionSignature digsTransition).paramTypes I.calldata =
            some locals := by
      simpa [locals] using dogDecode_digs_ok (v := v) hsz68
    have hslotEq : actualSlot = sourceSlot := by
      simp [actualSlot, sourceSlot, digsDirtSlotFor_eq hsz68, u256_add_comm]
    have hcallerWord :
        dogSlotWord callerSlot σ_evm I = dogSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have hDirtWord :
        dogSlotWord ⟨5⟩ σ_evm I = dogSlotWord ⟨5⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
    have henc : returnEquiv ByteArray.empty none digsTransition.returnType := by
      rw [show digsTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    by_cases hauthEvm : dogSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : dogSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
      by_cases hDirtLtEvm : (dogSlotWord ⟨5⟩ σ_evm I).toNat < rad.toNat
      · have hDirtLtSolm : (dogSlotWord ⟨5⟩ σ_solm I).toNat < rad.toNat := by
          rw [← hDirtWord]
          exact hDirtLtEvm
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody (config v) (contract v) evm0 locals digsTransition.body
              .reverted := by
          simpa [evm0, locals, rad] using
            (digsFirstSubUnderflowSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hDirtLtSolm)
        have hrev := RD.dogDigsFirstSubUnderflowRevert
          hpatch hreach hsz68 hsize hauthSolc (by simpa [rad] using hDirtLtEvm)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hDirtLeEvm : rad.toNat ≤ (dogSlotWord ⟨5⟩ σ_evm I).toNat := by
          exact Nat.le_of_not_gt hDirtLtEvm
        have hDirtLeSolm : rad.toNat ≤ (dogSlotWord ⟨5⟩ σ_solm I).toNat := by
          rw [← hDirtWord]
          exact hDirtLeEvm
        let dirtNewEvm := UInt256.sub (dogSlotWord ⟨5⟩ σ_evm I) rad
        let dirtNewSolm := UInt256.sub (dogSlotWord ⟨5⟩ σ_solm I) rad
        let σ1_evm := sstoreAccountMap I.codeOwner σ_evm ⟨5⟩ dirtNewEvm
        let σ1_solm := sstoreAccountMap I.codeOwner σ_solm ⟨5⟩ dirtNewSolm
        have hdirtNewEq : dirtNewEvm = dirtNewSolm := by
          simp [dirtNewEvm, dirtNewSolm, hDirtWord]
        have hAccounts1 : accountMapEquiv σ1_evm σ1_solm := by
          simpa [σ1_evm, σ1_solm, dirtNewEvm, dirtNewSolm, hDirtWord] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ dirtNewEvm hAccounts
        have hIlkWord :
            dogSlotWord actualSlot σ1_evm I = dogSlotWord sourceSlot σ1_solm I := by
          rw [hslotEq]
          exact accountMapEquiv_storage_findD hAccounts1 I.codeOwner sourceSlot ⟨0⟩
        by_cases hIlkLtEvm : (dogSlotWord actualSlot σ1_evm I).toNat < rad.toNat
        · have hIlkLtSolm : (dogSlotWord sourceSlot σ1_solm I).toNat < rad.toNat := by
            rw [← hIlkWord]
            exact hIlkLtEvm
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hbody :
              ExecTransitionBody (config v) (contract v) evm0 locals digsTransition.body
                .reverted := by
            simpa [evm0, locals, rad, sourceSlot, σ1_solm, dirtNewSolm] using
              (digsSecondSubUnderflowSourceBody (v := v) (cA := cA) (gh := gh)
                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hsz68 hauthSolm (by simpa [rad] using hDirtLeSolm)
                (by simpa [rad, sourceSlot, σ1_solm, dirtNewSolm] using hIlkLtSolm))
          have hrev := RD.dogDigsSecondSubUnderflowRevert
            hpatch hreach hperm hsz68 hsize hauthSolc
            (by simpa [rad] using hDirtLeEvm)
            (by simpa [rad, actualSlot, σ1_evm, dirtNewEvm] using hIlkLtEvm)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hIlkLeEvm : rad.toNat ≤ (dogSlotWord actualSlot σ1_evm I).toNat := by
            exact Nat.le_of_not_gt hIlkLtEvm
          have hIlkLeSolm : rad.toNat ≤ (dogSlotWord sourceSlot σ1_solm I).toNat := by
            rw [← hIlkWord]
            exact hIlkLeEvm
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ dirtNewSolm
          let ilkDirt0Solm := dogSlotWord sourceSlot evm1.accountMap evm1.executionEnv
          let ilkDirtNewSolm := UInt256.sub ilkDirt0Solm rad
          let evm2 := Solm.EVM.storageStore evm1 I.codeOwner sourceSlot ilkDirtNewSolm
          have hbody :
              ExecTransitionBody (config v) (contract v) evm0 locals digsTransition.body
                (.returned
                  (Frame.mk (contract v)
                    (digsLocalsDirtNewIlkDirtNew I dirtNewSolm ilkDirtNewSolm))
                  evm2 none) := by
            simpa [evm0, evm1, evm2, locals, rad, sourceSlot, dirtNewSolm,
              ilkDirt0Solm, ilkDirtNewSolm] using
              (digsSuccessSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hsz68 hauthSolm (by simpa [rad] using hDirtLeSolm)
                (by simpa [rad, sourceSlot, σ1_solm, dirtNewSolm] using hIlkLeSolm))
          have hret := RD.dogDigsSuccess
            hpatch hreach hperm hsz68 hsize hauthSolc
            (by simpa [rad] using hDirtLeEvm)
            (by simpa [rad, actualSlot, σ1_evm, dirtNewEvm] using hIlkLeEvm)
          have hcreated :
              (cA,
                sstoreAccountMap I.codeOwner σ1_evm actualSlot
                  (UInt256.sub (dogSlotWord actualSlot σ1_evm I) rad)).1 =
                evm2.createdAccounts := by
            simp [evm2, evm1, evm0, initState, storageStore_createdAccounts]
          have hIlkNewEq :
              UInt256.sub (dogSlotWord actualSlot σ1_evm I) rad =
                UInt256.sub (dogSlotWord sourceSlot σ1_solm I) rad := by
            rw [hIlkWord]
          have haccountsBase :
              accountMapEquiv
                (sstoreAccountMap I.codeOwner σ1_evm sourceSlot
                  (UInt256.sub (dogSlotWord actualSlot σ1_evm I) rad))
                (sstoreAccountMap I.codeOwner σ1_solm sourceSlot
                  (UInt256.sub (dogSlotWord sourceSlot σ1_solm I) rad)) := by
            rw [hIlkWord]
            exact accountMapEquiv_sstoreAccountMap I.codeOwner sourceSlot
              (UInt256.sub (dogSlotWord sourceSlot σ1_solm I) rad) hAccounts1
          have haccounts :
              accountMapEquiv
                (sstoreAccountMap I.codeOwner σ1_evm actualSlot
                  (UInt256.sub (dogSlotWord actualSlot σ1_evm I) rad))
                evm2.accountMap := by
            simpa [evm2, evm1, evm0, initState, storageStore_accountMap,
              storageStore_executionEnv, actualSlot, sourceSlot, hslotEq, hIlkWord,
              σ1_solm, ilkDirt0Solm, ilkDirtNewSolm] using haccountsBase
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            hcreated haccounts henc
    · have hauthSolm : dogSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evm0 locals digsTransition.body
            .reverted := by
        have hguard := dogAuthGuardEval_false (v := v) (cA := cA) (gh := gh)
          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals, digsLocals]) hauthSolm
        have hblock := nonpayableSecondRequireReverts
          (cfg := config v) (solm := { contract := contract v, locals := locals })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest := [
            .internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew",
            .assign .storage DirtRef (.var "DirtNew"),
            .internalCall "sub" [.storage (ilksF (.var "ilk") "dirt"), .var "rad"]
              "ilkDirtNew",
            .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, digsTransition, nonpayable, auth, evm0, locals] using
          ExecFuncBody.execBlockRevert hblock
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
      have hrev := RD.dogDigsAuthRevert hpatch hreach hsz68 hsize hauthSolc
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hlt :
        UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
      change I.calldata.size - 4 < 64
      omega
    have hrev := RD.solcExternalStaticArgsShortReverts
      (code := code) (sel := solcSelectorWord I) (entry := ⟨550⟩) (ret := ⟨313⟩)
      (decoded := ⟨572⟩) (need := ⟨64⟩) hreach
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      hlt
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (dogDecode_digs_none_short (v := v) hsz4 hshort)

end Benchmarks.Dss.Dog

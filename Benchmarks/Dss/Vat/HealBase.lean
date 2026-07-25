import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vat

/-! ## `heal(uint256)` -/

abbrev healRad (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev healLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "rad" (.int (Int.ofNat (healRad I).toNat))

abbrev healLocalsSinNew (I : ExecutionEnv) (sinNew : UInt256) : Store :=
  (healLocals I).insert "sinNew" (.int (Int.ofNat sinNew.toNat))

abbrev healLocalsDaiNew (I : ExecutionEnv) (sinNew daiNew : UInt256) : Store :=
  (healLocalsSinNew I sinNew).insert "daiNew" (.int (Int.ofNat daiNew.toNat))

abbrev healLocalsViceNew (I : ExecutionEnv)
    (sinNew daiNew viceNew : UInt256) : Store :=
  (healLocalsDaiNew I sinNew daiNew).insert "viceNew" (.int (Int.ofNat viceNew.toNat))

abbrev healLocalsDebtNew (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) : Store :=
  (healLocalsViceNew I sinNew daiNew viceNew).insert "debtNew"
    (.int (Int.ofNat debtNew.toNat))

theorem healLocals_get_rad (I : ExecutionEnv) :
    (healLocals I).get? "rad" = some (.int (Int.ofNat (healRad I).toNat)) := by
  simp [healLocals]

theorem healLocalsSinNew_get_rad (I : ExecutionEnv) (sinNew : UInt256) :
    (healLocalsSinNew I sinNew).get? "rad" =
      some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocalsSinNew, store_get_ne _ _ (by decide), healLocals_get_rad]

theorem healLocalsDaiNew_get_rad (I : ExecutionEnv) (sinNew daiNew : UInt256) :
    (healLocalsDaiNew I sinNew daiNew).get? "rad" =
      some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocalsDaiNew, store_get_ne _ _ (by decide), healLocalsSinNew_get_rad]

theorem healLocalsViceNew_get_rad (I : ExecutionEnv)
    (sinNew daiNew viceNew : UInt256) :
    (healLocalsViceNew I sinNew daiNew viceNew).get? "rad" =
      some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocalsViceNew, store_get_ne _ _ (by decide), healLocalsDaiNew_get_rad]

theorem healLocalsDebtNew_get_rad (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) :
    (healLocalsDebtNew I sinNew daiNew viceNew debtNew).get? "rad" =
      some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocalsDebtNew, store_get_ne _ _ (by decide), healLocalsViceNew_get_rad]

theorem healLocalsSinNew_get_sinNew (I : ExecutionEnv) (sinNew : UInt256) :
    (healLocalsSinNew I sinNew).get? "sinNew" =
      some (.int (Int.ofNat sinNew.toNat)) := by
  simp [healLocalsSinNew]

theorem healLocalsDaiNew_get_daiNew (I : ExecutionEnv) (sinNew daiNew : UInt256) :
    (healLocalsDaiNew I sinNew daiNew).get? "daiNew" =
      some (.int (Int.ofNat daiNew.toNat)) := by
  simp [healLocalsDaiNew]

theorem healLocalsViceNew_get_viceNew (I : ExecutionEnv)
    (sinNew daiNew viceNew : UInt256) :
    (healLocalsViceNew I sinNew daiNew viceNew).get? "viceNew" =
      some (.int (Int.ofNat viceNew.toNat)) := by
  simp [healLocalsViceNew]

theorem healLocalsDebtNew_get_debtNew (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) :
    (healLocalsDebtNew I sinNew daiNew viceNew debtNew).get? "debtNew" =
      some (.int (Int.ofNat debtNew.toNat)) := by
  simp [healLocalsDebtNew]

theorem healLocalsDebtNew_get_viceNew (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) :
    (healLocalsDebtNew I sinNew daiNew viceNew debtNew).get? "viceNew" =
      some (.int (Int.ofNat viceNew.toNat)) := by
  rw [healLocalsDebtNew, store_get_ne _ _ (by decide), healLocalsViceNew_get_viceNew]

theorem healLocalsDebtNew_get_daiNew (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) :
    (healLocalsDebtNew I sinNew daiNew viceNew debtNew).get? "daiNew" =
      some (.int (Int.ofNat daiNew.toNat)) := by
  rw [healLocalsDebtNew, store_get_ne _ _ (by decide)]
  rw [healLocalsViceNew, store_get_ne _ _ (by decide), healLocalsDaiNew_get_daiNew]

theorem healLocalsDebtNew_get_sinNew (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) :
    (healLocalsDebtNew I sinNew daiNew viceNew debtNew).get? "sinNew" =
      some (.int (Int.ofNat sinNew.toNat)) := by
  rw [healLocalsDebtNew, store_get_ne _ _ (by decide)]
  rw [healLocalsViceNew, store_get_ne _ _ (by decide)]
  rw [healLocalsDaiNew, store_get_ne _ _ (by decide), healLocalsSinNew_get_sinNew]

theorem vatEvalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem vatEvalExpr_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
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
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem vatEvalExpr_sub256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) = .revert := by
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro hle
  exact False.elim (not_le.mpr hlt hle)

theorem vatEvalExpr_le_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hle

theorem vatEvalExpr_le_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : b.toNat < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hlt

abbrev healSourceKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev healSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev healSinEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sin", steps := [.mindex (healSourceKey I)] }

abbrev healDaiEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "dai", steps := [.mindex (healSourceKey I)] }

abbrev healViceEvaledRef : EvaledStorageRef :=
  { base := "vice", steps := [] }

abbrev healDebtEvaledRef : EvaledStorageRef :=
  { base := "debt", steps := [] }

abbrev healSinSlot (I : ExecutionEnv) : UInt256 :=
  sinSlot (healSourceKey I)

abbrev healDaiSlot (I : ExecutionEnv) : UInt256 :=
  daiSlot (healSourceKey I)

abbrev healViceSlot : UInt256 :=
  ⟨8⟩

abbrev healDebtSlot : UInt256 :=
  ⟨7⟩

def healPostState (evm : EVM.State) (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew)
        evm.executionEnv.codeOwner (healDaiSlot I) daiNew)
      evm.executionEnv.codeOwner healViceSlot viceNew)
    evm.executionEnv.codeOwner healDebtSlot debtNew

abbrev healBodyTail : List Stmt :=
  checkedSubUintInto "sinNew" (.storage (sinRef sender)) (.var "rad") ++
  [ .assign .storage (sinRef sender) (.var "sinNew") ] ++
  checkedSubUintInto "daiNew" (.storage (daiRef sender)) (.var "rad") ++
  [ .assign .storage (daiRef sender) (.var "daiNew") ] ++
  checkedSubUintInto "viceNew" (.storage viceRef) (.var "rad") ++
  [ .assign .storage viceRef (.var "viceNew") ] ++
  checkedSubUintInto "debtNew" (.storage debtRef) (.var "rad") ++
  [ .assign .storage debtRef (.var "debtNew") ]

theorem healSourceWord_toNat (I : ExecutionEnv) :
    (healSourceWord I).toNat = I.source.val := by
  unfold healSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem healSinSlot_eq_mapSlot (I : ExecutionEnv) :
    healSinSlot I = solcMappingSlot ⟨6⟩ (healSourceWord I) := by
  unfold healSinSlot healSourceKey healSourceWord sinSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address]

theorem healDaiSlot_eq_mapSlot (I : ExecutionEnv) :
    healDaiSlot I = solcMappingSlot ⟨5⟩ (healSourceWord I) := by
  unfold healDaiSlot healSourceKey healSourceWord daiSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address]

set_option maxHeartbeats 800000 in
theorem wordAt32Mem_solcMappingSlot_of_read0 {mem : ByteArray} (key baseSlot : UInt256)
    (hmem : mem.size = 96)
    (hread0 : mem.readWithPadding 0 32 = UInt256.toByteArray key) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt32Mem baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  have hmem32 : (wordAt32Mem baseSlot mem).size = 96 :=
    wordAt32Mem_size_96 baseSlot hmem
  have hread :
      (wordAt32Mem baseSlot mem).readWithPadding 0 64 =
        UInt256.toByteArray key ++ UInt256.toByteArray baseSlot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hmem32]; omega)]
    have hleft :
        (wordAt32Mem baseSlot mem).extract 0 32 = UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0 (by rw [hmem32]; omega)]
      unfold wordAt32Mem
      rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
        (by rw [hmem]; omega) (by omega)]
      rw [hread0]
    have hright :
        (wordAt32Mem baseSlot mem).extract 32 64 = UInt256.toByteArray baseSlot := by
      rw [← readWithPadding_eq_extract _ 32 (by rw [hmem32]; omega)]
      unfold wordAt32Mem
      rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray baseSlot).size ≤ 32
        rw [toByteArray_size])
    rw [show (wordAt32Mem baseSlot mem).extract 0 64 =
        (wordAt32Mem baseSlot mem).extract 0 32 ++
          (wordAt32Mem baseSlot mem).extract 32 64 by
        rw [ByteArray.extract_append_extract]
        norm_num]
    rw [hleft, hright]
  rw [hread]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem evalStorageRef_heal_sin_sender (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := locals } evm (sinRef sender) =
      .ok (healSinEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, sinRef, sender, envValue,
    healSinEvaledRef, healSourceKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_heal_dai_sender (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := locals } evm (daiRef sender) =
      .ok (healDaiEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, daiRef, sender, envValue,
    healDaiEvaledRef, healSourceKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_heal_vice (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm viceRef =
      .ok healViceEvaledRef := by
  simp [evalStorageRef, evalStorageRefSteps, viceRef, healViceEvaledRef,
    EvalResult.bind, pure, bind]

theorem evalStorageRef_heal_debt (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm debtRef =
      .ok healDebtEvaledRef := by
  simp [evalStorageRef, evalStorageRefSteps, debtRef, healDebtEvaledRef,
    EvalResult.bind, pure, bind]

theorem vatEvalExpr_heal_sin_sender (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hbase : locals.get? "sin" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (sinRef sender)) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (healSinSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_heal_sin_sender evm I locals hsrc)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (healSinSlot I))

theorem vatEvalExpr_heal_dai_sender (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hsrc : evm.executionEnv.source = I.source)
    (hbase : locals.get? "dai" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (daiRef sender)) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (healDaiSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_heal_dai_sender evm I locals hsrc)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (healDaiSlot I))

theorem vatEvalExpr_heal_vice (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vice" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage viceRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        healViceSlot).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_heal_vice evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm healViceSlot)

theorem vatEvalExpr_heal_debt (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "debt" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage debtRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        healDebtSlot).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_heal_debt evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm healDebtSlot)

theorem assign_heal_sin_sender (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (sinNew : UInt256)
    (hsrc : evm.executionEnv.source = I.source)
    (hbase : locals.get? "sin" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (sinRef sender) (.int (Int.ofNat sinNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (healSinSlot I))
    (hbase := hbase)
    (her := evalStorageRef_heal_sin_sender evm I locals hsrc)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm (healSinSlot I) sinNew)

theorem assign_heal_dai_sender (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (daiNew : UInt256)
    (hsrc : evm.executionEnv.source = I.source)
    (hbase : locals.get? "dai" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healDaiSlot I) daiNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (daiRef sender) (.int (Int.ofNat daiNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (healDaiSlot I))
    (hbase := hbase)
    (her := evalStorageRef_heal_dai_sender evm I locals hsrc)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm (healDaiSlot I) daiNew)

theorem assign_heal_vice (evm : EVM.State) (locals : Store) (viceNew : UInt256)
    (hbase : locals.get? "vice" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner healViceSlot viceNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage viceRef (.int (Int.ofNat viceNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc healViceSlot)
    (hbase := hbase)
    (her := evalStorageRef_heal_vice evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm healViceSlot viceNew)

theorem assign_heal_debt (evm : EVM.State) (locals : Store) (debtNew : UInt256)
    (hbase : locals.get? "debt" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner healDebtSlot debtNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc healDebtSlot)
    (hbase := hbase)
    (her := evalStorageRef_heal_debt evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm healDebtSlot debtNew)

theorem vatHealSinSubBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinVal sinNew : UInt256}
    (hsrc : evm.executionEnv.source = I.source)
    (hsinLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I) = sinVal)
    (hsinNew : sinNew = UInt256.sub sinVal (healRad I))
    (hsinEnough : (healRad I).toNat ≤ sinVal.toNat) :
    ExecBlock config { contract := contract, locals := healLocals I } evm
      (checkedSubUintInto "sinNew" (.storage (sinRef sender)) (.var "rad"))
      (.ok { contract := contract, locals := healLocalsSinNew I sinNew } evm) := by
  have hrad :
      evalExpr? config { contract := contract, locals := healLocals I } evm (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocals I) (name := "rad")
      (value := healRad I) (healLocals_get_rad I)
  have hsin :
      evalExpr? config { contract := contract, locals := healLocals I } evm
          (.storage (sinRef sender)) =
        .ok (.int (Int.ofNat sinVal.toNat)) := by
    simpa [hsinLoad] using
      vatEvalExpr_heal_sin_sender evm I (healLocals I) hsrc (by simp [healLocals])
  have hsub :
      evalExpr? config { contract := contract, locals := healLocals I } evm
          (sub256 (.storage (sinRef sender)) (.var "rad")) =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    vatEvalExpr_sub256_ok hsin hrad hsinNew hsinEnough
  have hsinNewEval :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocalsSinNew I sinNew)
      (name := "sinNew") (value := sinNew) (healLocalsSinNew_get_sinNew I sinNew)
  have hsinAgain :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (.storage (sinRef sender)) =
        .ok (.int (Int.ofNat sinVal.toNat)) := by
    simpa [hsinLoad] using
      vatEvalExpr_heal_sin_sender evm I (healLocalsSinNew I sinNew) hsrc
        (by simp [healLocalsSinNew, healLocals])
  have hreq :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (.binary .le (.var "sinNew") (.storage (sinRef sender))) =
        .ok (.bool true) := by
    have hsinNewNat : sinNew.toNat = sinVal.toNat - (healRad I).toNat := by
      rw [hsinNew, usub_toNat hsinEnough]
    exact vatEvalExpr_le_uint256_true hsinNewEval hsinAgain (by rw [hsinNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatHealDaiSubBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiVal daiNew : UInt256}
    (hsrc : evm.executionEnv.source = I.source)
    (hdaiLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healDaiSlot I) = daiVal)
    (hdaiNew : daiNew = UInt256.sub daiVal (healRad I))
    (hdaiEnough : (healRad I).toNat ≤ daiVal.toNat) :
    ExecBlock config { contract := contract, locals := healLocalsSinNew I sinNew } evm
      (checkedSubUintInto "daiNew" (.storage (daiRef sender)) (.var "rad"))
      (.ok { contract := contract, locals := healLocalsDaiNew I sinNew daiNew } evm) := by
  have hrad :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocalsSinNew I sinNew)
      (name := "rad") (value := healRad I) (healLocalsSinNew_get_rad I sinNew)
  have hdai :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (.storage (daiRef sender)) =
        .ok (.int (Int.ofNat daiVal.toNat)) := by
    simpa [hdaiLoad] using
      vatEvalExpr_heal_dai_sender evm I (healLocalsSinNew I sinNew) hsrc
        (by simp [healLocalsSinNew, healLocals])
  have hsub :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (sub256 (.storage (daiRef sender)) (.var "rad")) =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    vatEvalExpr_sub256_ok hdai hrad hdaiNew hdaiEnough
  have hdaiNewEval :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (.var "daiNew") =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocalsDaiNew I sinNew daiNew)
      (name := "daiNew") (value := daiNew) (healLocalsDaiNew_get_daiNew I sinNew daiNew)
  have hdaiAgain :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (.storage (daiRef sender)) =
        .ok (.int (Int.ofNat daiVal.toNat)) := by
    simpa [hdaiLoad] using
      vatEvalExpr_heal_dai_sender evm I (healLocalsDaiNew I sinNew daiNew) hsrc
        (by simp [healLocalsDaiNew, healLocalsSinNew, healLocals])
  have hreq :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (.binary .le (.var "daiNew") (.storage (daiRef sender))) =
        .ok (.bool true) := by
    have hdaiNewNat : daiNew.toNat = daiVal.toNat - (healRad I).toNat := by
      rw [hdaiNew, usub_toNat hdaiEnough]
    exact vatEvalExpr_le_uint256_true hdaiNewEval hdaiAgain (by rw [hdaiNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatHealViceSubBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceVal viceNew : UInt256}
    (hviceLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner healViceSlot = viceVal)
    (hviceNew : viceNew = UInt256.sub viceVal (healRad I))
    (hviceEnough : (healRad I).toNat ≤ viceVal.toNat) :
    ExecBlock config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew } evm
      (checkedSubUintInto "viceNew" (.storage viceRef) (.var "rad"))
      (.ok { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm) := by
  have hrad :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocalsDaiNew I sinNew daiNew)
      (name := "rad") (value := healRad I) (healLocalsDaiNew_get_rad I sinNew daiNew)
  have hvice :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceVal.toNat)) := by
    simpa [hviceLoad] using
      vatEvalExpr_heal_vice evm (healLocalsDaiNew I sinNew daiNew)
        (by simp [healLocalsDaiNew, healLocalsSinNew, healLocals])
  have hsub :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (sub256 (.storage viceRef) (.var "rad")) =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    vatEvalExpr_sub256_ok hvice hrad hviceNew hviceEnough
  have hviceNewEval :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := healLocalsViceNew I sinNew daiNew viceNew) (name := "viceNew")
      (value := viceNew) (healLocalsViceNew_get_viceNew I sinNew daiNew viceNew)
  have hviceAgain :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (.storage viceRef) =
        .ok (.int (Int.ofNat viceVal.toNat)) := by
    simpa [hviceLoad] using
      vatEvalExpr_heal_vice evm (healLocalsViceNew I sinNew daiNew viceNew)
        (by simp [healLocalsViceNew, healLocalsDaiNew, healLocalsSinNew, healLocals])
  have hreq :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (.binary .le (.var "viceNew") (.storage viceRef)) =
        .ok (.bool true) := by
    have hviceNewNat : viceNew.toNat = viceVal.toNat - (healRad I).toNat := by
      rw [hviceNew, usub_toNat hviceEnough]
    exact vatEvalExpr_le_uint256_true hviceNewEval hviceAgain (by rw [hviceNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatHealDebtSubBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew debtVal debtNew : UInt256}
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner healDebtSlot = debtVal)
    (hdebtNew : debtNew = UInt256.sub debtVal (healRad I))
    (hdebtEnough : (healRad I).toNat ≤ debtVal.toNat) :
    ExecBlock config { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew }
        evm
      (checkedSubUintInto "debtNew" (.storage debtRef) (.var "rad"))
      (.ok { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
        evm) := by
  have hrad :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := healLocalsViceNew I sinNew daiNew viceNew) (name := "rad")
      (value := healRad I) (healLocalsViceNew_get_rad I sinNew daiNew viceNew)
  have hdebt :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (.storage debtRef) =
        .ok (.int (Int.ofNat debtVal.toNat)) := by
    simpa [hdebtLoad] using
      vatEvalExpr_heal_debt evm (healLocalsViceNew I sinNew daiNew viceNew)
        (by simp [healLocalsViceNew, healLocalsDaiNew, healLocalsSinNew, healLocals])
  have hsub :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (sub256 (.storage debtRef) (.var "rad")) =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_sub256_ok hdebt hrad hdebtNew hdebtEnough
  have hdebtNewEval :
      evalExpr? config
          { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew) (name := "debtNew")
      (value := debtNew) (healLocalsDebtNew_get_debtNew I sinNew daiNew viceNew debtNew)
  have hdebtAgain :
      evalExpr? config
          { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtVal.toNat)) := by
    simpa [hdebtLoad] using
      vatEvalExpr_heal_debt evm (healLocalsDebtNew I sinNew daiNew viceNew debtNew)
        (by simp [healLocalsDebtNew, healLocalsViceNew, healLocalsDaiNew,
          healLocalsSinNew, healLocals])
  have hreq :
      evalExpr? config
          { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          evm (.binary .le (.var "debtNew") (.storage debtRef)) =
        .ok (.bool true) := by
    have hdebtNewNat : debtNew.toNat = debtVal.toNat - (healRad I).toNat := by
      rw [hdebtNew, usub_toNat hdebtEnough]
    exact vatEvalExpr_le_uint256_true hdebtNewEval hdebtAgain (by rw [hdebtNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatHealSinSubBlockRevert (evm : EVM.State) (I : ExecutionEnv)
    {sinVal : UInt256}
    (hsrc : evm.executionEnv.source = I.source)
    (hsinLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I) = sinVal)
    (hsinUnderflow : sinVal.toNat < (healRad I).toNat) :
    ExecBlock config { contract := contract, locals := healLocals I } evm
      (checkedSubUintInto "sinNew" (.storage (sinRef sender)) (.var "rad"))
      .reverted := by
  have hrad :
      evalExpr? config { contract := contract, locals := healLocals I } evm (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocals I) (name := "rad")
      (value := healRad I) (healLocals_get_rad I)
  have hsin :
      evalExpr? config { contract := contract, locals := healLocals I } evm
          (.storage (sinRef sender)) =
        .ok (.int (Int.ofNat sinVal.toNat)) := by
    simpa [hsinLoad] using
      vatEvalExpr_heal_sin_sender evm I (healLocals I) hsrc (by simp [healLocals])
  have hsub :
      evalExpr? config { contract := contract, locals := healLocals I } evm
          (sub256 (.storage (sinRef sender)) (.var "rad")) = .revert :=
    vatEvalExpr_sub256_revert hsin hrad hsinUnderflow
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hsub)

theorem vatHealDaiSubBlockRevert (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiVal : UInt256}
    (hsrc : evm.executionEnv.source = I.source)
    (hdaiLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healDaiSlot I) = daiVal)
    (hdaiUnderflow : daiVal.toNat < (healRad I).toNat) :
    ExecBlock config { contract := contract, locals := healLocalsSinNew I sinNew } evm
      (checkedSubUintInto "daiNew" (.storage (daiRef sender)) (.var "rad"))
      .reverted := by
  have hrad :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocalsSinNew I sinNew)
      (name := "rad") (value := healRad I) (healLocalsSinNew_get_rad I sinNew)
  have hdai :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (.storage (daiRef sender)) =
        .ok (.int (Int.ofNat daiVal.toNat)) := by
    simpa [hdaiLoad] using
      vatEvalExpr_heal_dai_sender evm I (healLocalsSinNew I sinNew) hsrc
        (by simp [healLocalsSinNew, healLocals])
  have hsub :
      evalExpr? config { contract := contract, locals := healLocalsSinNew I sinNew } evm
          (sub256 (.storage (daiRef sender)) (.var "rad")) = .revert :=
    vatEvalExpr_sub256_revert hdai hrad hdaiUnderflow
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hsub)

theorem vatHealViceSubBlockRevert (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceVal : UInt256}
    (hviceLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner healViceSlot = viceVal)
    (hviceUnderflow : viceVal.toNat < (healRad I).toNat) :
    ExecBlock config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew } evm
      (checkedSubUintInto "viceNew" (.storage viceRef) (.var "rad"))
      .reverted := by
  have hrad :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := healLocalsDaiNew I sinNew daiNew)
      (name := "rad") (value := healRad I) (healLocalsDaiNew_get_rad I sinNew daiNew)
  have hvice :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceVal.toNat)) := by
    simpa [hviceLoad] using
      vatEvalExpr_heal_vice evm (healLocalsDaiNew I sinNew daiNew)
        (by simp [healLocalsDaiNew, healLocalsSinNew, healLocals])
  have hsub :
      evalExpr? config { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
          evm (sub256 (.storage viceRef) (.var "rad")) = .revert :=
    vatEvalExpr_sub256_revert hvice hrad hviceUnderflow
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hsub)

theorem vatHealDebtSubBlockRevert (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew debtVal : UInt256}
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner healDebtSlot = debtVal)
    (hdebtUnderflow : debtVal.toNat < (healRad I).toNat) :
    ExecBlock config { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew }
        evm
      (checkedSubUintInto "debtNew" (.storage debtRef) (.var "rad"))
      .reverted := by
  have hrad :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := healLocalsViceNew I sinNew daiNew viceNew) (name := "rad")
      (value := healRad I) (healLocalsViceNew_get_rad I sinNew daiNew viceNew)
  have hdebt :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (.storage debtRef) =
        .ok (.int (Int.ofNat debtVal.toNat)) := by
    simpa [hdebtLoad] using
      vatEvalExpr_heal_debt evm (healLocalsViceNew I sinNew daiNew viceNew)
        (by simp [healLocalsViceNew, healLocalsDaiNew, healLocalsSinNew, healLocals])
  have hsub :
      evalExpr? config
          { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
          (sub256 (.storage debtRef) (.var "rad")) = .revert :=
    vatEvalExpr_sub256_revert hdebt hrad hdebtUnderflow
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hsub)

theorem vatHealAssignSinOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew : UInt256}
    (hsrc : evm.executionEnv.source = I.source) :
    ExecBlock config
      { contract := contract, locals := healLocalsSinNew I sinNew } evm
      [ .assign .storage (sinRef sender) (.var "sinNew") ]
      (.ok { contract := contract, locals := healLocalsSinNew I sinNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew)) := by
  let locals := healLocalsSinNew I sinNew
  let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew
  have hsinNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := locals) (name := "sinNew")
      (value := sinNew) (by simpa [locals] using healLocalsSinNew_get_sinNew I sinNew)
  have hassignSin :
      assignStorageRef? config { contract := contract, locals := locals } evm
        .storage (sinRef sender) (.int (Int.ofNat sinNew.toNat)) =
          .ok ({ contract := contract, locals := locals }, evmSin) := by
    simpa [locals, evmSin] using
      assign_heal_sin_sender evm I locals sinNew hsrc
        (by simp [locals, healLocalsSinNew, healLocals])
  refine ExecBlock.consNormal (ExecStmt.assign hsinNewEval hassignSin) ?_
  exact ExecBlock.nil

theorem vatHealAssignDaiOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew : UInt256}
    (hsrc : evm.executionEnv.source = I.source) :
    ExecBlock config
      { contract := contract, locals := healLocalsDaiNew I sinNew daiNew } evm
      [ .assign .storage (daiRef sender) (.var "daiNew") ]
      (.ok { contract := contract, locals := healLocalsDaiNew I sinNew daiNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healDaiSlot I) daiNew)) := by
  let locals := healLocalsDaiNew I sinNew daiNew
  let evmDai := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healDaiSlot I) daiNew
  have hdaiNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "daiNew") =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := locals) (name := "daiNew")
      (value := daiNew) (by simpa [locals] using
        healLocalsDaiNew_get_daiNew I sinNew daiNew)
  have hassignDai :
      assignStorageRef? config { contract := contract, locals := locals } evm
        .storage (daiRef sender) (.int (Int.ofNat daiNew.toNat)) =
          .ok ({ contract := contract, locals := locals }, evmDai) := by
    simpa [locals, evmDai] using
      assign_heal_dai_sender evm I locals daiNew hsrc
        (by simp [locals, healLocalsDaiNew, healLocalsSinNew, healLocals])
  refine ExecBlock.consNormal (ExecStmt.assign hdaiNewEval hassignDai) ?_
  exact ExecBlock.nil

theorem vatHealAssignViceOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew : UInt256} :
    ExecBlock config
      { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew } evm
      [ .assign .storage viceRef (.var "viceNew") ]
      (.ok { contract := contract, locals := healLocalsViceNew I sinNew daiNew viceNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner healViceSlot viceNew)) := by
  let locals := healLocalsViceNew I sinNew daiNew viceNew
  let evmVice := Solm.EVM.storageStore evm evm.executionEnv.codeOwner healViceSlot viceNew
  have hviceNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := locals) (name := "viceNew")
      (value := viceNew) (by simpa [locals] using
        healLocalsViceNew_get_viceNew I sinNew daiNew viceNew)
  have hassignVice :
      assignStorageRef? config { contract := contract, locals := locals } evm
        .storage viceRef (.int (Int.ofNat viceNew.toNat)) =
          .ok ({ contract := contract, locals := locals }, evmVice) := by
    simpa [locals, evmVice] using
      assign_heal_vice evm locals viceNew
        (by simp [locals, healLocalsViceNew, healLocalsDaiNew, healLocalsSinNew, healLocals])
  refine ExecBlock.consNormal (ExecStmt.assign hviceNewEval hassignVice) ?_
  exact ExecBlock.nil

theorem vatHealAssignDebtOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew debtNew : UInt256} :
    ExecBlock config
      { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew } evm
      [ .assign .storage debtRef (.var "debtNew") ]
      (.ok { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner healDebtSlot debtNew)) := by
  let locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew
  let evmDebt := Solm.EVM.storageStore evm evm.executionEnv.codeOwner healDebtSlot debtNew
  have hdebtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := locals) (name := "debtNew")
      (value := debtNew) (by simp [locals, healLocalsDebtNew])
  have hassignDebt :
      assignStorageRef? config { contract := contract, locals := locals } evm
        .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
          .ok ({ contract := contract, locals := locals }, evmDebt) := by
    simpa [locals, evmDebt] using
      assign_heal_debt evm locals debtNew
        (by simp [locals, healLocalsDebtNew, healLocalsViceNew, healLocalsDaiNew,
          healLocalsSinNew, healLocals])
  refine ExecBlock.consNormal (ExecStmt.assign hdebtNewEval hassignDebt) ?_
  exact ExecBlock.nil

theorem vatHealSourceSuccess (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsinEnough : (healRad I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)).toNat) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)
    let sinNew := UInt256.sub sinVal (healRad I)
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)
    let daiNew := UInt256.sub daiVal (healRad I)
    let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner (healDaiSlot I) daiNew
    let viceVal := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot
    let viceNew := UInt256.sub viceVal (healRad I)
    let evmVice := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner healViceSlot viceNew
    let debtVal := Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot
    let debtNew := UInt256.sub debtVal (healRad I)
    (healRad I).toNat ≤ (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner
      (healDaiSlot I)).toNat →
    (healRad I).toNat ≤
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot).toNat →
    (healRad I).toNat ≤
      (Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot).toNat →
    ExecTransitionBody config contract evm (healLocals I) healTransition.body
      (.returned { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
        (healPostState evm I sinNew daiNew viceNew debtNew) none) := by
  intro sinVal sinNew evmSin daiVal daiNew evmDai viceVal viceNew evmVice debtVal debtNew
    hdaiEnough hviceEnough hdebtEnough
  have hsrcSin : evmSin.executionEnv.source = I.source := by
    simp [evmSin, storageStore_executionEnv, hsrc]
  have hsrcDai : evmDai.executionEnv.source = I.source := by
    simp [evmDai, storageStore_executionEnv, hsrcSin]
  have hsrcVice : evmVice.executionEnv.source = I.source := by
    simp [evmVice, storageStore_executionEnv, hsrcDai]
  have hsin := vatHealSinSubBlockOk (evm := evm) (I := I)
    (sinVal := sinVal) (sinNew := sinNew) hsrc rfl rfl hsinEnough
  have hassignSin := vatHealAssignSinOk (evm := evm) (I := I) (sinNew := sinNew) hsrc
  have hdaiEnough' :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)).toNat := by
    exact hdaiEnough
  have hdai := vatHealDaiSubBlockOk (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiVal := daiVal) (daiNew := daiNew) hsrcSin rfl rfl hdaiEnough'
  have hassignDai := vatHealAssignDaiOk (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) hsrcSin
  have hviceEnough' :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot).toNat := by
    exact hviceEnough
  have hvice := vatHealViceSubBlockOk (evm := evmDai) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceVal := viceVal) (viceNew := viceNew)
    rfl rfl hviceEnough'
  have hassignVice := vatHealAssignViceOk (evm := evmDai) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
  have hdebtEnough' :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot).toNat := by
    exact hdebtEnough
  have hdebt := vatHealDebtSubBlockOk (evm := evmVice) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
    (debtVal := debtVal) (debtNew := debtNew) rfl rfl hdebtEnough'
  have hassignDebt := vatHealAssignDebtOk (evm := evmVice) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew) (debtNew := debtNew)
  have h1 := execBlock_append hsin hassignSin
  have h2 := execBlock_append h1 hdai
  have h3 := execBlock_append h2 hassignDai
  have h4 := execBlock_append h3 hvice
  have h5 := execBlock_append h4 hassignVice
  have h6 := execBlock_append h5 hdebt
  have h7 := execBlock_append h6 hassignDebt
  have htail :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healBodyTail
        (.ok { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          (healPostState evm I sinNew daiNew viceNew debtNew)) := by
    simpa [healBodyTail, healPostState, evmSin, evmDai, evmVice, storageStore_executionEnv,
      List.append_assoc] using h7
  have hblock :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healTransition.body
        (.ok { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          (healPostState evm I sinNew daiNew viceNew debtNew)) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    simpa [healTransition, nonpayable, healBodyTail, checkedSubUintInto, List.append_assoc] using htail
  exact ExecFuncBody.execBlockOK hblock

theorem vatHealSourceSuccessNamed (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew debtNew : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsinNew :
      UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I))
        (healRad I) = sinNew)
    (hsinEnough : (healRad I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)).toNat) :
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew
    (UInt256.sub (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I))
        (healRad I) = daiNew) →
    (healRad I).toNat ≤
      (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)).toNat →
    let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner
      (healDaiSlot I) daiNew
    (UInt256.sub (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot)
        (healRad I) = viceNew) →
    (healRad I).toNat ≤
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot).toNat →
    let evmVice := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      healViceSlot viceNew
    (UInt256.sub (Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot)
        (healRad I) = debtNew) →
    (healRad I).toNat ≤
      (Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot).toNat →
    ExecTransitionBody config contract evm (healLocals I) healTransition.body
      (.returned { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
        (healPostState evm I sinNew daiNew viceNew debtNew) none) := by
  intro evmSin hdaiNew hdaiEnough evmDai hviceNew hviceEnough evmVice hdebtNew hdebtEnough
  have hsrcSin : evmSin.executionEnv.source = I.source := by
    simp [evmSin, storageStore_executionEnv, hsrc]
  have hsrcDai : evmDai.executionEnv.source = I.source := by
    simp [evmDai, storageStore_executionEnv, hsrcSin]
  have hsrcVice : evmVice.executionEnv.source = I.source := by
    simp [evmVice, storageStore_executionEnv, hsrcDai]
  have hsin := vatHealSinSubBlockOk (evm := evm) (I := I)
    (sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I))
    (sinNew := sinNew) hsrc rfl hsinNew.symm hsinEnough
  have hassignSin := vatHealAssignSinOk (evm := evm) (I := I) (sinNew := sinNew) hsrc
  have hdai := vatHealDaiSubBlockOk (evm := evmSin) (I := I)
    (sinNew := sinNew)
    (daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I))
    (daiNew := daiNew) hsrcSin rfl hdaiNew.symm hdaiEnough
  have hassignDai := vatHealAssignDaiOk (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) hsrcSin
  have hvice := vatHealViceSubBlockOk (evm := evmDai) (I := I)
    (sinNew := sinNew) (daiNew := daiNew)
    (viceVal := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot)
    (viceNew := viceNew) rfl hviceNew.symm hviceEnough
  have hassignVice := vatHealAssignViceOk (evm := evmDai) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
  have hdebt := vatHealDebtSubBlockOk (evm := evmVice) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
    (debtVal := Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot)
    (debtNew := debtNew) rfl hdebtNew.symm hdebtEnough
  have hassignDebt := vatHealAssignDebtOk (evm := evmVice) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew) (debtNew := debtNew)
  have h1 := execBlock_append hsin hassignSin
  have h2 := execBlock_append h1 hdai
  have h3 := execBlock_append h2 hassignDai
  have h4 := execBlock_append h3 hvice
  have h5 := execBlock_append h4 hassignVice
  have h6 := execBlock_append h5 hdebt
  have h7 := execBlock_append h6 hassignDebt
  have htail :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healBodyTail
        (.ok { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          (healPostState evm I sinNew daiNew viceNew debtNew)) := by
    simpa [healBodyTail, healPostState, evmSin, evmDai, evmVice, storageStore_executionEnv,
      List.append_assoc] using h7
  have hblock :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healTransition.body
        (.ok { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          (healPostState evm I sinNew daiNew viceNew debtNew)) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    simpa [healTransition, nonpayable, healBodyTail, checkedSubUintInto, List.append_assoc] using htail
  exact ExecFuncBody.execBlockOK hblock

theorem vatHealSourceSinUnderflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsinUnderflow :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)).toNat <
        (healRad I).toNat) :
    ExecTransitionBody config contract evm (healLocals I) healTransition.body .reverted := by
  let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)
  have hsinRev := vatHealSinSubBlockRevert (evm := evm) (I := I)
    (sinVal := sinVal) hsrc rfl hsinUnderflow
  have htail :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healBodyTail
        .reverted := by
    exact execBlock_append_term (s2 :=
      [ .assign .storage (sinRef sender) (.var "sinNew") ] ++
      checkedSubUintInto "daiNew" (.storage (daiRef sender)) (.var "rad") ++
      [ .assign .storage (daiRef sender) (.var "daiNew") ] ++
      checkedSubUintInto "viceNew" (.storage viceRef) (.var "rad") ++
      [ .assign .storage viceRef (.var "viceNew") ] ++
      checkedSubUintInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ]) hsinRev (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    simpa [healTransition, nonpayable, healBodyTail, checkedSubUintInto, List.append_assoc] using htail
  exact ExecFuncBody.execBlockRevert hblock

theorem vatHealSourceDaiUnderflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsinEnough : (healRad I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)).toNat) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)
    let sinNew := UInt256.sub sinVal (healRad I)
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)
    (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)).toNat <
      (healRad I).toNat →
    ExecTransitionBody config contract evm (healLocals I) healTransition.body .reverted := by
  intro sinVal sinNew evmSin daiVal hdaiUnderflow
  have hsrcSin : evmSin.executionEnv.source = I.source := by
    simp [evmSin, storageStore_executionEnv, hsrc]
  have hsin := vatHealSinSubBlockOk (evm := evm) (I := I)
    (sinVal := sinVal) (sinNew := sinNew) hsrc rfl rfl hsinEnough
  have hassignSin := vatHealAssignSinOk (evm := evm) (I := I) (sinNew := sinNew) hsrc
  have hdaiUnderflow' :
      (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)).toNat <
        (healRad I).toNat := by
    exact hdaiUnderflow
  have hdaiRev := vatHealDaiSubBlockRevert (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiVal := daiVal) hsrcSin rfl hdaiUnderflow'
  have hprefix := execBlock_append (execBlock_append hsin hassignSin) hdaiRev
  have htail :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healBodyTail
        .reverted := by
    simpa [List.append_assoc] using
      (execBlock_append_term (s2 :=
        [ .assign .storage (daiRef sender) (.var "daiNew") ] ++
        checkedSubUintInto "viceNew" (.storage viceRef) (.var "rad") ++
        [ .assign .storage viceRef (.var "viceNew") ] ++
        checkedSubUintInto "debtNew" (.storage debtRef) (.var "rad") ++
        [ .assign .storage debtRef (.var "debtNew") ])
        hprefix (by intro f e h; cases h))
  have hblock :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    simpa [healTransition, nonpayable, healBodyTail, checkedSubUintInto, List.append_assoc] using htail
  exact ExecFuncBody.execBlockRevert hblock

theorem vatHealSourceViceUnderflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsinEnough : (healRad I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)).toNat) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)
    let sinNew := UInt256.sub sinVal (healRad I)
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)
    let daiNew := UInt256.sub daiVal (healRad I)
    let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner (healDaiSlot I) daiNew
    let viceVal := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot
    (healRad I).toNat ≤ (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner
      (healDaiSlot I)).toNat →
    (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot).toNat <
      (healRad I).toNat →
    ExecTransitionBody config contract evm (healLocals I) healTransition.body .reverted := by
  intro sinVal sinNew evmSin daiVal daiNew evmDai viceVal hdaiEnough hviceUnderflow
  have hsrcSin : evmSin.executionEnv.source = I.source := by
    simp [evmSin, storageStore_executionEnv, hsrc]
  have hsrcDai : evmDai.executionEnv.source = I.source := by
    simp [evmDai, storageStore_executionEnv, hsrcSin]
  have hsin := vatHealSinSubBlockOk (evm := evm) (I := I)
    (sinVal := sinVal) (sinNew := sinNew) hsrc rfl rfl hsinEnough
  have hassignSin := vatHealAssignSinOk (evm := evm) (I := I) (sinNew := sinNew) hsrc
  have hdaiEnough' :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)).toNat := by
    exact hdaiEnough
  have hdai := vatHealDaiSubBlockOk (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiVal := daiVal) (daiNew := daiNew) hsrcSin rfl rfl hdaiEnough'
  have hassignDai := vatHealAssignDaiOk (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) hsrcSin
  have hviceUnderflow' :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot).toNat <
        (healRad I).toNat := by
    exact hviceUnderflow
  have hviceRev := vatHealViceSubBlockRevert (evm := evmDai) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceVal := viceVal) rfl hviceUnderflow'
  have hprefix :=
    execBlock_append (execBlock_append (execBlock_append (execBlock_append hsin hassignSin) hdai)
      hassignDai) hviceRev
  have htail :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healBodyTail
        .reverted := by
    simpa [List.append_assoc] using
      (execBlock_append_term (s2 :=
        [ .assign .storage viceRef (.var "viceNew") ] ++
        checkedSubUintInto "debtNew" (.storage debtRef) (.var "rad") ++
        [ .assign .storage debtRef (.var "debtNew") ])
        hprefix (by intro f e h; cases h))
  have hblock :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    simpa [healTransition, nonpayable, healBodyTail, checkedSubUintInto, List.append_assoc] using htail
  exact ExecFuncBody.execBlockRevert hblock

theorem vatHealSourceDebtUnderflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsinEnough : (healRad I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)).toNat) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (healSinSlot I)
    let sinNew := UInt256.sub sinVal (healRad I)
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (healSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)
    let daiNew := UInt256.sub daiVal (healRad I)
    let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner (healDaiSlot I) daiNew
    let viceVal := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot
    let viceNew := UInt256.sub viceVal (healRad I)
    let evmVice := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner healViceSlot viceNew
    let debtVal := Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot
    (healRad I).toNat ≤ (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner
      (healDaiSlot I)).toNat →
    (healRad I).toNat ≤
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot).toNat →
    (Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot).toNat <
      (healRad I).toNat →
    ExecTransitionBody config contract evm (healLocals I) healTransition.body .reverted := by
  intro sinVal sinNew evmSin daiVal daiNew evmDai viceVal viceNew evmVice debtVal
    hdaiEnough hviceEnough hdebtUnderflow
  have hsrcSin : evmSin.executionEnv.source = I.source := by
    simp [evmSin, storageStore_executionEnv, hsrc]
  have hsrcDai : evmDai.executionEnv.source = I.source := by
    simp [evmDai, storageStore_executionEnv, hsrcSin]
  have hsrcVice : evmVice.executionEnv.source = I.source := by
    simp [evmVice, storageStore_executionEnv, hsrcDai]
  have hsin := vatHealSinSubBlockOk (evm := evm) (I := I)
    (sinVal := sinVal) (sinNew := sinNew) hsrc rfl rfl hsinEnough
  have hassignSin := vatHealAssignSinOk (evm := evm) (I := I) (sinNew := sinNew) hsrc
  have hdaiEnough' :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (healDaiSlot I)).toNat := by
    exact hdaiEnough
  have hdai := vatHealDaiSubBlockOk (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiVal := daiVal) (daiNew := daiNew) hsrcSin rfl rfl hdaiEnough'
  have hassignDai := vatHealAssignDaiOk (evm := evmSin) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) hsrcSin
  have hviceEnough' :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner healViceSlot).toNat := by
    exact hviceEnough
  have hvice := vatHealViceSubBlockOk (evm := evmDai) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceVal := viceVal) (viceNew := viceNew)
    rfl rfl hviceEnough'
  have hassignVice := vatHealAssignViceOk (evm := evmDai) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
  have hdebtUnderflow' :
      (Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner healDebtSlot).toNat <
        (healRad I).toNat := by
    exact hdebtUnderflow
  have hdebtRev := vatHealDebtSubBlockRevert (evm := evmVice) (I := I)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew) (debtVal := debtVal)
    rfl hdebtUnderflow'
  have hprefix := execBlock_append
    (execBlock_append
      (execBlock_append
        (execBlock_append
          (execBlock_append
            (execBlock_append hsin hassignSin) hdai) hassignDai) hvice) hassignVice)
    hdebtRev
  have htail :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healBodyTail
        .reverted := by
    simpa [List.append_assoc] using
      (execBlock_append_term (s2 :=
        [ .assign .storage debtRef (.var "debtNew") ])
        hprefix (by intro f e h; cases h))
  have hblock :
      ExecBlock config { contract := contract, locals := healLocals I } evm
        healTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    simpa [healTransition, nonpayable, healBodyTail, checkedSubUintInto, List.append_assoc]
      using htail
  exact ExecFuncBody.execBlockRevert hblock

@[reducible] def solcCheckedAddEmptyRevertWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  solcCheckedAddSuccessWf code pc okPc
  ∧ decode code (solcCheckedArithmeticRevertPc pc) =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) =
      some (.DUP1, .none)
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedAddEmptyRevertAnyWords {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedAddEmptyRevertWf code pc okPc)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hadd, hdRev0, hdRev2, hdRev3⟩
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
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


end Benchmarks.Dss.Vat

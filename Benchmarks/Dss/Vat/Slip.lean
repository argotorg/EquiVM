import Benchmarks.Dss.Vat.Gem
import Benchmarks.Dss.Vat.Rely

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

/-! ## `slip(bytes32,address,int256)` -/

abbrev slipIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev slipUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev slipUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (slipUsrWord I)

abbrev slipWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev slipWadInt (I : ExecutionEnv) : Int :=
  if (slipWadWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (slipWadWord I).toNat
  else
    Int.ofNat (slipWadWord I).toNat - Int.ofNat EVM.wordModulus

abbrev slipIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev slipUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (slipUsrWord I).toNat)

abbrev slipWadValue (I : ExecutionEnv) : Value :=
  .int (slipWadInt I)

abbrev slipStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (slipIlkValue I)).insert "usr" (slipUsrValue I)).insert
    "wad" (slipWadValue I)

abbrev slipIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev slipUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (slipUsrWord I).toNat)

def slipStorageSlot (I : ExecutionEnv) : UInt256 :=
  gemSlot (slipIlkKey I) (slipUsrKey I)

abbrev slipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gem", steps := [.mindex (slipIlkKey I), .mindex (slipUsrKey I)] }

theorem slipStore_gem (I : ExecutionEnv) :
    (slipStore I).get? "gem" = none := by
  unfold slipStore
  rw [store_get_ne _ _ (by decide +native)]
  rw [store_get_ne _ _ (by decide +native)]
  rw [store_get_ne _ _ (by decide +native)]
  simp

theorem slipStore_wards (I : ExecutionEnv) :
    (slipStore I).get? "wards" = none := by
  unfold slipStore
  rw [store_get_ne _ _ (by decide +native)]
  rw [store_get_ne _ _ (by decide +native)]
  rw [store_get_ne _ _ (by decide +native)]
  simp

theorem slipStore_get_ilk (I : ExecutionEnv) :
    (slipStore I).get? "ilk" = some (slipIlkValue I) := by
  unfold slipStore
  rw [store_get_ne _ _ (by decide +native)]
  rw [store_get_ne _ _ (by decide +native)]
  simp

theorem slipStore_get_usr (I : ExecutionEnv) :
    (slipStore I).get? "usr" = some (slipUsrValue I) := by
  unfold slipStore
  rw [store_get_ne _ _ (by decide +native)]
  simp

theorem slipStore_get_wad (I : ExecutionEnv) :
    (slipStore I).get? "wad" = some (slipWadValue I) := by
  unfold slipStore
  simp

theorem slipStore_index_ilk (I : ExecutionEnv) :
    (slipStore I)["ilk"] = slipIlkValue I := by
  unfold slipStore
  rw [Std.HashMap.getElem_insert]
  simp
  rw [Std.HashMap.getElem_insert]
  simp

theorem slipStore_index_usr (I : ExecutionEnv) :
    (slipStore I)["usr"] = slipUsrValue I := by
  unfold slipStore
  rw [Std.HashMap.getElem_insert]
  simp

abbrev slipStoreGemNew (I : ExecutionEnv) (gemNew : UInt256) : Store :=
  (slipStore I).insert "gemNew" (.int (Int.ofNat gemNew.toNat))

theorem slipStoreGemNew_get_gemNew (I : ExecutionEnv) (gemNew : UInt256) :
    (slipStoreGemNew I gemNew).get? "gemNew" =
      some (.int (Int.ofNat gemNew.toNat)) := by
  rw [slipStoreGemNew, store_get_self]

theorem slipStoreGemNew_gem (I : ExecutionEnv) (gemNew : UInt256) :
    (slipStoreGemNew I gemNew).get? "gem" = none := by
  rw [slipStoreGemNew, store_get_ne _ _ (by decide +native), slipStore_gem]

theorem slipStoreGemNew_wards (I : ExecutionEnv) (gemNew : UInt256) :
    (slipStoreGemNew I gemNew).get? "wards" = none := by
  rw [slipStoreGemNew, store_get_ne _ _ (by decide +native), slipStore_wards]

theorem slipStoreGemNew_get_wad (I : ExecutionEnv) (gemNew : UInt256) :
    (slipStoreGemNew I gemNew).get? "wad" = some (slipWadValue I) := by
  rw [slipStoreGemNew, store_get_ne _ _ (by decide +native), slipStore_get_wad]

theorem slipStoreGemNew_index_ilk (I : ExecutionEnv) (gemNew : UInt256) :
    (slipStoreGemNew I gemNew)["ilk"] = slipIlkValue I := by
  change ((slipStore I).insert "gemNew" (.int (Int.ofNat gemNew.toNat)))["ilk"] =
    slipIlkValue I
  rw [Std.HashMap.getElem_insert]
  simp [slipStore_index_ilk]

theorem slipStoreGemNew_index_usr (I : ExecutionEnv) (gemNew : UInt256) :
    (slipStoreGemNew I gemNew)["usr"] = slipUsrValue I := by
  change ((slipStore I).insert "gemNew" (.int (Int.ofNat gemNew.toNat)))["usr"] =
    slipUsrValue I
  rw [Std.HashMap.getElem_insert]
  simp [slipStore_index_usr]

theorem slipStorageSlot_eq (I : ExecutionEnv) (hsz100 : 100 ≤ I.calldata.size) :
    slipStorageSlot I = solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
      (slipUsrMaskedWord I) := by
  unfold slipStorageSlot gemSlot gemIlkSlot slipIlkKey slipUsrKey slipUsrMaskedWord
    mapSlot solcMappingSlot slipIlkWord
  rw [gemIlkKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem evalStorageRef_slip_gem (evm : EVM.State) (I : ExecutionEnv)
    (hsz100 : 100 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := slipStore I } evm
      (gemRef (.var "ilk") (.var "usr")) = .ok (slipEvaledRef I) := by
  have hlen :
      ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    simp [bytes32Width]
    omega
  simp [slipEvaledRef, slipIlkValue, slipUsrValue, slipIlkKey, slipUsrKey, gemRef,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, slipStore_index_ilk,
    slipStore_index_usr, hlen]

theorem evalStorageRef_slip_gemNew (evm : EVM.State) (I : ExecutionEnv) (gemNew : UInt256)
    (hsz100 : 100 ≤ I.calldata.size) :
    evalStorageRef config
      { contract := contract, locals := slipStoreGemNew I gemNew } evm
      (gemRef (.var "ilk") (.var "usr")) = .ok (slipEvaledRef I) := by
  have hlen :
      ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    simp [bytes32Width]
    omega
  simp [slipEvaledRef, slipIlkValue, slipUsrValue, slipIlkKey, slipUsrKey, gemRef,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, slipStoreGemNew_index_ilk,
    slipStoreGemNew_index_usr, hlen]

theorem slipStorageType_gem (I : ExecutionEnv) :
    storageTypeAt? contract.storage (slipEvaledRef I) = some (.elem (.int uint256Int)) := by
  change storageTypeAt? storageDecls (slipEvaledRef I) = some (.elem (.int uint256Int))
  simp [slipEvaledRef, storageTypeAt?, storageTypeStep?, storageDecls, uint256St]

theorem slipStorageLayout_gem (I : ExecutionEnv) :
    config.storage.layout (slipEvaledRef I) = fun _ => some (wordLoc (slipStorageSlot I)) := by
  funext evm
  change storageLayoutRaw (slipEvaledRef I) evm = some (wordLoc (slipStorageSlot I))
  simp [storageLayoutRaw, slipEvaledRef, slipStorageSlot]

theorem slipWadInt_mod_word (I : ExecutionEnv) :
    slipWadInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (slipWadWord I).toNat := by
  have hltMod :
      (Int.ofNat (slipWadWord I).toNat) < Int.ofNat EVM.wordModulus := by
    have hltNat : (slipWadWord I).toNat < EVM.wordModulus := by
      change (slipWadWord I).val.val < EVM.twoPow 256
      exact (slipWadWord I).val.isLt
    exact Int.ofNat_lt.mpr hltNat
  have hbase :
      (Int.ofNat (slipWadWord I).toNat) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat (slipWadWord I).toNat :=
    Int.emod_eq_of_lt (Int.ofNat_nonneg _) hltMod
  unfold slipWadInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

theorem slipSignedAddWrap (old wad : UInt256) (wadInt : Int)
    (hwad : wadInt % (Int.ofNat EVM.wordModulus) = Int.ofNat wad.toNat) :
    (Int.ofNat old.toNat + wadInt) % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (wad + old).toNat := by
  have holdLt : old.toNat < EVM.wordModulus := by
    change old.val.val < EVM.twoPow 256
    exact old.val.isLt
  have hold :
      (Int.ofNat old.toNat) % (Int.ofNat EVM.wordModulus) = Int.ofNat old.toNat :=
    Int.emod_eq_of_lt (Int.ofNat_nonneg _) (Int.ofNat_lt.mpr holdLt)
  have hsumNat : (old.toNat + wad.toNat) % EVM.wordModulus = (wad + old).toNat := by
    rw [show EVM.wordModulus = UInt256.size by rfl]
    rw [uadd_toNat, Nat.add_comm]
  rw [Int.add_emod, hold, hwad]
  change ((↑(old.toNat + wad.toNat) : Int) % Int.ofNat EVM.wordModulus) =
    Int.ofNat (wad + old).toNat
  exact (Int.natCast_emod (old.toNat + wad.toNat) EVM.wordModulus).symm.trans
    (congrArg Int.ofNat hsumNat)

theorem evalExpr_slip_gem_old {evm : EVM.State} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := slipStore I } evm
      (.storage (gemRef (.var "ilk") (.var "usr"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (slipStorageSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (hbase := slipStore_gem I)
    (her := evalStorageRef_slip_gem evm I hsz100)
    (hty := slipStorageType_gem I)
    (hloc := slipStorageLayout_gem I)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (slipStorageSlot I))

set_option maxHeartbeats 1000000 in
theorem evalExpr_slip_gem_old_after_let {evm : EVM.State} {I : ExecutionEnv}
    (gemNew : UInt256) (hsz100 : 100 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
      (.storage (gemRef (.var "ilk") (.var "usr"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (slipStorageSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (hbase := slipStoreGemNew_gem I gemNew)
    (her := evalStorageRef_slip_gemNew evm I gemNew hsz100)
    (hty := slipStorageType_gem I)
    (hloc := slipStorageLayout_gem I)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (slipStorageSlot I))

theorem evalExpr_slip_gemNew {evm : EVM.State} {I : ExecutionEnv} {old gemNew : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (slipStorageSlot I) = old)
    (hwrap :
      (Int.ofNat old.toNat + slipWadInt I) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat gemNew.toNat) :
    evalExpr? config { contract := contract, locals := slipStore I } evm
      (wordWrap256 (.binary .add (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad"))) =
      .ok (.int (Int.ofNat gemNew.toNat)) := by
  have hgem := evalExpr_slip_gem_old (evm := evm) (I := I) hsz100
  have hwad :
      evalExpr? config { contract := contract, locals := slipStore I } evm (.var "wad") =
        .ok (.int (slipWadInt I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((slipStore I).get? "wad") =
      .ok (.int (slipWadInt I))
    rw [slipStore_get_wad]
    rfl
  have hmodNe : ¬ EVM.wordModulus = 0 := by decide
  simp [wordWrap256, evalExpr?, EvalResult.bind, bind, hgem, hwad, hload, evalBinaryOp?,
    hmodNe]
  simpa using hwrap

theorem assignStorageRef_slip_gemNew {evm evm' : EVM.State} {I : ExecutionEnv}
    {gemNew : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hevm' :
      evm' = Solm.EVM.storageStore evm evm.executionEnv.codeOwner (slipStorageSlot I) gemNew) :
    assignStorageRef? config
      { contract := contract, locals := slipStoreGemNew I gemNew } evm .storage
      (gemRef (.var "ilk") (.var "usr")) (.int (Int.ofNat gemNew.toNat)) =
      .ok ({ contract := contract, locals := slipStoreGemNew I gemNew }, evm') := by
  have hstore :
      storageLocStore evm (wordLoc (slipStorageSlot I)) (.int (Int.ofNat gemNew.toNat)) =
        some evm' := by
    rw [hevm']
    exact vatStorageLocStore_uint256 evm (slipStorageSlot I) gemNew
  exact assignStorageRef_storage_scalar
    (hbase := slipStoreGemNew_gem I gemNew)
    (her := evalStorageRef_slip_gemNew evm I gemNew hsz100)
    (hty := slipStorageType_gem I)
    (hloc := slipStorageLayout_gem I)
    (hstore := hstore)

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

theorem vatEvalExpr_varInt {evm : EVM.State} {locals : Store}
    {name : Ident} {value : Int}
    (h : locals.get? name = some (.int value)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int value) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int value)
  rw [h]
  rfl

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

theorem vatEvalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem vatEvalExpr_le_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hgt : b.toNat < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  omega

theorem vatEvalExpr_ge_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  omega

theorem vatEvalExpr_le_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hle : a ≤ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hle

theorem vatEvalExpr_ge_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hge : b ≤ a) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hge

theorem vatEvalExpr_le_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hgt : b < a) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  omega

theorem vatEvalExpr_ge_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hlt : a < b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  omega

theorem vatEvalExpr_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem vatEvalExpr_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem ugt_eq_zero_to_le {a b : UInt256}
    (h : UInt256.gt a b = ⟨0⟩) : a.toNat ≤ b.toNat := by
  by_contra hnot
  have hone : UInt256.gt a b = ⟨1⟩ := ugt_one (by omega)
  have hbad : (⟨1⟩ : UInt256) = ⟨0⟩ := by
    rw [← hone, h]
  exact False.elim ((by decide +native : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hbad)

theorem ult_eq_zero_to_le {a b : UInt256}
    (h : UInt256.lt a b = ⟨0⟩) : b.toNat ≤ a.toNat := by
  by_contra hnot
  have hone : UInt256.lt a b = ⟨1⟩ := ult_one (by omega)
  have hbad : (⟨1⟩ : UInt256) = ⟨0⟩ := by
    rw [← hone, h]
  exact False.elim ((by decide +native : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hbad)

theorem ugt_ne_zero_to_gt {a b : UInt256}
    (h : UInt256.gt a b ≠ ⟨0⟩) : b.toNat < a.toNat := by
  by_contra hnot
  exact h (ugt_zero (by omega))

theorem ult_ne_zero_to_lt {a b : UInt256}
    (h : UInt256.lt a b ≠ ⟨0⟩) : a.toNat < b.toNat := by
  by_contra hnot
  exact h (ult_zero (by omega))

theorem slt_zero_eq_zero_to_nonneg (w : UInt256)
    (h : UInt256.slt w ⟨0⟩ = ⟨0⟩) :
    0 ≤
      (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · simp [hlow]
  · have hhi : 2 ^ 255 ≤ w.toNat := by
      simpa [EVM.twoPow] using le_of_not_gt hlow
    have hone : UInt256.slt w (UInt256.ofNat 0) = ⟨1⟩ :=
      slt_lit_one_high (a := w) (m := 0) (by norm_num) hhi
    have hzero : UInt256.slt w (UInt256.ofNat 0) = ⟨0⟩ := by
      simpa using h
    have hbad : (⟨1⟩ : UInt256) = ⟨0⟩ := by
      rw [← hone, hzero]
    exact False.elim ((by decide +native : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hbad)

theorem sgt_zero_eq_zero_to_nonpos (w : UInt256)
    (h : UInt256.sgt w ⟨0⟩ = ⟨0⟩) :
    (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) ≤ 0 := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · by_cases hzero : w.toNat = 0
    · have hpow : 0 < EVM.twoPow 255 := by norm_num [EVM.twoPow]
      simp [hzero, hpow]
    · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero hzero
      have hone : UInt256.sgt w (UInt256.ofNat 0) = ⟨1⟩ :=
        sgt_lit_one (a := w) (m := 0) (by norm_num) (by simpa using hpos)
          (by simpa [EVM.twoPow] using hlow)
      have hzero' : UInt256.sgt w (UInt256.ofNat 0) = ⟨0⟩ := by
        simpa using h
      have hbad : (⟨1⟩ : UInt256) = ⟨0⟩ := by
        rw [← hone, hzero']
      exact False.elim ((by decide +native : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hbad)
  · simp [hlow]
    have hleNat : w.toNat ≤ EVM.wordModulus := Nat.le_of_lt w.val.isLt
    have hleInt : (w.toNat : Int) ≤ (EVM.wordModulus : Int) := by
      exact_mod_cast hleNat
    omega

theorem slt_zero_ne_zero_to_neg (w : UInt256)
    (h : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩) :
    (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) < 0 := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · have hslt0 : UInt256.slt w (UInt256.ofNat 0) = ⟨0⟩ :=
      slt_lit_zero (a := w) (m := 0) (by norm_num) (by omega)
        (by simpa [EVM.twoPow] using hlow)
    exact False.elim (h (by simpa using hslt0))
  · simp [hlow]
    have hltNat : w.toNat < EVM.wordModulus := w.val.isLt
    have hltInt : (w.toNat : Int) < (EVM.wordModulus : Int) := by
      exact_mod_cast hltNat
    omega

theorem sgt_zero_ne_zero_to_pos (w : UInt256)
    (h : UInt256.sgt w ⟨0⟩ ≠ ⟨0⟩) :
    0 <
      (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · by_cases hzero : w.toNat = 0
    · have hsgt0 : UInt256.sgt w (UInt256.ofNat 0) = ⟨0⟩ := by
        have hw : w = UInt256.ofNat 0 := by
          apply u256_inj
          simpa using hzero
        subst w
        decide +native
      exact False.elim (h (by simpa using hsgt0))
    · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero hzero
      simp [hlow]
      exact_mod_cast hpos
  · have hsgt0 : UInt256.sgt w (UInt256.ofNat 0) = ⟨0⟩ := by
      unfold UInt256.sgt UInt256.sgtBool UInt256.fromBool Bool.toUInt256
      have hhi : w.toNat ≥ 2 ^ 255 := by
        simpa [EVM.twoPow] using le_of_not_gt hlow
      have hzeroLow : ¬ (UInt256.ofNat 0).toNat ≥ 2 ^ 255 := by
        decide +native
      rw [if_pos hhi, if_neg hzeroLow]
      rfl
    exact False.elim (h (by simpa using hsgt0))

theorem evalSlipGuardNeg_true {evm : EVM.State} {I : ExecutionEnv} {old gemNew : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (slipStorageSlot I) = old)
    (hcond : 0 ≤ slipWadInt I ∨ gemNew.toNat ≤ old.toNat) :
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
      (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
        (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
      .ok (.bool true) := by
  have hwad :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.var "wad") = .ok (.int (slipWadInt I)) := by
    exact vatEvalExpr_varInt (by simpa [slipWadValue] using slipStoreGemNew_get_wad I gemNew)
  have hzero :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  cases hcond with
  | inl hnonneg =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_ge_int_true hwad hzero hnonneg)
  | inr hle =>
      by_cases hnonneg : 0 ≤ slipWadInt I
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_ge_int_true hwad hzero hnonneg)
      · have hleft := vatEvalExpr_ge_int_false hwad hzero (not_le.mp hnonneg)
        have hgemNew :
            evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
              (.var "gemNew") = .ok (.int (Int.ofNat gemNew.toNat)) :=
          vatEvalExpr_varUInt256 (slipStoreGemNew_get_gemNew I gemNew)
        have hold :
            evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
              (.storage (gemRef (.var "ilk") (.var "usr"))) =
              .ok (.int (Int.ofNat old.toNat)) := by
          rw [evalExpr_slip_gem_old_after_let (evm := evm) (I := I) gemNew hsz100]
          rw [hload]
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_le_uint256_true hgemNew hold hle)

theorem evalSlipGuardPos_true {evm : EVM.State} {I : ExecutionEnv} {old gemNew : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (slipStorageSlot I) = old)
    (hcond : slipWadInt I ≤ 0 ∨ old.toNat ≤ gemNew.toNat) :
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
      (eitherExpr (.binary .le (.var "wad") (.intLit 0))
        (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
      .ok (.bool true) := by
  have hwad :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.var "wad") = .ok (.int (slipWadInt I)) := by
    exact vatEvalExpr_varInt (by simpa [slipWadValue] using slipStoreGemNew_get_wad I gemNew)
  have hzero :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  cases hcond with
  | inl hnonpos =>
      exact vatEvalExpr_or_true_left
        (vatEvalExpr_le_int_true hwad hzero hnonpos)
  | inr hle =>
      by_cases hnonpos : slipWadInt I ≤ 0
      · exact vatEvalExpr_or_true_left
          (vatEvalExpr_le_int_true hwad hzero hnonpos)
      · have hleft := vatEvalExpr_le_int_false hwad hzero (not_le.mp hnonpos)
        have hgemNew :
            evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
              (.var "gemNew") = .ok (.int (Int.ofNat gemNew.toNat)) :=
          vatEvalExpr_varUInt256 (slipStoreGemNew_get_gemNew I gemNew)
        have hold :
            evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
              (.storage (gemRef (.var "ilk") (.var "usr"))) =
              .ok (.int (Int.ofNat old.toNat)) := by
          rw [evalExpr_slip_gem_old_after_let (evm := evm) (I := I) gemNew hsz100]
          rw [hload]
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_ge_uint256_true hgemNew hold hle)

theorem evalSlipGuardNeg_false {evm : EVM.State} {I : ExecutionEnv} {old gemNew : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (slipStorageSlot I) = old)
    (hcond : slipWadInt I < 0 ∧ old.toNat < gemNew.toNat) :
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
      (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
        (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
      .ok (.bool false) := by
  have hwad :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.var "wad") = .ok (.int (slipWadInt I)) := by
    exact vatEvalExpr_varInt (by simpa [slipWadValue] using slipStoreGemNew_get_wad I gemNew)
  have hzero :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hleft := vatEvalExpr_ge_int_false hwad hzero hcond.1
  have hgemNew :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.var "gemNew") = .ok (.int (Int.ofNat gemNew.toNat)) :=
    vatEvalExpr_varUInt256 (slipStoreGemNew_get_gemNew I gemNew)
  have hold :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.storage (gemRef (.var "ilk") (.var "usr"))) =
        .ok (.int (Int.ofNat old.toNat)) := by
    rw [evalExpr_slip_gem_old_after_let (evm := evm) (I := I) gemNew hsz100]
    rw [hload]
  exact vatEvalExpr_or_false_right hleft
    (vatEvalExpr_le_uint256_false hgemNew hold hcond.2)

theorem evalSlipGuardPos_false {evm : EVM.State} {I : ExecutionEnv} {old gemNew : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (slipStorageSlot I) = old)
    (hcond : 0 < slipWadInt I ∧ gemNew.toNat < old.toNat) :
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
      (eitherExpr (.binary .le (.var "wad") (.intLit 0))
        (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
      .ok (.bool false) := by
  have hwad :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.var "wad") = .ok (.int (slipWadInt I)) := by
    exact vatEvalExpr_varInt (by simpa [slipWadValue] using slipStoreGemNew_get_wad I gemNew)
  have hzero :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hleft := vatEvalExpr_le_int_false hwad hzero hcond.1
  have hgemNew :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.var "gemNew") = .ok (.int (Int.ofNat gemNew.toNat)) :=
    vatEvalExpr_varUInt256 (slipStoreGemNew_get_gemNew I gemNew)
  have hold :
      evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm
        (.storage (gemRef (.var "ilk") (.var "usr"))) =
        .ok (.int (Int.ofNat old.toNat)) := by
    rw [evalExpr_slip_gem_old_after_let (evm := evm) (I := I) gemNew hsz100]
    rw [hload]
  exact vatEvalExpr_or_false_right hleft
    (vatEvalExpr_ge_uint256_false hgemNew hold hcond.2)


theorem decodeScalarWordWithMode_legacyInt256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 int256 bytes start =
      some
        (.int
          (if (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.twoPow 255 then
            Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat
          else
            Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat -
              Int.ofNat EVM.wordModulus),
          start + 32) := by
  have hltWord :
      ↑(ABI.bytesToWord ((bytes.drop start).take 32)).val < EVM.wordModulus := by
    change (ABI.bytesToWord ((bytes.drop start).take 32)).val.val < EVM.twoPow 256
    exact (ABI.bytesToWord ((bytes.drop start).take 32)).val.isLt
  have hmodVal :
      (↑(ABI.bytesToWord ((bytes.drop start).take 32)).val) % EVM.wordModulus =
        ↑(ABI.bytesToWord ((bytes.drop start).take 32)).val :=
    Nat.mod_eq_of_lt hltWord
  have hmodInt :
      ((↑(↑(ABI.bytesToWord ((bytes.drop start).take 32)).val) : Int) %
          (↑EVM.wordModulus : Int)) =
        (↑(↑(ABI.bytesToWord ((bytes.drop start).take 32)).val) : Int) := by
    exact Int.emod_eq_of_lt (Int.ofNat_nonneg _) (by exact_mod_cast hltWord)
  simp [decodeScalarWordWithMode?, readWord?, readBytes?, decodeABIWord?, int256,
    int256Int, hlen, UInt256.toNat,
    show EVM.twoPow (256 - 1) = EVM.twoPow 255 by rfl,
    show EVM.twoPow 256 = EVM.wordModulus by rfl]
  rw [hmodVal]
  rw [hmodInt]

set_option maxHeartbeats 0 in
theorem decodeABIValues_bytes32_address_int256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [bytes32, addr, int256] bytes 0 0 96 96 DecodeMode.legacySolc05 =
      some
        ([ .fixedBytes bytes32Width (bytes.take 32),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .int
             (if (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat -
                 Int.ofNat EVM.wordModulus) ],
         96) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hge64 : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  have htakeBytes32 :
      List.take (↑bytes32Width + 1) (List.take 32 bytes) = List.take 32 bytes := by
    simp [bytes32Width]
  have hltWord64 :
      ↑(ABI.bytesToWord ((bytes.drop 64).take 32)).val < EVM.wordModulus := by
    change (ABI.bytesToWord ((bytes.drop 64).take 32)).val.val < EVM.twoPow 256
    exact (ABI.bytesToWord ((bytes.drop 64).take 32)).val.isLt
  have hmod64Val :
      (↑(ABI.bytesToWord ((bytes.drop 64).take 32)).val) % EVM.wordModulus =
        ↑(ABI.bytesToWord ((bytes.drop 64).take 32)).val :=
    Nat.mod_eq_of_lt hltWord64
  have hmod64Int :
      ((↑(↑(ABI.bytesToWord ((bytes.drop 64).take 32)).val) : Int) %
          (↑EVM.wordModulus : Int)) =
        (↑(↑(ABI.bytesToWord ((bytes.drop 64).take 32)).val) : Int) := by
    exact Int.emod_eq_of_lt (Int.ofNat_nonneg _) (by exact_mod_cast hltWord64)
  simp [decodeABIValues?, decodeABIValue?, readBytes?, readWord?, decodeABIWord?,
    bytes32, addr, int256, bytes32Width, int256Int, isDynamicABIType,
    staticABIEncodedSize?, hlen0, hlen32, hlen64, htakeBytes32, hge32, hge64,
    UInt256.toNat, show EVM.twoPow (256 - 1) = EVM.twoPow 255 by rfl,
    show EVM.twoPow 256 = EVM.wordModulus by rfl]
  rw [hmod64Val]
  rw [hmod64Int]

theorem decodeCalldata_legacyBytes32_address_int256_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z] [bytes32, addr, int256] cd =
      some ((((∅ : Store).insert x
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int
          (if (calldataWord cd 68).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 68).toNat
          else
            Int.ofNat (calldataWord cd 68).toNat - Int.ofNat EVM.wordModulus))) := by
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
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, int256] = some 96 by decide +native]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 96)]
  rw [decodeABIValues_bytes32_address_int256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  simp [decodeCalldata.insertValues]

set_option maxHeartbeats 0 in
theorem vatDecode_slip_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (slipTransition.params.map Param.name)
      (transitionSignature slipTransition).paramTypes I.calldata = some (slipStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "usr", "wad"]
    [bytes32, addr, int256] I.calldata = _
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "usr", "wad"]
    [bytes32, addr, int256] I.calldata =
      some ((((∅ : Store).insert "ilk" (slipIlkValue I)).insert "usr" (slipUsrValue I)).insert
        "wad" (slipWadValue I))
  simpa [slipIlkValue, slipUsrValue, slipWadValue, slipWadInt, slipUsrWord, slipWadWord,
    calldataWord] using
      decodeCalldata_legacyBytes32_address_int256_ok
        (cd := I.calldata) (x := "ilk") (y := "usr") (z := "wad") hsz100

theorem vatDecode_slip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (slipTransition.params.map Param.name)
      (transitionSignature slipTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "usr", "wad"]
    [bytes32, addr, int256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "usr", "wad"]
    [bytes32, addr, int256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, int256] = some 96 by decide +native]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 96)]

theorem vatDispatchSlip {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 23)) :
    dispatchMsg contract I.calldata = some slipTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 23 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some slipTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes, initSelectorBytes,
    liveSelectorBytes, moveSelectorBytes, nopeSelectorBytes, relySelectorBytes,
    sinSelectorBytes, slipSelectorBytes]
  decide +native

theorem vatReachSlipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 23)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1045⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x7cdd3fde⟩ :=
    vatSelWord_eq_of_beq I hsz 0x7c 0xdd 0x3f 0xde ⟨0x7cdd3fde⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms212Body 0 (by omega) ⟨1045⟩ hcode hwv hsz hsize
    hroot hhigh hhighlow heq0 htake (by jump_dest) (by decide +native)

@[reducible] def solcSlipExternalLoadAndJumpWf
    (code : ByteArray) (pc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p27 := p24 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.CALLDATALOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p11 = some (.SHL, .none)
  ∧ decode code p12 = some (.SUB, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.DUP3, .none)
  ∧ decode code p16 = some (.ADD, .none)
  ∧ decode code p17 = some (.CALLDATALOAD, .none)
  ∧ decode code p18 = some (.AND, .none)
  ∧ decode code p19 = some (.SWAP1, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p22 = some (.ADD, .none)
  ∧ decode code p23 = some (.CALLDATALOAD, .none)
  ∧ decode code p24 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p27 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcSlipExternalLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hwf : solcSlipExternalLoadAndJumpWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 68 ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd27⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.dup1 hd2 (by evm_ov)
  have rd4 := rd3.calldataload hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd7 := rd5.push1 ⟨1⟩ hd5 (by evm_ov)
  have rd9 := rd7.push1 ⟨1⟩ hd7 (by evm_ov)
  have rd11 := rd9.push1 ⟨160⟩ hd9 (by evm_ov)
  have rd12 := rd11.shl hd11 (by evm_ov)
  have rd13 := rd12.sub hd12 (by evm_ov)
  have rd15 := rd13.push1 ⟨32⟩ hd13 (by evm_ov)
  have rd16 := rd15.dup3 hd15 (by evm_ov)
  have rd17 := rd16.add hd16 (by evm_ov)
  have rd18 := rd17.calldataload hd17 (by evm_ov)
  have rd19 := rd18.and hd18 (by evm_ov)
  have rd20 := rd19.swap1 hd19 (by evm_ov)
  have rd22 := rd20.push1 ⟨64⟩ hd20 (by evm_ov)
  have rd23 := rd22.add hd22 (by evm_ov)
  have rd24 := rd23.calldataload hd23 (by evm_ov)
  have rd27 := rd24.push2 routine hd24 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd27.jump hd27 hroutine (by evm_ov)⟩

theorem vatSlipX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1045⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4558⟩
        [slipWadWord I, slipUsrMaskedWord I, slipIlkWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1045⟩) (ret := ⟨524⟩)
    (decoded := ⟨1067⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcSlipExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨1067⟩) (ret := ⟨524⟩) (routine := ⟨4558⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcSlipExternalLoadAndJumpWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [slipWadWord, slipUsrMaskedWord, slipUsrWord, slipIlkWord] using hroutine⟩

theorem vatSlipX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1045⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1045⟩) (ret := ⟨524⟩)
    (decoded := ⟨1067⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem RD.vatSignedAddOkSecond {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {sum x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6681⟩ (sum :: y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hpos : UInt256.sgt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt sum x = ⟨0⟩)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret (sum :: R) mem activeWords rdata acc k' C' := by
  have rd6682 := h.jumpdest (by decide +native) (by evm_ov)
  have rd6684 := rd6682.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd6685 := rd6684.dup3 (by decide +native) (by evm_ov)
  have rd6686 := rd6685.sgt (by decide +native) (by evm_ov)
  have rd6687 := rd6686.iszero (by decide +native) (by evm_ov)
  have rd6688 := rd6687.dup1 (by decide +native) (by evm_ov)
  have rd6691 := rd6688.push2 ⟨6697⟩ (by decide +native) (by evm_ov)
  by_cases hypos0 : UInt256.sgt y ⟨0⟩ = ⟨0⟩
  · have rd6697 := by
      rw [hypos0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6691
      simpa using rd6691.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
        (by evm_ov)
    have rd6698 := rd6697.jumpdest (by decide +native) (by evm_ov)
    have rd6701 := rd6698.push2 ⟨6615⟩ (by decide +native) (by evm_ov)
    have rd6615 := by
      simpa using rd6701.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
        (by evm_ov)
    have rd6616 := rd6615.jumpdest (by decide +native) (by evm_ov)
    have rd6617 := rd6616.swap3 (by decide +native) (by evm_ov)
    have rd6618 := rd6617.swap2 (by decide +native) (by evm_ov)
    have rd6619 := rd6618.pop (by decide +native) (by evm_ov)
    have rd6620 := rd6619.pop (by decide +native) (by evm_ov)
    exact ⟨_, _, rd6620.jump (by decide +native) hret (by evm_ov)⟩
  · have rd6692 := by
      have hcond : UInt256.isZero (UInt256.sgt y ⟨0⟩) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hypos0
      rw [hcond] at rd6691
      simpa using rd6691.jumpiNT (by decide +native)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6693 := rd6692.pop (by decide +native) (by evm_ov)
    have rd6694 := rd6693.dup3 (by decide +native) (by evm_ov)
    have rd6695 := rd6694.dup2 (by decide +native) (by evm_ov)
    have rd6696 := rd6695.lt (by decide +native) (by evm_ov)
    have rd6697pre := rd6696.iszero (by decide +native) (by evm_ov)
    have hlt0 : UInt256.lt sum x = ⟨0⟩ :=
      hpos.resolve_left hypos0
    have rd6697 := by
      rw [hlt0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6697pre
      exact rd6697pre
    have rd6698 := rd6697.jumpdest (by decide +native) (by evm_ov)
    have rd6701 := rd6698.push2 ⟨6615⟩ (by decide +native) (by evm_ov)
    have rd6615 := by
      simpa using rd6701.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
        (by evm_ov)
    have rd6616 := rd6615.jumpdest (by decide +native) (by evm_ov)
    have rd6617 := rd6616.swap3 (by decide +native) (by evm_ov)
    have rd6618 := rd6617.swap2 (by decide +native) (by evm_ov)
    have rd6619 := rd6618.pop (by decide +native) (by evm_ov)
    have rd6620 := rd6619.pop (by decide +native) (by evm_ov)
    exact ⟨_, _, rd6620.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vatSignedAddRevertSecond {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {sum x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6681⟩ (sum :: y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hpos : ¬ (UInt256.sgt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt sum x = ⟨0⟩))
    (hov : R.length + 7 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  have rd6682 := h.jumpdest (by decide +native) (by evm_ov)
  have rd6684 := rd6682.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd6685 := rd6684.dup3 (by decide +native) (by evm_ov)
  have rd6686 := rd6685.sgt (by decide +native) (by evm_ov)
  have rd6687 := rd6686.iszero (by decide +native) (by evm_ov)
  have rd6688 := rd6687.dup1 (by decide +native) (by evm_ov)
  have rd6691 := rd6688.push2 ⟨6697⟩ (by decide +native) (by evm_ov)
  have hypos0 : UInt256.sgt y ⟨0⟩ ≠ ⟨0⟩ := by
    intro hy
    exact hpos (Or.inl hy)
  have rd6692 := by
    have hcond : UInt256.isZero (UInt256.sgt y ⟨0⟩) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hypos0
    rw [hcond] at rd6691
    simpa using rd6691.jumpiNT (by decide +native)
      (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd6693 := rd6692.pop (by decide +native) (by evm_ov)
  have rd6694 := rd6693.dup3 (by decide +native) (by evm_ov)
  have rd6695 := rd6694.dup2 (by decide +native) (by evm_ov)
  have rd6696 := rd6695.lt (by decide +native) (by evm_ov)
  have rd6697pre := rd6696.iszero (by decide +native) (by evm_ov)
  have hlt0 : UInt256.lt sum x ≠ ⟨0⟩ := by
    intro hlt
    exact hpos (Or.inr hlt)
  have rd6697 := by
    have hcond : UInt256.isZero (UInt256.lt sum x) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hlt0
    rw [hcond] at rd6697pre
    exact rd6697pre
  have rd6698 := rd6697.jumpdest (by decide +native) (by evm_ov)
  have rd6701 := rd6698.push2 ⟨6615⟩ (by decide +native) (by evm_ov)
  have rd6702 := rd6701.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd6702
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons]; omega)

theorem RD.vatSignedAddOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6653⟩ (y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hneg : UInt256.slt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt (y + x) x = ⟨0⟩)
    (hpos : UInt256.sgt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt (y + x) x = ⟨0⟩)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret ((y + x) :: R) mem activeWords rdata acc k' C' := by
  let sum := y + x
  have rd6654 := h.jumpdest (by decide +native) (by evm_ov)
  have rd6655 := rd6654.dup2 (by decide +native) (by evm_ov)
  have rd6656 := rd6655.dup2 (by decide +native) (by evm_ov)
  have rd6657 := rd6656.add (by decide +native) (by evm_ov)
  have rd6659 := rd6657.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd6660 := rd6659.dup3 (by decide +native) (by evm_ov)
  have rd6661 := rd6660.slt (by decide +native) (by evm_ov)
  have rd6662 := rd6661.iszero (by decide +native) (by evm_ov)
  have rd6663 := rd6662.dup1 (by decide +native) (by evm_ov)
  have rd6666 := rd6663.push2 ⟨6672⟩ (by decide +native) (by evm_ov)
  by_cases hyneg0 : UInt256.slt y ⟨0⟩ = ⟨0⟩
  · have rd6672 := by
      rw [hyneg0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6666
      simpa [sum] using rd6666.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
        (by evm_ov)
    have rd6673 := rd6672.jumpdest (by decide +native) (by evm_ov)
    have rd6676 := rd6673.push2 ⟨6681⟩ (by decide +native) (by evm_ov)
    have rd6681 := by
      simpa using rd6676.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
        (by evm_ov)
    exact RD.vatSignedAddOkSecond (h := rd6681) hpos hret hov
  · have rd6667 := by
      have hcond : UInt256.isZero (UInt256.slt y ⟨0⟩) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hyneg0
      rw [hcond] at rd6666
      simpa [sum] using rd6666.jumpiNT (by decide +native)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6668 := rd6667.pop (by decide +native) (by evm_ov)
    have rd6669 := rd6668.dup3 (by decide +native) (by evm_ov)
    have rd6670 := rd6669.dup2 (by decide +native) (by evm_ov)
    have rd6671 := rd6670.gt (by decide +native) (by evm_ov)
    have rd6672pre := rd6671.iszero (by decide +native) (by evm_ov)
    have hgt0 : UInt256.gt sum x = ⟨0⟩ := by
      simpa [sum] using hneg.resolve_left hyneg0
    have rd6672 := by
      rw [hgt0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6672pre
      exact rd6672pre
    have rd6673 := rd6672.jumpdest (by decide +native) (by evm_ov)
    have rd6676 := rd6673.push2 ⟨6681⟩ (by decide +native) (by evm_ov)
    have rd6681 := by
      simpa using rd6676.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
        (by evm_ov)
    exact RD.vatSignedAddOkSecond (h := rd6681) hpos hret hov

theorem RD.vatSignedAddRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {activeWords : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6653⟩ (y :: x :: ret :: R) mem
      activeWords rdata acc k C)
    (hneg : ¬ (UInt256.slt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt (y + x) x = ⟨0⟩) ∨
      (UInt256.slt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt (y + x) x = ⟨0⟩) ∧
        ¬ (UInt256.sgt y ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt (y + x) x = ⟨0⟩))
    (hov : R.length + 7 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  let sum := y + x
  have rd6654 := h.jumpdest (by decide +native) (by evm_ov)
  have rd6655 := rd6654.dup2 (by decide +native) (by evm_ov)
  have rd6656 := rd6655.dup2 (by decide +native) (by evm_ov)
  have rd6657 := rd6656.add (by decide +native) (by evm_ov)
  have rd6659 := rd6657.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd6660 := rd6659.dup3 (by decide +native) (by evm_ov)
  have rd6661 := rd6660.slt (by decide +native) (by evm_ov)
  have rd6662 := rd6661.iszero (by decide +native) (by evm_ov)
  have rd6663 := rd6662.dup1 (by decide +native) (by evm_ov)
  have rd6666 := rd6663.push2 ⟨6672⟩ (by decide +native) (by evm_ov)
  rcases hneg with hnegFail | ⟨hnegOk, hposFail⟩
  · have hyneg0 : UInt256.slt y ⟨0⟩ ≠ ⟨0⟩ := by
      intro hy
      exact hnegFail (Or.inl hy)
    have rd6667 := by
      have hcond : UInt256.isZero (UInt256.slt y ⟨0⟩) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hyneg0
      rw [hcond] at rd6666
      simpa [sum] using rd6666.jumpiNT (by decide +native)
        (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6668 := rd6667.pop (by decide +native) (by evm_ov)
    have rd6669 := rd6668.dup3 (by decide +native) (by evm_ov)
    have rd6670 := rd6669.dup2 (by decide +native) (by evm_ov)
    have rd6671 := rd6670.gt (by decide +native) (by evm_ov)
    have rd6672pre := rd6671.iszero (by decide +native) (by evm_ov)
    have hgt0 : UInt256.gt sum x ≠ ⟨0⟩ := by
      intro hgt
      exact hnegFail (Or.inr (by simpa [sum] using hgt))
    have rd6672 := by
      have hcond : UInt256.isZero (UInt256.gt sum x) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hgt0
      rw [hcond] at rd6672pre
      exact rd6672pre
    have rd6673 := rd6672.jumpdest (by decide +native) (by evm_ov)
    have rd6676 := rd6673.push2 ⟨6681⟩ (by decide +native) (by evm_ov)
    have rd6677 := rd6676.jumpiNT (by decide +native)
      (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    exact RD.solcPush1Dup1Revert0 rd6677
      (by decide +native) (by decide +native) (by decide +native)
      (by simp only [List.length_cons]; omega)
  · by_cases hyneg0 : UInt256.slt y ⟨0⟩ = ⟨0⟩
    · have rd6672 := by
        rw [hyneg0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6666
        simpa [sum] using rd6666.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
          (by evm_ov)
      have rd6673 := rd6672.jumpdest (by decide +native) (by evm_ov)
      have rd6676 := rd6673.push2 ⟨6681⟩ (by decide +native) (by evm_ov)
      have rd6681 := by
        simpa using rd6676.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
          (by evm_ov)
      exact RD.vatSignedAddRevertSecond (h := rd6681) (by simpa [sum] using hposFail) hov
    · have rd6667 := by
        have hcond : UInt256.isZero (UInt256.slt y ⟨0⟩) = ⟨0⟩ :=
          isZero_eq_zero_of_ne hyneg0
        rw [hcond] at rd6666
        simpa [sum] using rd6666.jumpiNT (by decide +native)
          (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
      have rd6668 := rd6667.pop (by decide +native) (by evm_ov)
      have rd6669 := rd6668.dup3 (by decide +native) (by evm_ov)
      have rd6670 := rd6669.dup2 (by decide +native) (by evm_ov)
      have rd6671 := rd6670.gt (by decide +native) (by evm_ov)
      have rd6672pre := rd6671.iszero (by decide +native) (by evm_ov)
      have hgt0 : UInt256.gt sum x = ⟨0⟩ := by
        simpa [sum] using hnegOk.resolve_left hyneg0
      have rd6672 := by
        rw [hgt0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6672pre
        exact rd6672pre
      have rd6673 := rd6672.jumpdest (by decide +native) (by evm_ov)
      have rd6676 := rd6673.push2 ⟨6681⟩ (by decide +native) (by evm_ov)
      have rd6681 := by
        simpa using rd6676.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
          (by evm_ov)
      exact RD.vatSignedAddRevertSecond (h := rd6681) (by simpa [sum] using hposFail) hov

theorem RD.vatSlipToStoreValue {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {wad usr ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨4640⟩ (wad :: usr :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (husrClean : UInt256.land usr solcAddrMask = usr)
    (hneg :
      UInt256.slt wad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (wad + solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr))
          (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr)) = ⟨0⟩)
    (hpos :
      UInt256.sgt wad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (wad + solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr))
          (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr)) = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨4685⟩
      ((wad + solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr)) ::
        wad :: usr :: ilk :: ret :: R)
      (twoWordHashMem usr (solcMappingSlot ⟨4⟩ ilk) (twoWordHashMem ilk ⟨4⟩ mem))
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  let inner := solcMappingSlot ⟨4⟩ ilk
  let slot := solcMappingSlot inner usr
  let old := solcSlotWord σ ee slot
  have rd4641 := h.jumpdest (by decide +native) (by evm_ov)
  have rd4643 := rd4641.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd4644 := rd4643.dup4 (by decide +native) (by evm_ov)
  have rd4645 := rd4644.dup2 (by decide +native) (by evm_ov)
  have rd4646 := rd4645.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4648 := rd4646.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  have rd4650 := rd4648.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd4651 := rd4650.swap1 (by decide +native) (by evm_ov)
  have rd4652 := rd4651.dup2 (by decide +native) (by evm_ov)
  have rd4653 := rd4652.mstore 0 (twoWordHashMem ilk ⟨4⟩ mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4655 := rd4653.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd4656 := rd4655.dup1 (by decide +native) (by evm_ov)
  have rd4657 := rd4656.dup4 (by decide +native) (by evm_ov)
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨4⟩ mem).readWithPadding 0 64))) =
        inner := by
    simpa [inner] using twoWordHashMem_solcMappingSlot ⟨4⟩ ilk hmem
  have rd4658 := rd4657.keccak256 0 inner (UInt256.ofNat 3) (by decide +native)
    mem_cost hinner (by decide +native) (by evm_ov)
  have rd4660 := rd4658.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd4662 := rd4660.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd4664 := rd4662.push1 ⟨160⟩ (by decide +native) (by evm_ov)
  have rd4665 := rd4664.shl (by decide +native) (by evm_ov)
  have rd4666 := rd4665.sub (by decide +native) (by evm_ov)
  have rd4667 := rd4666.dup7 (by decide +native) (by evm_ov)
  have rd4668 := rd4667.and (by decide +native) (by evm_ov)
  have hmask : UInt256.land usr
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = usr := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact husrClean
  rw [hmask] at rd4668
  have rd4669 := rd4668.dup5 (by decide +native) (by evm_ov)
  have rd4670 := rd4669.mstore 0 (wordAt0Mem usr (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4671 := rd4670.swap1 (by decide +native) (by evm_ov)
  have rd4672 := rd4671.swap2 (by decide +native) (by evm_ov)
  have rd4673 := rd4672.mstore 0 (twoWordHashMem usr inner (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4674 := rd4673.swap1 (by decide +native) (by evm_ov)
  have hmemInner : (twoWordHashMem ilk ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨4⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem usr inner (twoWordHashMem ilk ⟨4⟩ mem)).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot inner usr hmemInner
  have rd4675 := rd4674.keccak256 0 slot (UInt256.ofNat 3) (by decide +native)
    mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4676⟩ := rd4675.sload (by decide +native) (by evm_ov)
  have hold :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  rw [hold] at rd4676
  have rd4679 := rd4676.push2 ⟨4685⟩ (by decide +native) (by evm_ov)
  have rd4680 := rd4679.swap1 (by decide +native) (by evm_ov)
  have rd4681 := rd4680.dup3 (by decide +native) (by evm_ov)
  have rd4684 := rd4681.push2 ⟨6653⟩ (by decide +native) (by evm_ov)
  have rd6653 := rd4684.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4685⟩ := RD.vatSignedAddOk
    (x := old) (y := wad) (ret := ⟨4685⟩) (R := wad :: usr :: ilk :: ret :: R)
    rd6653
    (by simpa [old, slot, inner] using hneg)
    (by simpa [old, slot, inner] using hpos)
    (by jump_dest) (by simp [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, by simpa [old, slot, inner] using rd4685⟩

theorem RD.vatSlipToStoreRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {wad usr ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨4640⟩ (wad :: usr :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (husrClean : UInt256.land usr solcAddrMask = usr)
    (hfail :
      ¬ (UInt256.slt wad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (wad + solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr))
          (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr)) = ⟨0⟩) ∨
      (UInt256.slt wad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (wad + solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr))
          (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt wad ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt (wad + solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr))
            (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr)) = ⟨0⟩))
    (hov : R.length + 12 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  let inner := solcMappingSlot ⟨4⟩ ilk
  let slot := solcMappingSlot inner usr
  let old := solcSlotWord σ ee slot
  have rd4641 := h.jumpdest (by decide +native) (by evm_ov)
  have rd4643 := rd4641.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd4644 := rd4643.dup4 (by decide +native) (by evm_ov)
  have rd4645 := rd4644.dup2 (by decide +native) (by evm_ov)
  have rd4646 := rd4645.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4648 := rd4646.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  have rd4650 := rd4648.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd4651 := rd4650.swap1 (by decide +native) (by evm_ov)
  have rd4652 := rd4651.dup2 (by decide +native) (by evm_ov)
  have rd4653 := rd4652.mstore 0 (twoWordHashMem ilk ⟨4⟩ mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4655 := rd4653.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd4656 := rd4655.dup1 (by decide +native) (by evm_ov)
  have rd4657 := rd4656.dup4 (by decide +native) (by evm_ov)
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨4⟩ mem).readWithPadding 0 64))) =
        inner := by
    simpa [inner] using twoWordHashMem_solcMappingSlot ⟨4⟩ ilk hmem
  have rd4658 := rd4657.keccak256 0 inner (UInt256.ofNat 3) (by decide +native)
    mem_cost hinner (by decide +native) (by evm_ov)
  have rd4660 := rd4658.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd4662 := rd4660.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd4664 := rd4662.push1 ⟨160⟩ (by decide +native) (by evm_ov)
  have rd4665 := rd4664.shl (by decide +native) (by evm_ov)
  have rd4666 := rd4665.sub (by decide +native) (by evm_ov)
  have rd4667 := rd4666.dup7 (by decide +native) (by evm_ov)
  have rd4668 := rd4667.and (by decide +native) (by evm_ov)
  have hmask : UInt256.land usr
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = usr := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact husrClean
  rw [hmask] at rd4668
  have rd4669 := rd4668.dup5 (by decide +native) (by evm_ov)
  have rd4670 := rd4669.mstore 0 (wordAt0Mem usr (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4671 := rd4670.swap1 (by decide +native) (by evm_ov)
  have rd4672 := rd4671.swap2 (by decide +native) (by evm_ov)
  have rd4673 := rd4672.mstore 0 (twoWordHashMem usr inner (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4674 := rd4673.swap1 (by decide +native) (by evm_ov)
  have hmemInner : (twoWordHashMem ilk ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨4⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem usr inner (twoWordHashMem ilk ⟨4⟩ mem)).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot inner usr hmemInner
  have rd4675 := rd4674.keccak256 0 slot (UInt256.ofNat 3) (by decide +native)
    mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4676⟩ := rd4675.sload (by decide +native) (by evm_ov)
  have hold :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  rw [hold] at rd4676
  have rd4679 := rd4676.push2 ⟨4685⟩ (by decide +native) (by evm_ov)
  have rd4680 := rd4679.swap1 (by decide +native) (by evm_ov)
  have rd4681 := rd4680.dup3 (by decide +native) (by evm_ov)
  have rd4684 := rd4681.push2 ⟨6653⟩ (by decide +native) (by evm_ov)
  have rd6653 := rd4684.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := old) (y := wad) (ret := ⟨4685⟩) (R := wad :: usr :: ilk :: ret :: R)
    rd6653 (by simpa [old, slot, inner] using hfail)
    (by simp [List.length_cons] at hov ⊢; omega)

theorem RD.vatSlipStoreValue {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {sum wad usr ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨4685⟩ (sum :: wad :: usr :: ilk :: ret :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (husrClean : UInt256.land usr solcAddrMask = usr)
    (hperm : ee.perm = true)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret R
      (twoWordHashMem usr (solcMappingSlot ⟨4⟩ ilk) (twoWordHashMem ilk ⟨4⟩ mem))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) usr) sum) k' C' := by
  let inner := solcMappingSlot ⟨4⟩ ilk
  let slot := solcMappingSlot inner usr
  have rd4686 := h.jumpdest (by decide +native) (by evm_ov)
  have rd4688 := rd4686.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd4689 := rd4688.swap4 (by decide +native) (by evm_ov)
  have rd4690 := rd4689.dup5 (by decide +native) (by evm_ov)
  have rd4691 := rd4690.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4693 := rd4691.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  have rd4695 := rd4693.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd4696 := rd4695.swap1 (by decide +native) (by evm_ov)
  have rd4697 := rd4696.dup2 (by decide +native) (by evm_ov)
  have rd4698 := rd4697.mstore 0 (twoWordHashMem ilk ⟨4⟩ mem) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4700 := rd4698.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd4701 := rd4700.dup1 (by decide +native) (by evm_ov)
  have rd4702 := rd4701.dup7 (by decide +native) (by evm_ov)
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨4⟩ mem).readWithPadding 0 64))) =
        inner := by
    simpa [inner] using twoWordHashMem_solcMappingSlot ⟨4⟩ ilk hmem
  have rd4703 := rd4702.keccak256 0 inner (UInt256.ofNat 3) (by decide +native)
    mem_cost hinner (by decide +native) (by evm_ov)
  have rd4705 := rd4703.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd4707 := rd4705.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd4709 := rd4707.push1 ⟨160⟩ (by decide +native) (by evm_ov)
  have rd4710 := rd4709.shl (by decide +native) (by evm_ov)
  have rd4711 := rd4710.sub (by decide +native) (by evm_ov)
  have rd4712 := rd4711.swap1 (by decide +native) (by evm_ov)
  have rd4713 := rd4712.swap6 (by decide +native) (by evm_ov)
  have rd4714 := rd4713.and (by decide +native) (by evm_ov)
  have hmask : UInt256.land usr
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = usr := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact husrClean
  rw [hmask] at rd4714
  have rd4715 := rd4714.dup7 (by decide +native) (by evm_ov)
  have rd4716 := rd4715.mstore 0 (wordAt0Mem usr (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4717 := rd4716.swap4 (by decide +native) (by evm_ov)
  have rd4718 := rd4717.swap1 (by decide +native) (by evm_ov)
  have rd4719 := rd4718.mstore 0 (twoWordHashMem usr inner (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd4720 := rd4719.swap2 (by decide +native) (by evm_ov)
  have rd4721 := rd4720.swap1 (by decide +native) (by evm_ov)
  have rd4722 := rd4721.swap3 (by decide +native) (by evm_ov)
  have hmemInner : (twoWordHashMem ilk ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨4⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem usr inner (twoWordHashMem ilk ⟨4⟩ mem)).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot inner usr hmemInner
  have rd4723 := rd4722.keccak256 0 slot (UInt256.ofNat 3) (by decide +native)
    mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4724⟩ := rd4723.sstore hperm (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd4725 := rd4724.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, by simpa [slot, inner] using rd4725.jump (by decide +native) hret (by evm_ov)⟩

theorem slipUsrMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (slipUsrMaskedWord I) solcAddrMask = slipUsrMaskedWord I := by
  unfold slipUsrMaskedWord
  rw [u256_land_comm solcAddrMask (slipUsrWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (slipUsrWord I))

set_option maxHeartbeats 1000000 in
theorem RD.vatSlipStoreOk {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4558⟩
      [slipWadWord I, slipUsrMaskedWord I, slipIlkWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩)
    (hneg :
      UInt256.slt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (slipWadWord I +
            solcSlotWord σ I (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
              (slipUsrMaskedWord I)))
          (solcSlotWord σ I (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
            (slipUsrMaskedWord I))) = ⟨0⟩)
    (hpos :
      UInt256.sgt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (slipWadWord I +
            solcSlotWord σ I (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
              (slipUsrMaskedWord I)))
          (solcSlotWord σ I (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
            (slipUsrMaskedWord I))) = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩ [sel]
      (twoWordHashMem (slipUsrMaskedWord I)
        (solcMappingSlot ⟨4⟩ (slipIlkWord I))
        (twoWordHashMem (slipIlkWord I) ⟨4⟩
          (twoWordHashMem (slipUsrMaskedWord I)
            (solcMappingSlot ⟨4⟩ (slipIlkWord I))
            (twoWordHashMem (slipIlkWord I) ⟨4⟩
              (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I)) (slipUsrMaskedWord I))
        (slipWadWord I +
          solcSlotWord σ I (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
            (slipUsrMaskedWord I)))) k' C' := by
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨4558⟩) (okPc := ⟨4640⟩)
    (key := slipWadWord I) (ret := slipUsrMaskedWord I)
    (R := [slipIlkWord I, ⟨524⟩, sel]) h
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
    hauth (by jump_dest) (by simp)
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hwithSum⟩ := RD.vatSlipToStoreValue
    (wad := slipWadWord I) (usr := slipUsrMaskedWord I) (ilk := slipIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hafterAuth hmemAuth (slipUsrMaskedWord_clean I)
    hneg hpos (by simp)
  have hmemOuter :
      (twoWordHashMem (slipUsrMaskedWord I)
        (solcMappingSlot ⟨4⟩ (slipIlkWord I))
        (twoWordHashMem (slipIlkWord I) ⟨4⟩
          (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem))).size = 96 := by
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact hmemAuth
  obtain ⟨_, _, hstored⟩ := RD.vatSlipStoreValue
    (sum := slipWadWord I +
      solcSlotWord σ I (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
        (slipUsrMaskedWord I)))
    (wad := slipWadWord I) (usr := slipUsrMaskedWord I) (ilk := slipIlkWord I)
    (ret := ⟨524⟩) (R := [sel]) hwithSum hmemOuter (slipUsrMaskedWord_clean I)
    hperm (by jump_dest) (by simp)
  exact ⟨_, _, by simpa using hstored⟩

theorem vatSlipSourceOk
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let old := vatSlotWord (slipStorageSlot I) σ_solm I
    let gemNew := slipWadWord I + old
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm0
        (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
          (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
        .ok (.bool true) →
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm0
        (eitherExpr (.binary .le (.var "wad") (.intLit 0))
          (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
        .ok (.bool true) →
    ExecTransitionBody config contract evm0 (slipStore I) slipTransition.body
      (.returned { contract := contract, locals := slipStoreGemNew I gemNew }
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (slipStorageSlot I) gemNew)
        none) := by
  intro evm0 old gemNew hguardNeg hguardPos
  have hload :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (slipStorageSlot I) = old := by
    simp [evm0, old, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hwrap :
      (Int.ofNat old.toNat + slipWadInt I) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat gemNew.toNat := by
    simpa [old, gemNew] using
      slipSignedAddWrap old (slipWadWord I) (slipWadInt I) (slipWadInt_mod_word I)
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := slipStore I) (slipStore_wards I) (by
      simpa [vatCallerWardsSlot, vatSlotWord] using hauthSolm)
  have hlet :
      evalExpr? config { contract := contract, locals := slipStore I } evm0
        (wordWrap256 (.binary .add (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad"))) =
        .ok (.int (Int.ofNat gemNew.toNat)) :=
    evalExpr_slip_gemNew (evm := evm0) (I := I) (old := old) (gemNew := gemNew)
      hsz100 hload hwrap
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (slipStorageSlot I) gemNew
  have hassign :
      assignStorageRef? config
        { contract := contract, locals := slipStoreGemNew I gemNew } evm0 .storage
        (gemRef (.var "ilk") (.var "usr")) (.int (Int.ofNat gemNew.toNat)) =
        .ok ({ contract := contract, locals := slipStoreGemNew I gemNew }, evm1) :=
    assignStorageRef_slip_gemNew (evm := evm0) (evm' := evm1) (I := I)
      (gemNew := gemNew) hsz100 rfl
  have hblock :
      ExecBlock config { contract := contract, locals := slipStore I } evm0
        (nonpayable ++ auth ++
          checkedAddSignedInto "gemNew" (.storage (gemRef (.var "ilk") (.var "usr")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ])
        (.ok { contract := contract, locals := slipStoreGemNew I gemNew } evm1) := by
    change ExecBlock config { contract := contract, locals := slipStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .letDecl "gemNew" (some uint256)
          (wordWrap256 (.binary .add (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad"))),
        .require
          (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
            (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))),
        .require
          (eitherExpr (.binary .le (.var "wad") (.intLit 0))
            (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))),
        .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ]
      (.ok { contract := contract, locals := slipStoreGemNew I gemNew } evm1)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNeg) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    have hgemNewVar :
        evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm0
          (.var "gemNew") = .ok (.int (Int.ofNat gemNew.toNat)) := by
      rw [evalExpr?]
      change EvalResult.ofOption EvalError.unboundVariable
        ((slipStoreGemNew I gemNew).get? "gemNew") =
          .ok (.int (Int.ofNat gemNew.toNat))
      rw [slipStoreGemNew_get_gemNew]
      rfl
    exact ExecBlock.consNormal (ExecStmt.assign hgemNewVar hassign) ExecBlock.nil
  simpa [ExecTransitionBody, slipTransition, evm0, evm1, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem vatSlipSourceRevertGuardNeg
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let old := vatSlotWord (slipStorageSlot I) σ_solm I
    let gemNew := slipWadWord I + old
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm0
        (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
          (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
        .ok (.bool false) →
    ExecTransitionBody config contract evm0 (slipStore I) slipTransition.body .reverted := by
  intro evm0 old gemNew hguardNeg
  have hload :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (slipStorageSlot I) = old := by
    simp [evm0, old, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hwrap :
      (Int.ofNat old.toNat + slipWadInt I) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat gemNew.toNat := by
    simpa [old, gemNew] using
      slipSignedAddWrap old (slipWadWord I) (slipWadInt I) (slipWadInt_mod_word I)
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := slipStore I) (slipStore_wards I) (by
      simpa [vatCallerWardsSlot, vatSlotWord] using hauthSolm)
  have hlet :
      evalExpr? config { contract := contract, locals := slipStore I } evm0
        (wordWrap256 (.binary .add (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad"))) =
        .ok (.int (Int.ofNat gemNew.toNat)) :=
    evalExpr_slip_gemNew (evm := evm0) (I := I) (old := old) (gemNew := gemNew)
      hsz100 hload hwrap
  have hblock :
      ExecBlock config { contract := contract, locals := slipStore I } evm0
        (nonpayable ++ auth ++
          checkedAddSignedInto "gemNew" (.storage (gemRef (.var "ilk") (.var "usr")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := slipStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .letDecl "gemNew" (some uint256)
          (wordWrap256 (.binary .add (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad"))),
        .require
          (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
            (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))),
        .require
          (eitherExpr (.binary .le (.var "wad") (.intLit 0))
            (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))),
        .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNeg)
  simpa [ExecTransitionBody, slipTransition, evm0, nonpayable, auth] using
    ExecFuncBody.execBlockRevert hblock

theorem vatSlipSourceRevertGuardPos
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let old := vatSlotWord (slipStorageSlot I) σ_solm I
    let gemNew := slipWadWord I + old
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm0
        (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
          (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
        .ok (.bool true) →
    evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNew } evm0
        (eitherExpr (.binary .le (.var "wad") (.intLit 0))
          (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
        .ok (.bool false) →
    ExecTransitionBody config contract evm0 (slipStore I) slipTransition.body .reverted := by
  intro evm0 old gemNew hguardNeg hguardPos
  have hload :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (slipStorageSlot I) = old := by
    simp [evm0, old, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hwrap :
      (Int.ofNat old.toNat + slipWadInt I) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat gemNew.toNat := by
    simpa [old, gemNew] using
      slipSignedAddWrap old (slipWadWord I) (slipWadInt I) (slipWadInt_mod_word I)
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := slipStore I) (slipStore_wards I) (by
      simpa [vatCallerWardsSlot, vatSlotWord] using hauthSolm)
  have hlet :
      evalExpr? config { contract := contract, locals := slipStore I } evm0
        (wordWrap256 (.binary .add (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad"))) =
        .ok (.int (Int.ofNat gemNew.toNat)) :=
    evalExpr_slip_gemNew (evm := evm0) (I := I) (old := old) (gemNew := gemNew)
      hsz100 hload hwrap
  have hblock :
      ExecBlock config { contract := contract, locals := slipStore I } evm0
        (nonpayable ++ auth ++
          checkedAddSignedInto "gemNew" (.storage (gemRef (.var "ilk") (.var "usr")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := slipStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .letDecl "gemNew" (some uint256)
          (wordWrap256 (.binary .add (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad"))),
        .require
          (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
            (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))),
        .require
          (eitherExpr (.binary .le (.var "wad") (.intLit 0))
            (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))),
        .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNeg) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPos)
  simpa [ExecTransitionBody, slipTransition, evm0, nonpayable, auth] using
    ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 0 in
theorem vatSlipBodyCore : VatBodyTheorem 23 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 23) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some slipTransition :=
    vatDispatchSlip hsel
  have hreach := vatReachSlipBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := vatDecode_slip_ok (I := I) hsz100
    obtain ⟨_, _, hdecoded⟩ := vatSlipX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    let callerSlot := vatCallerWardsSlot I
    let slot := slipStorageSlot I
    let oldE := vatSlotWord slot σ_evm I
    let oldS := vatSlotWord slot σ_solm I
    have hcallerWord : vatSlotWord callerSlot σ_evm I = vatSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have holdWord : oldE = oldS := by
      simpa [oldE, oldS, slot] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
    by_cases hauthEvm : vatSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : vatSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hloadS :
          Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner slot = oldS := by
        simp [evm0, oldS, slot, vatSlotWord, solcSlotWord, initState,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      have hslotEq := slipStorageSlot_eq I hsz100
      have holdSolc :
          solcSlotWord σ_evm I
              (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                (slipUsrMaskedWord I)) = oldE := by
        simpa [oldE, slot, vatSlotWord, hslotEq]
      let gemNewE := slipWadWord I + oldE
      let gemNewS := slipWadWord I + oldS
      by_cases hneg :
          UInt256.slt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.gt gemNewE oldE = ⟨0⟩
      · by_cases hpos :
            UInt256.sgt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.lt gemNewE oldE = ⟨0⟩
        · have hnegSolc :
              UInt256.slt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt
                  (slipWadWord I +
                    solcSlotWord σ_evm I
                      (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                        (slipUsrMaskedWord I)))
                  (solcSlotWord σ_evm I
                    (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                      (slipUsrMaskedWord I))) = ⟨0⟩ := by
            simpa [gemNewE, holdSolc] using hneg
          have hposSolc :
              UInt256.sgt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt
                  (slipWadWord I +
                    solcSlotWord σ_evm I
                      (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                        (slipUsrMaskedWord I)))
                  (solcSlotWord σ_evm I
                    (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                      (slipUsrMaskedWord I))) = ⟨0⟩ := by
            simpa [gemNewE, holdSolc] using hpos
          have hnegSource :
              0 ≤ slipWadInt I ∨ gemNewS.toNat ≤ oldS.toNat := by
            cases hneg with
            | inl hslt =>
                exact Or.inl (by
                  simpa [slipWadInt] using slt_zero_eq_zero_to_nonneg (slipWadWord I) hslt)
            | inr hgt =>
                exact Or.inr (by
                  have hle := ugt_eq_zero_to_le hgt
                  simpa [gemNewE, gemNewS, oldE, oldS, holdWord] using hle)
          have hposSource :
              slipWadInt I ≤ 0 ∨ oldS.toNat ≤ gemNewS.toNat := by
            cases hpos with
            | inl hsgt =>
                exact Or.inl (by
                  simpa [slipWadInt] using sgt_zero_eq_zero_to_nonpos (slipWadWord I) hsgt)
            | inr hlt =>
                exact Or.inr (by
                  have hle := ult_eq_zero_to_le hlt
                  simpa [gemNewE, gemNewS, oldE, oldS, holdWord] using hle)
          have hguardNeg :
              evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNewS } evm0
                  (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
                    (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
                  .ok (.bool true) :=
            evalSlipGuardNeg_true (evm := evm0) (I := I) (old := oldS)
              (gemNew := gemNewS) hsz100 hloadS hnegSource
          have hguardPos :
              evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNewS } evm0
                  (eitherExpr (.binary .le (.var "wad") (.intLit 0))
                    (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
                  .ok (.bool true) :=
            evalSlipGuardPos_true (evm := evm0) (I := I) (old := oldS)
              (gemNew := gemNewS) hsz100 hloadS hposSource
          have hbody := vatSlipSourceOk
            (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz100
            (by simpa [callerSlot] using hauthSolm) hguardNeg hguardPos
          obtain ⟨_, _, hretPc⟩ := RD.vatSlipStoreOk
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            hdecoded hauthSolc hnegSolc hposSolc hperm
          have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
          have hret :
              RDret vatBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (cA, sstoreAccountMap I.codeOwner σ_evm
                  (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                    (slipUsrMaskedWord I))
                  (slipWadWord I +
                    solcSlotWord σ_evm I
                      (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                        (slipUsrMaskedWord I))))
                ByteArray.empty := by
            simpa using RD.stop hretPc' (by decide +native) (by simp)
          let evm1 :=
            Solm.EVM.storageStore evm0 I.codeOwner slot gemNewS
          have hcreated :
              (cA, sstoreAccountMap I.codeOwner σ_evm
                (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                  (slipUsrMaskedWord I))
                (slipWadWord I +
                  solcSlotWord σ_evm I
                    (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                      (slipUsrMaskedWord I)))).1 = evm1.createdAccounts := by
            simp [evm1, evm0, initState, storageStore_createdAccounts]
          have haccounts :
              accountMapEquiv
                (cA, sstoreAccountMap I.codeOwner σ_evm
                  (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                    (slipUsrMaskedWord I))
                  (slipWadWord I +
                    solcSlotWord σ_evm I
                      (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                        (slipUsrMaskedWord I)))).2
                evm1.accountMap := by
            simpa [evm1, evm0, initState, storageStore_accountMap, slot, hslotEq,
              gemNewE, gemNewS, oldE, oldS, holdWord, holdSolc] using
              accountMapEquiv_sstoreAccountMap I.codeOwner slot gemNewS hAccounts
          have henc : returnEquiv ByteArray.empty none slipTransition.returnType := by
            rw [show slipTransition.returnType = [] by rfl]
            exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            hcreated haccounts henc
        · have hposFailSolc :
              ¬ (UInt256.sgt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt
                  (slipWadWord I +
                    solcSlotWord σ_evm I
                      (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                        (slipUsrMaskedWord I)))
                  (solcSlotWord σ_evm I
                    (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                      (slipUsrMaskedWord I))) = ⟨0⟩) := by
            intro hp
            exact hpos (by simpa [gemNewE, holdSolc] using hp)
          have hnegSolc :
              UInt256.slt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt
                  (slipWadWord I +
                    solcSlotWord σ_evm I
                      (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                        (slipUsrMaskedWord I)))
                  (solcSlotWord σ_evm I
                    (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                      (slipUsrMaskedWord I))) = ⟨0⟩ := by
            simpa [gemNewE, holdSolc] using hneg
          have hnegSource :
              0 ≤ slipWadInt I ∨ gemNewS.toNat ≤ oldS.toNat := by
            cases hneg with
            | inl hslt =>
                exact Or.inl (by
                  simpa [slipWadInt] using slt_zero_eq_zero_to_nonneg (slipWadWord I) hslt)
            | inr hgt =>
                exact Or.inr (by
                  have hle := ugt_eq_zero_to_le hgt
                  simpa [gemNewE, gemNewS, oldE, oldS, holdWord] using hle)
          have hguardNeg :
              evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNewS } evm0
                  (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
                    (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
                  .ok (.bool true) :=
            evalSlipGuardNeg_true (evm := evm0) (I := I) (old := oldS)
              (gemNew := gemNewS) hsz100 hloadS hnegSource
          have hposFalseCond : 0 < slipWadInt I ∧ gemNewS.toNat < oldS.toNat := by
            constructor
            · have hsgtNe : UInt256.sgt (slipWadWord I) ⟨0⟩ ≠ ⟨0⟩ := by
                intro hsgt
                exact hpos (Or.inl hsgt)
              simpa [slipWadInt] using sgt_zero_ne_zero_to_pos (slipWadWord I) hsgtNe
            · have hltNe : UInt256.lt gemNewE oldE ≠ ⟨0⟩ := by
                intro hlt
                exact hpos (Or.inr hlt)
              have hltNat := ult_ne_zero_to_lt hltNe
              simpa [gemNewE, gemNewS, oldE, oldS, holdWord] using hltNat
          have hguardPosFalse :
              evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNewS } evm0
                  (eitherExpr (.binary .le (.var "wad") (.intLit 0))
                    (.binary .ge (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
                  .ok (.bool false) :=
            evalSlipGuardPos_false (evm := evm0) (I := I) (old := oldS)
              (gemNew := gemNewS) hsz100 hloadS hposFalseCond
          have hbody := vatSlipSourceRevertGuardPos
            (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz100
            (by simpa [callerSlot] using hauthSolm) hguardNeg hguardPosFalse
          obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
            (code := vatBytecode) (pc := ⟨4558⟩) (okPc := ⟨4640⟩)
            (key := slipWadWord I) (ret := slipUsrMaskedWord I)
            (R := [slipIlkWord I, ⟨524⟩, vatSelWord I])
            (by simpa using hdecoded)
            (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
            hauthSolc (by jump_dest) (by simp)
          have hmemAuth :
              (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
            twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
          have hrev := RD.vatSlipToStoreRevert
            (wad := slipWadWord I) (usr := slipUsrMaskedWord I) (ilk := slipIlkWord I)
            (ret := ⟨524⟩) (R := [vatSelWord I]) hafterAuth hmemAuth
            (slipUsrMaskedWord_clean I) (Or.inr ⟨hnegSolc, hposFailSolc⟩) (by simp)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hnegFailSolc :
            ¬ (UInt256.slt (slipWadWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt
                (slipWadWord I +
                  solcSlotWord σ_evm I
                    (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                      (slipUsrMaskedWord I)))
                (solcSlotWord σ_evm I
                  (solcMappingSlot (solcMappingSlot ⟨4⟩ (slipIlkWord I))
                    (slipUsrMaskedWord I))) = ⟨0⟩) := by
          intro hn
          exact hneg (by simpa [gemNewE, holdSolc] using hn)
        have hnegFalseCond : slipWadInt I < 0 ∧ oldS.toNat < gemNewS.toNat := by
          constructor
          · have hsltNe : UInt256.slt (slipWadWord I) ⟨0⟩ ≠ ⟨0⟩ := by
              intro hslt
              exact hneg (Or.inl hslt)
            simpa [slipWadInt] using slt_zero_ne_zero_to_neg (slipWadWord I) hsltNe
          · have hgtNe : UInt256.gt gemNewE oldE ≠ ⟨0⟩ := by
              intro hgt
              exact hneg (Or.inr hgt)
            have hgtNat := ugt_ne_zero_to_gt hgtNe
            simpa [gemNewE, gemNewS, oldE, oldS, holdWord] using hgtNat
        have hguardNegFalse :
            evalExpr? config { contract := contract, locals := slipStoreGemNew I gemNewS } evm0
                (eitherExpr (.binary .ge (.var "wad") (.intLit 0))
                  (.binary .le (.var "gemNew") (.storage (gemRef (.var "ilk") (.var "usr"))))) =
                .ok (.bool false) :=
          evalSlipGuardNeg_false (evm := evm0) (I := I) (old := oldS)
            (gemNew := gemNewS) hsz100 hloadS hnegFalseCond
        have hbody := vatSlipSourceRevertGuardNeg
          (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hwv hsz100
          (by simpa [callerSlot] using hauthSolm) hguardNegFalse
        obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
          (code := vatBytecode) (pc := ⟨4558⟩) (okPc := ⟨4640⟩)
          (key := slipWadWord I) (ret := slipUsrMaskedWord I)
          (R := [slipIlkWord I, ⟨524⟩, vatSelWord I])
          (by simpa using hdecoded)
          (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
          hauthSolc (by jump_dest) (by simp)
        have hmemAuth :
            (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hrev := RD.vatSlipToStoreRevert
          (wad := slipWadWord I) (usr := slipUsrMaskedWord I) (ilk := slipIlkWord I)
          (ret := ⟨524⟩) (R := [vatSelWord I]) hafterAuth hmemAuth
          (slipUsrMaskedWord_clean I) (Or.inl hnegFailSolc) (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : vatSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 (slipStore I) slipTransition.body .reverted := by
        have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := slipStore I)
          (slipStore_wards I) (by simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthSolm)
        have hblock := nonpayableSecondRequireReverts
          (cfg := config) (solm := { contract := contract, locals := slipStore I })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest := checkedAddSignedInto "gemNew" (.storage (gemRef (.var "ilk") (.var "usr")))
            (.var "wad") ++
            [ .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, slipTransition, nonpayable, auth, evm0] using
          ExecFuncBody.execBlockRevert hblock
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
      have hrev := RD.vatAuthCheckRevert
        (pc := ⟨4558⟩) (okPc := ⟨4640⟩) (key := slipWadWord I)
        (ret := slipUsrMaskedWord I) (R := [slipIlkWord I, ⟨524⟩, vatSelWord I])
        (by simpa using hdecoded)
        (by unfold vatAuthCheckWf; repeat' first | apply And.intro | decide +native)
        (by unfold vatAuthRevertTailWf vatAuthTailPc; repeat' first | apply And.intro | decide +native)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (vatSlipX_shortarg (g := Sat256.ofUInt256 g) hsz4 (by omega) hsize hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (vatDecode_slip_none_short hsz4 (by omega))

end Benchmarks.Dss.Vat

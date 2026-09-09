import Benchmarks.Dss.Vat.Dispatch
import Benchmarks.Dss.Vat.HealBase
import Benchmarks.Dss.Vat.Rely

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

/-! ## `suck(address,address,uint256)` -/

abbrev suckUWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev suckUMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (suckUWord I)

abbrev suckVWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev suckVMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (suckVWord I)

abbrev suckRadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev suckUValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (suckUWord I).toNat)

abbrev suckVValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (suckVWord I).toNat)

abbrev suckRadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (suckRadWord I).toNat)

abbrev suckStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "u" (suckUValue I)).insert "v" (suckVValue I)).insert
    "rad" (suckRadValue I)

abbrev suckStoreSinNew (I : ExecutionEnv) (sinNew : UInt256) : Store :=
  (suckStore I).insert "sinNew" (.int (Int.ofNat sinNew.toNat))

abbrev suckStoreDaiNew (I : ExecutionEnv) (sinNew daiNew : UInt256) : Store :=
  (suckStoreSinNew I sinNew).insert "daiNew" (.int (Int.ofNat daiNew.toNat))

abbrev suckStoreViceNew (I : ExecutionEnv)
    (sinNew daiNew viceNew : UInt256) : Store :=
  (suckStoreDaiNew I sinNew daiNew).insert "viceNew" (.int (Int.ofNat viceNew.toNat))

abbrev suckStoreDebtNew (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) : Store :=
  (suckStoreViceNew I sinNew daiNew viceNew).insert "debtNew"
    (.int (Int.ofNat debtNew.toNat))

abbrev suckUKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (suckUWord I).toNat)

abbrev suckVKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (suckVWord I).toNat)

abbrev suckSinSlot (I : ExecutionEnv) : UInt256 :=
  sinSlot (suckUKey I)

abbrev suckDaiSlot (I : ExecutionEnv) : UInt256 :=
  daiSlot (suckVKey I)

abbrev suckViceSlot : UInt256 :=
  ⟨8⟩

abbrev suckDebtSlot : UInt256 :=
  ⟨7⟩

abbrev suckPostState (evm : EVM.State) (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew)
        evm.executionEnv.codeOwner (suckDaiSlot I) daiNew)
      evm.executionEnv.codeOwner suckViceSlot viceNew)
    evm.executionEnv.codeOwner suckDebtSlot debtNew

theorem suckSinSlot_eq (I : ExecutionEnv) :
    suckSinSlot I = solcMappingSlot ⟨6⟩ (suckUMaskedWord I) := by
  unfold suckSinSlot suckUKey suckUMaskedWord sinSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem suckDaiSlot_eq (I : ExecutionEnv) :
    suckDaiSlot I = solcMappingSlot ⟨5⟩ (suckVMaskedWord I) := by
  unfold suckDaiSlot suckVKey suckVMaskedWord daiSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem vatStorageLoad_after_initState_store
    {cA gh bl σ σ₀ A I} {g : Sat256} (writeSlot readSlot val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner writeSlot val)
        I.codeOwner readSlot =
      vatSlotWord readSlot (sstoreAccountMap I.codeOwner σ writeSlot val) I := by
  simp [Solm.EVM.storageLoad, vatSlotWord, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount,
    Account.lookupStorage]

theorem vatStorageLoad_after_initState_store₂
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (slot₁ slot₂ readSlot val₁ val₂ : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
            I.codeOwner slot₁ val₁)
          I.codeOwner slot₂ val₂)
        I.codeOwner readSlot =
      vatSlotWord readSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ slot₁ val₁) slot₂ val₂) I := by
  simp [Solm.EVM.storageLoad, vatSlotWord, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount, Account.lookupStorage]

theorem vatStorageLoad_after_initState_store₃
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (slot₁ slot₂ slot₃ readSlot val₁ val₂ val₃ : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
              I.codeOwner slot₁ val₁)
            I.codeOwner slot₂ val₂)
          I.codeOwner slot₃ val₃)
        I.codeOwner readSlot =
      vatSlotWord readSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ slot₁ val₁) slot₂ val₂)
          slot₃ val₃) I := by
  simp [Solm.EVM.storageLoad, vatSlotWord, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount, Account.lookupStorage]

theorem accountMapEquiv_sstoreAccountMap_four {σ τ : AccountMap}
    (a1 a2 a3 a4 : AccountAddress)
    (slot1 val1 slot2 val2 slot3 val3 slot4 val4 : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap a4
        (sstoreAccountMap a3
          (sstoreAccountMap a2 (sstoreAccountMap a1 σ slot1 val1) slot2 val2)
          slot3 val3) slot4 val4)
      (sstoreAccountMap a4
        (sstoreAccountMap a3
          (sstoreAccountMap a2 (sstoreAccountMap a1 τ slot1 val1) slot2 val2)
          slot3 val3) slot4 val4) := by
  exact accountMapEquiv_sstoreAccountMap a4 slot4 val4
    (accountMapEquiv_sstoreAccountMap_three a1 a2 a3
      slot1 val1 slot2 val2 slot3 val3 hστ)

theorem suckUMaskedWord_canonical (I : ExecutionEnv) :
    (suckUMaskedWord I).toNat < EVM.addressModulus := by
  unfold suckUMaskedWord
  rw [u256_land_comm solcAddrMask (suckUWord I)]
  exact solcAddrMask_result_canonical (suckUWord I)

theorem suckVMaskedWord_canonical (I : ExecutionEnv) :
    (suckVMaskedWord I).toNat < EVM.addressModulus := by
  unfold suckVMaskedWord
  rw [u256_land_comm solcAddrMask (suckVWord I)]
  exact solcAddrMask_result_canonical (suckVWord I)

abbrev suckSinEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sin", steps := [.mindex (suckUKey I)] }

abbrev suckDaiEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "dai", steps := [.mindex (suckVKey I)] }

abbrev suckViceEvaledRef : EvaledStorageRef :=
  { base := "vice", steps := [] }

abbrev suckDebtEvaledRef : EvaledStorageRef :=
  { base := "debt", steps := [] }

theorem suckStore_get_u (I : ExecutionEnv) :
    (suckStore I).get? "u" = some (suckUValue I) := by
  unfold suckStore
  repeat rw [store_get_ne _ _ (by decide +native)]
  simp

theorem suckStore_get_v (I : ExecutionEnv) :
    (suckStore I).get? "v" = some (suckVValue I) := by
  unfold suckStore
  rw [store_get_ne _ _ (by decide +native)]
  simp

theorem suckStoreSinNew_get_u (I : ExecutionEnv) (sinNew : UInt256) :
    (suckStoreSinNew I sinNew).get? "u" = some (suckUValue I) := by
  rw [suckStoreSinNew, store_get_ne _ _ (by decide +native), suckStore_get_u]

theorem suckStoreSinNew_get_v (I : ExecutionEnv) (sinNew : UInt256) :
    (suckStoreSinNew I sinNew).get? "v" = some (suckVValue I) := by
  rw [suckStoreSinNew, store_get_ne _ _ (by decide +native), suckStore_get_v]

theorem suckStoreDaiNew_get_v (I : ExecutionEnv) (sinNew daiNew : UInt256) :
    (suckStoreDaiNew I sinNew daiNew).get? "v" = some (suckVValue I) := by
  rw [suckStoreDaiNew, store_get_ne _ _ (by decide +native),
    suckStoreSinNew_get_v]

theorem suckStore_get_rad (I : ExecutionEnv) :
    (suckStore I).get? "rad" = some (suckRadValue I) := by
  simp [suckStore]

theorem suckStoreSinNew_get_rad (I : ExecutionEnv) (sinNew : UInt256) :
    (suckStoreSinNew I sinNew).get? "rad" = some (suckRadValue I) := by
  rw [suckStoreSinNew, store_get_ne _ _ (by decide +native), suckStore_get_rad]

theorem suckStoreDaiNew_get_rad (I : ExecutionEnv) (sinNew daiNew : UInt256) :
    (suckStoreDaiNew I sinNew daiNew).get? "rad" = some (suckRadValue I) := by
  rw [suckStoreDaiNew, store_get_ne _ _ (by decide +native),
    suckStoreSinNew_get_rad]

theorem suckStoreViceNew_get_rad (I : ExecutionEnv)
    (sinNew daiNew viceNew : UInt256) :
    (suckStoreViceNew I sinNew daiNew viceNew).get? "rad" =
      some (suckRadValue I) := by
  rw [suckStoreViceNew, store_get_ne _ _ (by decide +native),
    suckStoreDaiNew_get_rad]

theorem suckStoreSinNew_get_sinNew (I : ExecutionEnv) (sinNew : UInt256) :
    (suckStoreSinNew I sinNew).get? "sinNew" =
      some (.int (Int.ofNat sinNew.toNat)) := by
  simp [suckStoreSinNew]

theorem suckStoreDaiNew_get_daiNew (I : ExecutionEnv) (sinNew daiNew : UInt256) :
    (suckStoreDaiNew I sinNew daiNew).get? "daiNew" =
      some (.int (Int.ofNat daiNew.toNat)) := by
  simp [suckStoreDaiNew]

theorem suckStoreViceNew_get_viceNew (I : ExecutionEnv)
    (sinNew daiNew viceNew : UInt256) :
    (suckStoreViceNew I sinNew daiNew viceNew).get? "viceNew" =
      some (.int (Int.ofNat viceNew.toNat)) := by
  simp [suckStoreViceNew]

theorem suckStoreDebtNew_get_debtNew (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) :
    (suckStoreDebtNew I sinNew daiNew viceNew debtNew).get? "debtNew" =
      some (.int (Int.ofNat debtNew.toNat)) := by
  simp [suckStoreDebtNew]

theorem suckStore_sin (I : ExecutionEnv) :
    (suckStore I).get? "sin" = none := by
  unfold suckStore
  repeat rw [store_get_ne _ _ (by decide +native)]
  simp

theorem suckStoreSinNew_sin (I : ExecutionEnv) (sinNew : UInt256) :
    (suckStoreSinNew I sinNew).get? "sin" = none := by
  rw [suckStoreSinNew, store_get_ne _ _ (by decide +native), suckStore_sin]

theorem suckStore_dai (I : ExecutionEnv) :
    (suckStore I).get? "dai" = none := by
  unfold suckStore
  repeat rw [store_get_ne _ _ (by decide +native)]
  simp

theorem suckStoreSinNew_dai (I : ExecutionEnv) (sinNew : UInt256) :
    (suckStoreSinNew I sinNew).get? "dai" = none := by
  rw [suckStoreSinNew, store_get_ne _ _ (by decide +native), suckStore_dai]

theorem suckStoreDaiNew_dai (I : ExecutionEnv) (sinNew daiNew : UInt256) :
    (suckStoreDaiNew I sinNew daiNew).get? "dai" = none := by
  rw [suckStoreDaiNew, store_get_ne _ _ (by decide +native), suckStoreSinNew_dai]

theorem suckStore_vice (I : ExecutionEnv) :
    (suckStore I).get? "vice" = none := by
  unfold suckStore
  repeat rw [store_get_ne _ _ (by decide +native)]
  simp

theorem suckStoreDaiNew_vice (I : ExecutionEnv) (sinNew daiNew : UInt256) :
    (suckStoreDaiNew I sinNew daiNew).get? "vice" = none := by
  rw [suckStoreDaiNew, store_get_ne _ _ (by decide +native)]
  rw [suckStoreSinNew, store_get_ne _ _ (by decide +native), suckStore_vice]

theorem suckStoreViceNew_vice (I : ExecutionEnv) (sinNew daiNew viceNew : UInt256) :
    (suckStoreViceNew I sinNew daiNew viceNew).get? "vice" = none := by
  rw [suckStoreViceNew, store_get_ne _ _ (by decide +native), suckStoreDaiNew_vice]

theorem suckStore_debt (I : ExecutionEnv) :
    (suckStore I).get? "debt" = none := by
  unfold suckStore
  repeat rw [store_get_ne _ _ (by decide +native)]
  simp

theorem suckStoreViceNew_debt (I : ExecutionEnv) (sinNew daiNew viceNew : UInt256) :
    (suckStoreViceNew I sinNew daiNew viceNew).get? "debt" = none := by
  rw [suckStoreViceNew, store_get_ne _ _ (by decide +native)]
  rw [suckStoreDaiNew, store_get_ne _ _ (by decide +native)]
  rw [suckStoreSinNew, store_get_ne _ _ (by decide +native), suckStore_debt]

theorem suckStoreDebtNew_debt (I : ExecutionEnv)
    (sinNew daiNew viceNew debtNew : UInt256) :
    (suckStoreDebtNew I sinNew daiNew viceNew debtNew).get? "debt" = none := by
  rw [suckStoreDebtNew, store_get_ne _ _ (by decide +native), suckStoreViceNew_debt]

theorem suckStore_wards (I : ExecutionEnv) :
    (suckStore I).get? "wards" = none := by
  unfold suckStore
  repeat rw [store_get_ne _ _ (by decide +native)]
  simp

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_suck_sin_u (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hu : locals.get? "u" = some (suckUValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (sinRef (.var "u")) = .ok (suckSinEvaledRef I) := by
  simp [suckSinEvaledRef, suckUValue, suckUKey, sinRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hu]

theorem evalExpr_suck_sin_u_old (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := suckStore I } evm
        (.storage (sinRef (.var "u"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := suckStore_sin I)
    (her := evalStorageRef_suck_sin_u evm I (suckStore I) (suckStore_get_u I))
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract,
      storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw (suckSinEvaledRef I) evm =
        some (wordLoc (suckSinSlot I))
      simp [storageLayoutRaw, suckSinEvaledRef, suckSinSlot])]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (suckSinSlot I))

theorem evalExpr_suck_sin_u (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hu : locals.get? "u" = some (suckUValue I)) (hbase : locals.get? "sin" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (sinRef (.var "u"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_suck_sin_u evm I locals hu)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract,
      storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw (suckSinEvaledRef I) evm =
        some (wordLoc (suckSinSlot I))
      simp [storageLayoutRaw, suckSinEvaledRef, suckSinSlot])]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (suckSinSlot I))

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_suck_dai_v (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hv : locals.get? "v" = some (suckVValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (daiRef (.var "v")) = .ok (suckDaiEvaledRef I) := by
  simp [suckDaiEvaledRef, suckVValue, suckVKey, daiRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hv]

theorem evalExpr_suck_dai_v (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hv : locals.get? "v" = some (suckVValue I)) (hbase : locals.get? "dai" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (daiRef (.var "v"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckDaiSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_suck_dai_v evm I locals hv)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract,
      storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw (suckDaiEvaledRef I) evm =
        some (wordLoc (suckDaiSlot I))
      simp [storageLayoutRaw, suckDaiEvaledRef, suckDaiSlot])]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (suckDaiSlot I))

theorem evalStorageRef_suck_vice (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm viceRef =
      .ok suckViceEvaledRef := by
  simp [evalStorageRef, evalStorageRefSteps, viceRef, suckViceEvaledRef,
    EvalResult.bind, pure, bind]

theorem evalStorageRef_suck_debt (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm debtRef =
      .ok suckDebtEvaledRef := by
  simp [evalStorageRef, evalStorageRefSteps, debtRef, suckDebtEvaledRef,
    EvalResult.bind, pure, bind]

theorem evalExpr_suck_vice (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vice" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage viceRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner suckViceSlot).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_suck_vice evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm suckViceSlot)

theorem evalExpr_suck_debt (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "debt" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage debtRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner suckDebtSlot).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_suck_debt evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm suckDebtSlot)

theorem suckEvalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem suckEvalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem suckEvalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
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

theorem assign_suck_sin_u (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (sinNew : UInt256)
    (hu : locals.get? "u" = some (suckUValue I)) (hbase : locals.get? "sin" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (sinRef (.var "u")) (.int (Int.ofNat sinNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (suckSinSlot I))
    (hbase := hbase)
    (her := evalStorageRef_suck_sin_u evm I locals hu)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw (suckSinEvaledRef I) evm = some (wordLoc (suckSinSlot I))
      simp [storageLayoutRaw, suckSinEvaledRef, suckSinSlot])
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm (suckSinSlot I) sinNew)

theorem assign_suck_dai_v (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (daiNew : UInt256)
    (hv : locals.get? "v" = some (suckVValue I)) (hbase : locals.get? "dai" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckDaiSlot I) daiNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (daiRef (.var "v")) (.int (Int.ofNat daiNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (suckDaiSlot I))
    (hbase := hbase)
    (her := evalStorageRef_suck_dai_v evm I locals hv)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw (suckDaiEvaledRef I) evm = some (wordLoc (suckDaiSlot I))
      simp [storageLayoutRaw, suckDaiEvaledRef, suckDaiSlot])
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm (suckDaiSlot I) daiNew)

theorem assign_suck_vice (evm : EVM.State) (locals : Store) (viceNew : UInt256)
    (hbase : locals.get? "vice" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner suckViceSlot viceNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage viceRef (.int (Int.ofNat viceNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc suckViceSlot)
    (hbase := hbase)
    (her := evalStorageRef_suck_vice evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm suckViceSlot viceNew)

theorem assign_suck_debt (evm : EVM.State) (locals : Store) (debtNew : UInt256)
    (hbase : locals.get? "debt" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner suckDebtSlot debtNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc suckDebtSlot)
    (hbase := hbase)
    (her := evalStorageRef_suck_debt evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm suckDebtSlot debtNew)

theorem vatSuckSinAddBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinVal sinNew : UInt256}
    (hsinLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I) = sinVal)
    (hsinNew : sinNew = sinVal + suckRadWord I)
    (hsinFit : sinVal.toNat + (suckRadWord I).toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := suckStore I } evm
      (checkedAddUintInto "sinNew" (.storage (sinRef (.var "u"))) (.var "rad"))
      (.ok { contract := contract, locals := suckStoreSinNew I sinNew } evm) := by
  have hrad :
      evalExpr? config { contract := contract, locals := suckStore I } evm (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStore I) (name := "rad")
      (value := suckRadWord I) (suckStore_get_rad I)
  have hsin :
      evalExpr? config { contract := contract, locals := suckStore I } evm
          (.storage (sinRef (.var "u"))) =
        .ok (.int (Int.ofNat sinVal.toNat)) := by
    simpa [hsinLoad] using evalExpr_suck_sin_u_old (evm := evm) (I := I)
  have hadd :
      evalExpr? config { contract := contract, locals := suckStore I } evm
          (add256 (.storage (sinRef (.var "u"))) (.var "rad")) =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    suckEvalExpr_add256_ok hsin hrad hsinNew hsinFit
  have hsinNewEval :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreSinNew I sinNew)
      (name := "sinNew") (value := sinNew) (suckStoreSinNew_get_sinNew I sinNew)
  have hsinAgain :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.storage (sinRef (.var "u"))) =
        .ok (.int (Int.ofNat sinVal.toNat)) := by
    simpa [hsinLoad] using
      evalExpr_suck_sin_u evm I (suckStoreSinNew I sinNew)
        (suckStoreSinNew_get_u I sinNew) (suckStoreSinNew_sin I sinNew)
  have hsinNewNat : sinNew.toNat = sinVal.toNat + (suckRadWord I).toNat := by
    rw [hsinNew, uadd_toNat, Nat.mod_eq_of_lt hsinFit]
  have hreq :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.binary .ge (.var "sinNew") (.storage (sinRef (.var "u")))) =
        .ok (.bool true) :=
    suckEvalExpr_ge_uint256_true hsinNewEval hsinAgain (by rw [hsinNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hadd) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatSuckAssignSinOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew : UInt256} :
    ExecBlock config { contract := contract, locals := suckStoreSinNew I sinNew } evm
      [ .assign .storage (sinRef (.var "u")) (.var "sinNew") ]
      (.ok { contract := contract, locals := suckStoreSinNew I sinNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew)) := by
  have hsinNewEval :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreSinNew I sinNew)
      (name := "sinNew") (value := sinNew) (suckStoreSinNew_get_sinNew I sinNew)
  have hassign :
      assignStorageRef? config { contract := contract, locals := suckStoreSinNew I sinNew }
          evm .storage (sinRef (.var "u")) (.int (Int.ofNat sinNew.toNat)) =
        .ok ({ contract := contract, locals := suckStoreSinNew I sinNew },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew) := by
    simpa using assign_suck_sin_u evm I (suckStoreSinNew I sinNew) sinNew
      (suckStoreSinNew_get_u I sinNew) (suckStoreSinNew_sin I sinNew)
  exact ExecBlock.consNormal (ExecStmt.assign hsinNewEval hassign) ExecBlock.nil

theorem vatSuckDaiAddBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiVal daiNew : UInt256}
    (hdaiLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckDaiSlot I) = daiVal)
    (hdaiNew : daiNew = daiVal + suckRadWord I)
    (hdaiFit : daiVal.toNat + (suckRadWord I).toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := suckStoreSinNew I sinNew } evm
      (checkedAddUintInto "daiNew" (.storage (daiRef (.var "v"))) (.var "rad"))
      (.ok { contract := contract, locals := suckStoreDaiNew I sinNew daiNew } evm) := by
  have hrad :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreSinNew I sinNew)
      (name := "rad") (value := suckRadWord I) (suckStoreSinNew_get_rad I sinNew)
  have hdai :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.storage (daiRef (.var "v"))) =
        .ok (.int (Int.ofNat daiVal.toNat)) := by
    simpa [hdaiLoad] using
      evalExpr_suck_dai_v evm I (suckStoreSinNew I sinNew)
        (suckStoreSinNew_get_v I sinNew) (suckStoreSinNew_dai I sinNew)
  have hadd :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (add256 (.storage (daiRef (.var "v"))) (.var "rad")) =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    suckEvalExpr_add256_ok hdai hrad hdaiNew hdaiFit
  have hdaiNewEval :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (.var "daiNew") =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreDaiNew I sinNew daiNew)
      (name := "daiNew") (value := daiNew) (suckStoreDaiNew_get_daiNew I sinNew daiNew)
  have hdaiAgain :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (.storage (daiRef (.var "v"))) =
        .ok (.int (Int.ofNat daiVal.toNat)) := by
    simpa [hdaiLoad] using
      evalExpr_suck_dai_v evm I (suckStoreDaiNew I sinNew daiNew)
        (suckStoreDaiNew_get_v I sinNew daiNew) (suckStoreDaiNew_dai I sinNew daiNew)
  have hdaiNewNat : daiNew.toNat = daiVal.toNat + (suckRadWord I).toNat := by
    rw [hdaiNew, uadd_toNat, Nat.mod_eq_of_lt hdaiFit]
  have hreq :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (.binary .ge (.var "daiNew") (.storage (daiRef (.var "v")))) =
        .ok (.bool true) :=
    suckEvalExpr_ge_uint256_true hdaiNewEval hdaiAgain (by rw [hdaiNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hadd) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatSuckDaiAddBlockRevert (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiVal : UInt256}
    (hdaiLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckDaiSlot I) = daiVal)
    (hdaiOverflow : UInt256.size ≤ daiVal.toNat + (suckRadWord I).toNat) :
    ExecBlock config { contract := contract, locals := suckStoreSinNew I sinNew } evm
      (checkedAddUintInto "daiNew" (.storage (daiRef (.var "v"))) (.var "rad"))
      .reverted := by
  have hrad :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreSinNew I sinNew)
      (name := "rad") (value := suckRadWord I) (suckStoreSinNew_get_rad I sinNew)
  have hdai :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (.storage (daiRef (.var "v"))) =
        .ok (.int (Int.ofNat daiVal.toNat)) := by
    simpa [hdaiLoad] using
      evalExpr_suck_dai_v evm I (suckStoreSinNew I sinNew)
        (suckStoreSinNew_get_v I sinNew) (suckStoreSinNew_dai I sinNew)
  have hadd :
      evalExpr? config { contract := contract, locals := suckStoreSinNew I sinNew } evm
          (add256 (.storage (daiRef (.var "v"))) (.var "rad")) = .revert :=
    suckEvalExpr_add256_revert hdai hrad hdaiOverflow
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)

theorem vatSuckAssignDaiOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew : UInt256} :
    ExecBlock config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew } evm
      [ .assign .storage (daiRef (.var "v")) (.var "daiNew") ]
      (.ok { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckDaiSlot I) daiNew)) := by
  have hdaiNewEval :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew } evm
          (.var "daiNew") =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreDaiNew I sinNew daiNew)
      (name := "daiNew") (value := daiNew) (suckStoreDaiNew_get_daiNew I sinNew daiNew)
  have hassign :
      assignStorageRef? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm .storage (daiRef (.var "v")) (.int (Int.ofNat daiNew.toNat)) =
        .ok ({ contract := contract, locals := suckStoreDaiNew I sinNew daiNew },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckDaiSlot I) daiNew) := by
    simpa using assign_suck_dai_v evm I (suckStoreDaiNew I sinNew daiNew) daiNew
      (suckStoreDaiNew_get_v I sinNew daiNew) (suckStoreDaiNew_dai I sinNew daiNew)
  exact ExecBlock.consNormal (ExecStmt.assign hdaiNewEval hassign) ExecBlock.nil

theorem vatSuckViceAddBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceVal viceNew : UInt256}
    (hviceLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner suckViceSlot = viceVal)
    (hviceNew : viceNew = viceVal + suckRadWord I)
    (hviceFit : viceVal.toNat + (suckRadWord I).toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew } evm
      (checkedAddUintInto "viceNew" (.storage viceRef) (.var "rad"))
      (.ok { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm) := by
  have hrad :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreDaiNew I sinNew daiNew)
      (name := "rad") (value := suckRadWord I) (suckStoreDaiNew_get_rad I sinNew daiNew)
  have hvice :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceVal.toNat)) := by
    simpa [hviceLoad] using
      evalExpr_suck_vice evm (suckStoreDaiNew I sinNew daiNew)
        (suckStoreDaiNew_vice I sinNew daiNew)
  have hadd :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (add256 (.storage viceRef) (.var "rad")) =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    suckEvalExpr_add256_ok hvice hrad hviceNew hviceFit
  have hviceNewEval :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew }
          evm (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := suckStoreViceNew I sinNew daiNew viceNew) (name := "viceNew")
      (value := viceNew) (suckStoreViceNew_get_viceNew I sinNew daiNew viceNew)
  have hviceAgain :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew }
          evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceVal.toNat)) := by
    simpa [hviceLoad] using
      evalExpr_suck_vice evm (suckStoreViceNew I sinNew daiNew viceNew)
        (suckStoreViceNew_vice I sinNew daiNew viceNew)
  have hviceNewNat : viceNew.toNat = viceVal.toNat + (suckRadWord I).toNat := by
    rw [hviceNew, uadd_toNat, Nat.mod_eq_of_lt hviceFit]
  have hreq :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (.binary .ge (.var "viceNew") (.storage viceRef)) =
        .ok (.bool true) :=
    suckEvalExpr_ge_uint256_true hviceNewEval hviceAgain (by rw [hviceNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hadd) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatSuckViceAddBlockRevert (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceVal : UInt256}
    (hviceLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner suckViceSlot = viceVal)
    (hviceOverflow : UInt256.size ≤ viceVal.toNat + (suckRadWord I).toNat) :
    ExecBlock config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew } evm
      (checkedAddUintInto "viceNew" (.storage viceRef) (.var "rad"))
      .reverted := by
  have hrad :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm) (locals := suckStoreDaiNew I sinNew daiNew)
      (name := "rad") (value := suckRadWord I) (suckStoreDaiNew_get_rad I sinNew daiNew)
  have hvice :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceVal.toNat)) := by
    simpa [hviceLoad] using
      evalExpr_suck_vice evm (suckStoreDaiNew I sinNew daiNew)
        (suckStoreDaiNew_vice I sinNew daiNew)
  have hadd :
      evalExpr? config { contract := contract, locals := suckStoreDaiNew I sinNew daiNew }
          evm (add256 (.storage viceRef) (.var "rad")) = .revert :=
    suckEvalExpr_add256_revert hvice hrad hviceOverflow
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)

theorem vatSuckAssignViceOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew : UInt256} :
    ExecBlock config
      { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
      [ .assign .storage viceRef (.var "viceNew") ]
      (.ok { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner suckViceSlot viceNew)) := by
  have hviceNewEval :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := suckStoreViceNew I sinNew daiNew viceNew) (name := "viceNew")
      (value := viceNew) (suckStoreViceNew_get_viceNew I sinNew daiNew viceNew)
  have hassign :
      assignStorageRef? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew }
          evm .storage viceRef (.int (Int.ofNat viceNew.toNat)) =
        .ok ({ contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner suckViceSlot viceNew) := by
    simpa using assign_suck_vice evm (suckStoreViceNew I sinNew daiNew viceNew) viceNew
      (suckStoreViceNew_vice I sinNew daiNew viceNew)
  exact ExecBlock.consNormal (ExecStmt.assign hviceNewEval hassign) ExecBlock.nil

theorem vatSuckDebtAddBlockOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew debtVal debtNew : UInt256}
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner suckDebtSlot = debtVal)
    (hdebtNew : debtNew = debtVal + suckRadWord I)
    (hdebtFit : debtVal.toNat + (suckRadWord I).toNat < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
      (checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad"))
      (.ok { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
        evm) := by
  have hrad :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := suckStoreViceNew I sinNew daiNew viceNew) (name := "rad")
      (value := suckRadWord I) (suckStoreViceNew_get_rad I sinNew daiNew viceNew)
  have hdebt :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (.storage debtRef) =
        .ok (.int (Int.ofNat debtVal.toNat)) := by
    simpa [hdebtLoad] using
      evalExpr_suck_debt evm (suckStoreViceNew I sinNew daiNew viceNew)
        (suckStoreViceNew_debt I sinNew daiNew viceNew)
  have hadd :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (add256 (.storage debtRef) (.var "rad")) =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    suckEvalExpr_add256_ok hdebt hrad hdebtNew hdebtFit
  have hdebtNewEval :
      evalExpr? config
          { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
          evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew) (name := "debtNew")
      (value := debtNew) (suckStoreDebtNew_get_debtNew I sinNew daiNew viceNew debtNew)
  have hdebtAgain :
      evalExpr? config
          { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
          evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtVal.toNat)) := by
    simpa [hdebtLoad] using
      evalExpr_suck_debt evm (suckStoreDebtNew I sinNew daiNew viceNew debtNew)
        (suckStoreDebtNew_debt I sinNew daiNew viceNew debtNew)
  have hdebtNewNat : debtNew.toNat = debtVal.toNat + (suckRadWord I).toNat := by
    rw [hdebtNew, uadd_toNat, Nat.mod_eq_of_lt hdebtFit]
  have hreq :
      evalExpr? config
          { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
          evm (.binary .ge (.var "debtNew") (.storage debtRef)) =
        .ok (.bool true) :=
    suckEvalExpr_ge_uint256_true hdebtNewEval hdebtAgain (by rw [hdebtNewNat]; omega)
  refine ExecBlock.consNormal (ExecStmt.letDecl hadd) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.nil

theorem vatSuckDebtAddBlockRevert (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew debtVal : UInt256}
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner suckDebtSlot = debtVal)
    (hdebtOverflow : UInt256.size ≤ debtVal.toNat + (suckRadWord I).toNat) :
    ExecBlock config
      { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
      (checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad"))
      .reverted := by
  have hrad :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := suckStoreViceNew I sinNew daiNew viceNew) (name := "rad")
      (value := suckRadWord I) (suckStoreViceNew_get_rad I sinNew daiNew viceNew)
  have hdebt :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (.storage debtRef) =
        .ok (.int (Int.ofNat debtVal.toNat)) := by
    simpa [hdebtLoad] using
      evalExpr_suck_debt evm (suckStoreViceNew I sinNew daiNew viceNew)
        (suckStoreViceNew_debt I sinNew daiNew viceNew)
  have hadd :
      evalExpr? config
          { contract := contract, locals := suckStoreViceNew I sinNew daiNew viceNew } evm
          (add256 (.storage debtRef) (.var "rad")) = .revert :=
    suckEvalExpr_add256_revert hdebt hrad hdebtOverflow
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)

theorem vatSuckAssignDebtOk (evm : EVM.State) (I : ExecutionEnv)
    {sinNew daiNew viceNew debtNew : UInt256} :
    ExecBlock config
      { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew } evm
      [ .assign .storage debtRef (.var "debtNew") ]
      (.ok { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner suckDebtSlot debtNew)) := by
  have hdebtNewEval :
      evalExpr? config
          { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
          evm (.var "debtNew") =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm)
      (locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew) (name := "debtNew")
      (value := debtNew) (suckStoreDebtNew_get_debtNew I sinNew daiNew viceNew debtNew)
  have hassign :
      assignStorageRef? config
          { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
          evm .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
        .ok ({ contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner suckDebtSlot debtNew) := by
    simpa using assign_suck_debt evm (suckStoreDebtNew I sinNew daiNew viceNew debtNew) debtNew
      (suckStoreDebtNew_debt I sinNew daiNew viceNew debtNew)
  exact ExecBlock.consNormal (ExecStmt.assign hdebtNewEval hassign) ExecBlock.nil

theorem vatSuckSourceSuccess (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := suckStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hsinFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)).toNat +
        (suckRadWord I).toNat < UInt256.size) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)
    let sinNew := sinVal + suckRadWord I
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I)
    let daiNew := daiVal + suckRadWord I
    let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) daiNew
    let viceVal := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot
    let viceNew := viceVal + suckRadWord I
    let evmVice := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner suckViceSlot viceNew
    let debtVal := Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner suckDebtSlot
    let debtNew := debtVal + suckRadWord I
    daiVal.toNat + (suckRadWord I).toNat < UInt256.size →
    viceVal.toNat + (suckRadWord I).toNat < UInt256.size →
    debtVal.toNat + (suckRadWord I).toNat < UInt256.size →
    ExecTransitionBody config contract evm (suckStore I) suckTransition.body
      (.returned { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
        (suckPostState evm I sinNew daiNew viceNew debtNew) none) := by
  intro sinVal sinNew evmSin daiVal daiNew evmDai viceVal viceNew evmVice debtVal debtNew
    hdaiFit hviceFit hdebtFit
  have hsinLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I) = sinVal := rfl
  have hdaiLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) = daiVal := rfl
  have hviceLoad :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot = viceVal := rfl
  have hdebtLoad :
      Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner suckDebtSlot = debtVal := rfl
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    exact ExecBlock.consNormal (ExecStmt.requireTrue hauth) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm I (sinVal := sinVal) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFit
  have hsinAssign := vatSuckAssignSinOk evm I (sinNew := sinNew)
  have hdaiAdd :=
    vatSuckDaiAddBlockOk evmSin I (sinNew := sinNew) (daiVal := daiVal)
      (daiNew := daiNew) hdaiLoad (by rfl) hdaiFit
  have hdaiAssign := vatSuckAssignDaiOk evmSin I (sinNew := sinNew) (daiNew := daiNew)
  have hviceAdd :=
    vatSuckViceAddBlockOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceVal := viceVal) (viceNew := viceNew) hviceLoad (by rfl) hviceFit
  have hviceAssign :=
    vatSuckAssignViceOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew)
  have hdebtAdd :=
    vatSuckDebtAddBlockOk evmVice I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew) (debtVal := debtVal) (debtNew := debtNew)
      hdebtLoad (by rfl) hdebtFit
  have hdebtAssign :=
    vatSuckAssignDebtOk evmVice I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew) (debtNew := debtNew)
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiAdd
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hviceAdd
  have h06 := execBlock_append h05 hviceAssign
  have h07 := execBlock_append h06 hdebtAdd
  have hblock := execBlock_append h07 hdebtAssign
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc, suckPostState, evmSin, evmDai, evmVice, storageStore_executionEnv] using
    ExecFuncBody.execBlockOK hblock

theorem vatSuckSourceRevertDaiOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := suckStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hsinFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)).toNat +
        (suckRadWord I).toNat < UInt256.size) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)
    let sinNew := sinVal + suckRadWord I
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I)
    UInt256.size ≤ daiVal.toNat + (suckRadWord I).toNat →
    ExecTransitionBody config contract evm (suckStore I) suckTransition.body .reverted := by
  intro sinVal sinNew evmSin daiVal hdaiOverflow
  have hsinLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I) = sinVal := rfl
  have hdaiLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) = daiVal := rfl
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    exact ExecBlock.consNormal (ExecStmt.requireTrue hauth) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm I (sinVal := sinVal) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFit
  have hsinAssign := vatSuckAssignSinOk evm I (sinNew := sinNew)
  have hdaiRevert :=
    vatSuckDaiAddBlockRevert evmSin I (sinNew := sinNew) (daiVal := daiVal)
      hdaiLoad hdaiOverflow
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .assign .storage (daiRef (.var "v")) (.var "daiNew") ] ++
      checkedAddUintInto "viceNew" (.storage viceRef) (.var "rad") ++
      [ .assign .storage viceRef (.var "viceNew") ] ++
      checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ])
    h03 (by intro f' e' h; cases h)
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatSuckSourceRevertDaiOverflowVat
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFit :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hdaiOverflow :
      UInt256.size ≤
        (vatSlotWord (suckDaiSlot I)
          (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I)
            (vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I)) I).toNat +
          (suckRadWord I).toNat) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (suckStore I) suckTransition.body .reverted := by
  intro evm0
  have hguard := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := suckStore I) (suckStore_wards I) hauth
  let sinVal := vatSlotWord (suckSinSlot I) σ_solm I
  let sinNew := sinVal + suckRadWord I
  let evmSin := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I) sinNew
  let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I)
  have hsinLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (suckSinSlot I) = sinVal := by
    simp [sinVal, evm0, initState, Solm.EVM.storageLoad, vatSlotWord,
      State.lookupAccount, Account.lookupStorage]
  have hsinFitLoad : sinVal.toNat + (suckRadWord I).toNat < UInt256.size := by
    simpa [sinVal] using hsinFit
  have hdaiLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) = daiVal := rfl
  have hdaiOverflowLoad :
      UInt256.size ≤ daiVal.toNat + (suckRadWord I).toNat := by
    have hload :
        daiVal =
          vatSlotWord (suckDaiSlot I)
            (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I := by
      simpa [daiVal, evmSin, evm0, sinNew, initState, storageStore_executionEnv] using
        (vatStorageLoad_after_initState_store
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (writeSlot := suckSinSlot I) (readSlot := suckDaiSlot I) (val := sinNew))
    rw [hload]
    simpa [sinNew, sinVal] using hdaiOverflow
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm0) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simpa [evm0, initState] using hwv)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm0 I (sinVal := sinVal) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFitLoad
  have hsinAssign := vatSuckAssignSinOk evm0 I (sinNew := sinNew)
  have hdaiRevert :=
    vatSuckDaiAddBlockRevert evmSin I (sinNew := sinNew) (daiVal := daiVal)
      hdaiLoad hdaiOverflowLoad
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .assign .storage (daiRef (.var "v")) (.var "daiNew") ] ++
      checkedAddUintInto "viceNew" (.storage viceRef) (.var "rad") ++
      [ .assign .storage viceRef (.var "viceNew") ] ++
      checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ])
    h03 (by intro f' e' h; cases h)
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatSuckSourceRevertViceOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := suckStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hsinFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)).toNat +
        (suckRadWord I).toNat < UInt256.size) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)
    let sinNew := sinVal + suckRadWord I
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I)
    let daiNew := daiVal + suckRadWord I
    let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) daiNew
    let viceVal := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot
    daiVal.toNat + (suckRadWord I).toNat < UInt256.size →
    UInt256.size ≤ viceVal.toNat + (suckRadWord I).toNat →
    ExecTransitionBody config contract evm (suckStore I) suckTransition.body .reverted := by
  intro sinVal sinNew evmSin daiVal daiNew evmDai viceVal hdaiFit hviceOverflow
  have hsinLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I) = sinVal := rfl
  have hdaiLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) = daiVal := rfl
  have hviceLoad :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot = viceVal := rfl
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    exact ExecBlock.consNormal (ExecStmt.requireTrue hauth) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm I (sinVal := sinVal) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFit
  have hsinAssign := vatSuckAssignSinOk evm I (sinNew := sinNew)
  have hdaiAdd :=
    vatSuckDaiAddBlockOk evmSin I (sinNew := sinNew) (daiVal := daiVal)
      (daiNew := daiNew) hdaiLoad (by rfl) hdaiFit
  have hdaiAssign := vatSuckAssignDaiOk evmSin I (sinNew := sinNew) (daiNew := daiNew)
  have hviceRevert :=
    vatSuckViceAddBlockRevert evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceVal := viceVal) hviceLoad hviceOverflow
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiAdd
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hviceRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .assign .storage viceRef (.var "viceNew") ] ++
      checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ])
    h05 (by intro f' e' h; cases h)
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatSuckSourceRevertViceOverflowVat
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFit :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size) :
    let sinNew := vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I
    let σSinSolm := sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew
    let daiNew := vatSlotWord (suckDaiSlot I) σSinSolm I + suckRadWord I
    let σDaiSolm := sstoreAccountMap I.codeOwner σSinSolm (suckDaiSlot I) daiNew
    (vatSlotWord (suckDaiSlot I) σSinSolm I).toNat +
      (suckRadWord I).toNat < UInt256.size →
    UInt256.size ≤ (vatSlotWord suckViceSlot σDaiSolm I).toNat + (suckRadWord I).toNat →
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (suckStore I) suckTransition.body .reverted := by
  intro sinNew σSinSolm daiNew σDaiSolm hdaiFit hviceOverflow evm0
  have hguard := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := suckStore I) (suckStore_wards I) hauth
  have hsinLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (suckSinSlot I) =
        vatSlotWord (suckSinSlot I) σ_solm I := by
    simp [evm0, initState, Solm.EVM.storageLoad, vatSlotWord,
      State.lookupAccount, Account.lookupStorage]
  have hdaiLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I)
            sinNew)
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I)
            sinNew).executionEnv.codeOwner
          (suckDaiSlot I) =
        vatSlotWord (suckDaiSlot I) σSinSolm I := by
    simpa [evm0, sinNew, σSinSolm, initState, storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (writeSlot := suckSinSlot I) (readSlot := suckDaiSlot I) (val := sinNew))
  have hviceLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I)
              sinNew)
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I)
              sinNew).executionEnv.codeOwner (suckDaiSlot I) daiNew)
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I)
              sinNew)
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I)
              sinNew).executionEnv.codeOwner (suckDaiSlot I) daiNew).executionEnv.codeOwner
          suckViceSlot =
        vatSlotWord suckViceSlot σDaiSolm I := by
    simpa [evm0, sinNew, σSinSolm, daiNew, σDaiSolm, initState,
      storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store₂
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot₁ := suckSinSlot I) (slot₂ := suckDaiSlot I) (readSlot := suckViceSlot)
        (val₁ := sinNew) (val₂ := daiNew))
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm0) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simpa [evm0, initState] using hwv)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm0 I
      (sinVal := vatSlotWord (suckSinSlot I) σ_solm I) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFit
  have hsinAssign := vatSuckAssignSinOk evm0 I (sinNew := sinNew)
  have hdaiAdd :=
    vatSuckDaiAddBlockOk
      (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I) sinNew)
      I (sinNew := sinNew) (daiVal := vatSlotWord (suckDaiSlot I) σSinSolm I)
      (daiNew := daiNew) hdaiLoad (by rfl) hdaiFit
  have hdaiAssign :=
    vatSuckAssignDaiOk
      (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I) sinNew)
      I (sinNew := sinNew) (daiNew := daiNew)
  have hviceRevert :=
    vatSuckViceAddBlockRevert
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I) sinNew)
        (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (suckSinSlot I)
          sinNew).executionEnv.codeOwner (suckDaiSlot I) daiNew)
      I (sinNew := sinNew) (daiNew := daiNew)
      (viceVal := vatSlotWord suckViceSlot σDaiSolm I) hviceLoad hviceOverflow
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiAdd
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hviceRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .assign .storage viceRef (.var "viceNew") ] ++
      checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ])
    h05 (by intro f' e' h; cases h)
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatSuckSourceRevertDebtOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := suckStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hsinFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)).toNat +
        (suckRadWord I).toNat < UInt256.size) :
    let sinVal := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I)
    let sinNew := sinVal + suckRadWord I
    let evmSin := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (suckSinSlot I) sinNew
    let daiVal := Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I)
    let daiNew := daiVal + suckRadWord I
    let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) daiNew
    let viceVal := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot
    let viceNew := viceVal + suckRadWord I
    let evmVice := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner suckViceSlot viceNew
    let debtVal := Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner suckDebtSlot
    daiVal.toNat + (suckRadWord I).toNat < UInt256.size →
    viceVal.toNat + (suckRadWord I).toNat < UInt256.size →
    UInt256.size ≤ debtVal.toNat + (suckRadWord I).toNat →
    ExecTransitionBody config contract evm (suckStore I) suckTransition.body .reverted := by
  intro sinVal sinNew evmSin daiVal daiNew evmDai viceVal viceNew evmVice debtVal
    hdaiFit hviceFit hdebtOverflow
  have hsinLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (suckSinSlot I) = sinVal := rfl
  have hdaiLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) = daiVal := rfl
  have hviceLoad :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot = viceVal := rfl
  have hdebtLoad :
      Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner suckDebtSlot = debtVal := rfl
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    exact ExecBlock.consNormal (ExecStmt.requireTrue hauth) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm I (sinVal := sinVal) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFit
  have hsinAssign := vatSuckAssignSinOk evm I (sinNew := sinNew)
  have hdaiAdd :=
    vatSuckDaiAddBlockOk evmSin I (sinNew := sinNew) (daiVal := daiVal)
      (daiNew := daiNew) hdaiLoad (by rfl) hdaiFit
  have hdaiAssign := vatSuckAssignDaiOk evmSin I (sinNew := sinNew) (daiNew := daiNew)
  have hviceAdd :=
    vatSuckViceAddBlockOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceVal := viceVal) (viceNew := viceNew) hviceLoad (by rfl) hviceFit
  have hviceAssign :=
    vatSuckAssignViceOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew)
  have hdebtRevert :=
    vatSuckDebtAddBlockRevert evmVice I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew) (debtVal := debtVal) hdebtLoad hdebtOverflow
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiAdd
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hviceAdd
  have h06 := execBlock_append h05 hviceAssign
  have h07 := execBlock_append h06 hdebtRevert
  have hblock := execBlock_append_term
    (s2 := [ .assign .storage debtRef (.var "debtNew") ])
    h07 (by intro f' e' h; cases h)
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatSuckSourceRevertDebtOverflowVat
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFit :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size) :
    let sinNew := vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I
    let σSinSolm := sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew
    let daiNew := vatSlotWord (suckDaiSlot I) σSinSolm I + suckRadWord I
    let σDaiSolm := sstoreAccountMap I.codeOwner σSinSolm (suckDaiSlot I) daiNew
    let viceNew := vatSlotWord suckViceSlot σDaiSolm I + suckRadWord I
    let σViceSolm := sstoreAccountMap I.codeOwner σDaiSolm suckViceSlot viceNew
    (vatSlotWord (suckDaiSlot I) σSinSolm I).toNat +
      (suckRadWord I).toNat < UInt256.size →
    (vatSlotWord suckViceSlot σDaiSolm I).toNat +
      (suckRadWord I).toNat < UInt256.size →
    UInt256.size ≤ (vatSlotWord suckDebtSlot σViceSolm I).toNat + (suckRadWord I).toNat →
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (suckStore I) suckTransition.body .reverted := by
  intro sinNew σSinSolm daiNew σDaiSolm viceNew σViceSolm hdaiFit hviceFit
    hdebtOverflow evm0
  have hguard := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := suckStore I) (suckStore_wards I) hauth
  have hsinLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (suckSinSlot I) =
        vatSlotWord (suckSinSlot I) σ_solm I := by
    simp [evm0, initState, Solm.EVM.storageLoad, vatSlotWord,
      State.lookupAccount, Account.lookupStorage]
  let evmSin := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (suckSinSlot I) sinNew
  have hdaiLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) =
        vatSlotWord (suckDaiSlot I) σSinSolm I := by
    simpa [evmSin, evm0, sinNew, σSinSolm, initState, storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (writeSlot := suckSinSlot I) (readSlot := suckDaiSlot I) (val := sinNew))
  let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner
    (suckDaiSlot I) daiNew
  have hviceLoad :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot =
        vatSlotWord suckViceSlot σDaiSolm I := by
    simpa [evmDai, evmSin, evm0, sinNew, σSinSolm, daiNew, σDaiSolm, initState,
      storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store₂
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot₁ := suckSinSlot I) (slot₂ := suckDaiSlot I) (readSlot := suckViceSlot)
        (val₁ := sinNew) (val₂ := daiNew))
  let evmVice := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
    suckViceSlot viceNew
  have hdebtLoad :
      Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner suckDebtSlot =
        vatSlotWord suckDebtSlot σViceSolm I := by
    simpa [evmVice, evmDai, evmSin, evm0, sinNew, σSinSolm, daiNew, σDaiSolm,
      viceNew, σViceSolm, initState, storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store₃
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot₁ := suckSinSlot I) (slot₂ := suckDaiSlot I) (slot₃ := suckViceSlot)
        (readSlot := suckDebtSlot) (val₁ := sinNew) (val₂ := daiNew)
        (val₃ := viceNew))
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm0) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simpa [evm0, initState] using hwv)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm0 I
      (sinVal := vatSlotWord (suckSinSlot I) σ_solm I) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFit
  have hsinAssign := vatSuckAssignSinOk evm0 I (sinNew := sinNew)
  have hdaiAdd :=
    vatSuckDaiAddBlockOk evmSin I (sinNew := sinNew)
      (daiVal := vatSlotWord (suckDaiSlot I) σSinSolm I)
      (daiNew := daiNew) hdaiLoad (by rfl) hdaiFit
  have hdaiAssign := vatSuckAssignDaiOk evmSin I (sinNew := sinNew) (daiNew := daiNew)
  have hviceAdd :=
    vatSuckViceAddBlockOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceVal := vatSlotWord suckViceSlot σDaiSolm I) (viceNew := viceNew)
      hviceLoad (by rfl) hviceFit
  have hviceAssign :=
    vatSuckAssignViceOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew)
  have hdebtRevert :=
    vatSuckDebtAddBlockRevert evmVice I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew) (debtVal := vatSlotWord suckDebtSlot σViceSolm I)
      hdebtLoad hdebtOverflow
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiAdd
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hviceAdd
  have h06 := execBlock_append h05 hviceAssign
  have h07 := execBlock_append h06 hdebtRevert
  have hblock := execBlock_append_term
    (s2 := [ .assign .storage debtRef (.var "debtNew") ])
    h07 (by intro f' e' h; cases h)
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatSuckSourceSuccessVat
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFit :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size) :
    let sinNew := vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I
    let σSinSolm := sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew
    let daiNew := vatSlotWord (suckDaiSlot I) σSinSolm I + suckRadWord I
    let σDaiSolm := sstoreAccountMap I.codeOwner σSinSolm (suckDaiSlot I) daiNew
    let viceNew := vatSlotWord suckViceSlot σDaiSolm I + suckRadWord I
    let σViceSolm := sstoreAccountMap I.codeOwner σDaiSolm suckViceSlot viceNew
    let debtNew := vatSlotWord suckDebtSlot σViceSolm I + suckRadWord I
    (vatSlotWord (suckDaiSlot I) σSinSolm I).toNat +
      (suckRadWord I).toNat < UInt256.size →
    (vatSlotWord suckViceSlot σDaiSolm I).toNat +
      (suckRadWord I).toNat < UInt256.size →
    (vatSlotWord suckDebtSlot σViceSolm I).toNat +
      (suckRadWord I).toNat < UInt256.size →
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (suckStore I) suckTransition.body
      (.returned { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
        (suckPostState evm0 I sinNew daiNew viceNew debtNew) none) := by
  intro sinNew σSinSolm daiNew σDaiSolm viceNew σViceSolm debtNew hdaiFit hviceFit
    hdebtFit evm0
  have hguard := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := suckStore I) (suckStore_wards I) hauth
  have hsinLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (suckSinSlot I) =
        vatSlotWord (suckSinSlot I) σ_solm I := by
    simp [evm0, initState, Solm.EVM.storageLoad, vatSlotWord,
      State.lookupAccount, Account.lookupStorage]
  let evmSin := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (suckSinSlot I) sinNew
  have hdaiLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner (suckDaiSlot I) =
        vatSlotWord (suckDaiSlot I) σSinSolm I := by
    simpa [evmSin, evm0, sinNew, σSinSolm, initState, storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (writeSlot := suckSinSlot I) (readSlot := suckDaiSlot I) (val := sinNew))
  let evmDai := Solm.EVM.storageStore evmSin evmSin.executionEnv.codeOwner
    (suckDaiSlot I) daiNew
  have hviceLoad :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner suckViceSlot =
        vatSlotWord suckViceSlot σDaiSolm I := by
    simpa [evmDai, evmSin, evm0, sinNew, σSinSolm, daiNew, σDaiSolm, initState,
      storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store₂
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot₁ := suckSinSlot I) (slot₂ := suckDaiSlot I) (readSlot := suckViceSlot)
        (val₁ := sinNew) (val₂ := daiNew))
  let evmVice := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
    suckViceSlot viceNew
  have hdebtLoad :
      Solm.EVM.storageLoad evmVice evmVice.executionEnv.codeOwner suckDebtSlot =
        vatSlotWord suckDebtSlot σViceSolm I := by
    simpa [evmVice, evmDai, evmSin, evm0, sinNew, σSinSolm, daiNew, σDaiSolm,
      viceNew, σViceSolm, initState, storageStore_executionEnv] using
      (vatStorageLoad_after_initState_store₃
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot₁ := suckSinSlot I) (slot₂ := suckDaiSlot I) (slot₃ := suckViceSlot)
        (readSlot := suckDebtSlot) (val₁ := sinNew) (val₂ := daiNew)
        (val₃ := viceNew))
  let evmDebt := Solm.EVM.storageStore evmVice evmVice.executionEnv.codeOwner
    suckDebtSlot debtNew
  have hprefix :
      ExecBlock config { contract := contract, locals := suckStore I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
        (.ok { contract := contract, locals := suckStore I } evm0) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simpa [evm0, initState] using hwv)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
  have hsinAdd :=
    vatSuckSinAddBlockOk evm0 I
      (sinVal := vatSlotWord (suckSinSlot I) σ_solm I) (sinNew := sinNew)
      hsinLoad (by rfl) hsinFit
  have hsinAssign := vatSuckAssignSinOk evm0 I (sinNew := sinNew)
  have hdaiAdd :=
    vatSuckDaiAddBlockOk evmSin I (sinNew := sinNew)
      (daiVal := vatSlotWord (suckDaiSlot I) σSinSolm I)
      (daiNew := daiNew) hdaiLoad (by rfl) hdaiFit
  have hdaiAssign := vatSuckAssignDaiOk evmSin I (sinNew := sinNew) (daiNew := daiNew)
  have hviceAdd :=
    vatSuckViceAddBlockOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceVal := vatSlotWord suckViceSlot σDaiSolm I) (viceNew := viceNew)
      hviceLoad (by rfl) hviceFit
  have hviceAssign :=
    vatSuckAssignViceOk evmDai I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew)
  have hdebtAdd :=
    vatSuckDebtAddBlockOk evmVice I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew) (debtVal := vatSlotWord suckDebtSlot σViceSolm I)
      (debtNew := debtNew) hdebtLoad (by rfl) hdebtFit
  have hdebtAssign :=
    vatSuckAssignDebtOk evmVice I (sinNew := sinNew) (daiNew := daiNew)
      (viceNew := viceNew) (debtNew := debtNew)
  have h01 := execBlock_append hprefix hsinAdd
  have h02 := execBlock_append h01 hsinAssign
  have h03 := execBlock_append h02 hdaiAdd
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hviceAdd
  have h06 := execBlock_append h05 hviceAssign
  have h07 := execBlock_append h06 hdebtAdd
  have hblock := execBlock_append h07 hdebtAssign
  simpa [ExecTransitionBody, suckTransition, nonpayable, auth, checkedAddUintInto,
    List.append_assoc, suckPostState, evmSin, evmDai, evmVice, evmDebt,
    storageStore_executionEnv] using ExecFuncBody.execBlockOK hblock

theorem vatSuckSourceSuccessVatEq
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    {sinNew daiNew viceNew debtNew : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFit :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hsinNew :
      vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I = sinNew)
    (hdaiFit :
      (vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hdaiNew :
      vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I +
        suckRadWord I = daiNew)
    (hviceFit :
      (vatSlotWord suckViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew) I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hviceNew :
      vatSlotWord suckViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew) I +
        suckRadWord I = viceNew)
    (hdebtFit :
      (vatSlotWord suckDebtSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew)
          suckViceSlot viceNew) I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hdebtNew :
      vatSlotWord suckDebtSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew)
          suckViceSlot viceNew) I +
        suckRadWord I = debtNew) :
    ExecTransitionBody config contract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (suckStore I) suckTransition.body
      (.returned { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
        (suckPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          I sinNew daiNew viceNew debtNew) none) := by
  have hbody :=
    vatSuckSourceSuccessVat
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hwv hauth hsinFit
      (by simpa only [hsinNew] using hdaiFit)
      (by simpa only [hsinNew, hdaiNew] using hviceFit)
      (by simpa only [hsinNew, hdaiNew, hviceNew] using hdebtFit)
  simpa only [hsinNew, hdaiNew, hviceNew, hdebtNew] using hbody

theorem vatSuckSourceRevertSinOverflow
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hover : UInt256.size ≤
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat + (suckRadWord I).toNat) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (suckStore I) suckTransition.body .reverted := by
  intro evm0
  have hsinLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (suckSinSlot I) =
        vatSlotWord (suckSinSlot I) σ_solm I := by
    simp [evm0, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hrad :
      evalExpr? config { contract := contract, locals := suckStore I } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (suckRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := suckStore I) (name := "rad")
      (value := suckRadWord I) (suckStore_get_rad I)
  have hsin :
      evalExpr? config { contract := contract, locals := suckStore I } evm0
          (.storage (sinRef (.var "u"))) =
        .ok (.int (Int.ofNat (vatSlotWord (suckSinSlot I) σ_solm I).toNat)) := by
    simpa [hsinLoad] using evalExpr_suck_sin_u_old (evm := evm0) (I := I)
  have hadd :
      evalExpr? config { contract := contract, locals := suckStore I } evm0
          (add256 (.storage (sinRef (.var "u"))) (.var "rad")) = .revert :=
    suckEvalExpr_add256_revert hsin hrad hover
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := suckStore I) (suckStore_wards I) hauth
  have hblock :
      ExecBlock config { contract := contract, locals := suckStore I } evm0
        suckTransition.body .reverted := by
    change ExecBlock config { contract := contract, locals := suckStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .letDecl "sinNew" (some uint256)
          (add256 (.storage (sinRef (.var "u"))) (.var "rad")),
        .require (.binary .ge (.var "sinNew") (.storage (sinRef (.var "u")))),
        .assign .storage (sinRef (.var "u")) (.var "sinNew"),
        .letDecl "daiNew" (some uint256)
          (add256 (.storage (daiRef (.var "v"))) (.var "rad")),
        .require (.binary .ge (.var "daiNew") (.storage (daiRef (.var "v")))),
        .assign .storage (daiRef (.var "v")) (.var "daiNew"),
        .letDecl "viceNew" (some uint256)
          (add256 (.storage viceRef) (.var "rad")),
        .require (.binary .ge (.var "viceNew") (.storage viceRef)),
        .assign .storage viceRef (.var "viceNew"),
        .letDecl "debtNew" (some uint256)
          (add256 (.storage debtRef) (.var "rad")),
        .require (.binary .ge (.var "debtNew") (.storage debtRef)),
        .assign .storage debtRef (.var "debtNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem vatDecode_suck_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
      (transitionSignature suckTransition).paramTypes I.calldata = some (suckStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["u", "v", "rad"]
    [addr, addr, uint256] I.calldata = _
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["u", "v", "rad"]
      [abiAddress, abiAddress, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "u"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "v"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "rad"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact
    decodeCalldata_legacyAddress_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "u") (y := "v") (z := "rad") hsz100

theorem vatDecode_suck_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
      (transitionSignature suckTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["u", "v", "rad"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["u", "v", "rad"]
    [abiAddress, abiAddress, abiUInt256] I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "u") (y := "v") (z := "rad") hsz4 hshort

theorem vatDispatchSuck {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 24)) :
    dispatchMsg contract I.calldata = some suckTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 24 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some suckTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes, initSelectorBytes,
    liveSelectorBytes, moveSelectorBytes, nopeSelectorBytes, relySelectorBytes,
    sinSelectorBytes, slipSelectorBytes, suckSelectorBytes]
  decide +native

theorem vatReachSuckBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 24)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1543⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xf24e23eb⟩ :=
    vatSelWord_eq_of_beq I hsz 0xf2 0x4e 0x23 0xeb ⟨0xf24e23eb⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms65Body 2 (by omega) ⟨1543⟩ hcode hwv hsz hsize
    hroot hhigh hhighhigh heq0 htake (by jump_dest) (by decide +native)

theorem vatSuckX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1543⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6190⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1543⟩) (ret := ⟨524⟩)
    (decoded := ⟨1565⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hmasked⟩ := RD.solcAddressAddressUint256ExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨1565⟩) (ret := ⟨524⟩) (routine := ⟨6190⟩)
    (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [suckRadWord, suckVMaskedWord, suckUMaskedWord, suckVWord, suckUWord,
      calldataWord] using hmasked⟩

theorem vatSuckX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1543⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1543⟩) (ret := ⟨524⟩)
    (decoded := ⟨1565⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem vatSuckBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsel : selIs I (vatSelBytes 24))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1543⟩ [vatSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatSuckX_shortarg (g := Sat256.ofUInt256 g) hsz4 hshort hsize hreach)
    |>.reEquivDecodingFailed hcode (vatDispatchSuck hsel)
      (vatDecode_suck_none_short hsz4 hshort)

theorem RD.vatSuckSinLoadToAdd
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {memAuth : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6272⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      memAuth (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : memAuth.size = 96) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6637⟩
      (suckRadWord I ::
        solcSlotWord σ I (solcMappingSlot ⟨6⟩ (suckUMaskedWord I)) ::
        ⟨6307⟩ :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckUMaskedWord I) ⟨6⟩ memAuth)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmaskLiteral :
      UInt256.land (suckUMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        suckUMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (suckUMaskedWord_canonical I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (suckUMaskedWord I) ⟨6⟩ memAuth).readWithPadding 0 64))) =
        solcMappingSlot ⟨6⟩ (suckUMaskedWord I) :=
    twoWordHashMem_solcMappingSlot ⟨6⟩ (suckUMaskedWord I) hmem
  have rd6283pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov)]
  have rd6283₀ := evm_run rd6283pre with [raw and (by decide +native) (by evm_ov)]
  have rd6283 := rd6283₀
  rw [hmaskLiteral] at rd6283
  have rd6287pre := evm_run rd6283 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd6288 := rd6287pre.mstore 0 (wordAt0Mem (suckUMaskedWord I) memAuth)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6292pre := evm_run rd6288 with [
    raw push1 ⟨6⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd6293 := rd6292pre.mstore 0
    (twoWordHashMem (suckUMaskedWord I) ⟨6⟩ memAuth)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6296pre := evm_run rd6293 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd6297 := rd6296pre.keccak256 0 (solcMappingSlot ⟨6⟩ (suckUMaskedWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨k6298, C6298, rd6298raw⟩ := rd6297.sload (by decide +native) (by evm_ov)
  have rd6298 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6298⟩
      (solcSlotWord σ I (solcMappingSlot ⟨6⟩ (suckUMaskedWord I)) ::
        suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckUMaskedWord I) ⟨6⟩ memAuth)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6298 C6298 := by
    simpa [solcSlotWord] using rd6298raw
  have rd6637pre := evm_run rd6298 with [
    raw push2 ⟨6307⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨6637⟩ (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd6637pre.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem RD.vatSuckSinAddOverflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {memAuth : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6272⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      memAuth (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : memAuth.size = 96)
    (hover : UInt256.size ≤
      (vatSlotWord (suckSinSlot I) σ I).toNat + (suckRadWord I).toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hslotEq :
      solcSlotWord σ I (solcMappingSlot ⟨6⟩ (suckUMaskedWord I)) =
        vatSlotWord (suckSinSlot I) σ I := by
    simp [vatSlotWord, suckSinSlot_eq I]
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckSinLoadToAdd h hmem
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (suckSinSlot I) σ I) (b := suckRadWord I) (ret := ⟨6307⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa [hslotEq] using hroutine)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hover (by simp)

theorem RD.vatSuckSinAddSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {memAuth : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6272⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      memAuth (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : memAuth.size = 96)
    (hfit :
      (vatSlotWord (suckSinSlot I) σ I).toNat + (suckRadWord I).toNat < UInt256.size) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6307⟩
      ((vatSlotWord (suckSinSlot I) σ I + suckRadWord I) ::
        suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckUMaskedWord I) ⟨6⟩ memAuth)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslotEq :
      solcSlotWord σ I (solcMappingSlot ⟨6⟩ (suckUMaskedWord I)) =
        vatSlotWord (suckSinSlot I) σ I := by
    simp [vatSlotWord, suckSinSlot_eq I]
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckSinLoadToAdd h hmem
  obtain ⟨_, _, hafter⟩ := RD.solcCheckedAddSuccess
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (suckSinSlot I) σ I) (b := suckRadWord I) (ret := ⟨6307⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa [hslotEq] using hroutine)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hfit (by jump_dest) (by jump_dest) (by simp)
  exact ⟨_, _, hafter⟩

theorem RD.vatSuckSinStore
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel sinNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6307⟩
      (sinNew :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6340⟩
      (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: suckRadWord I ::
        suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckUMaskedWord I) ⟨6⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (suckSinSlot I) sinNew) k' C' := by
  have hmaskLiteral :
      UInt256.land (suckUMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        suckUMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (suckUMaskedWord_canonical I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (suckUMaskedWord I) ⟨6⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨6⟩ (suckUMaskedWord I) :=
    twoWordHashMem_solcMappingSlot ⟨6⟩ (suckUMaskedWord I) hmem
  have hslotEq : solcMappingSlot ⟨6⟩ (suckUMaskedWord I) = suckSinSlot I := by
    rw [suckSinSlot_eq]
  have hmaskDef :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rd6319pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov)]
  have rd6319₀ := evm_run rd6319pre with [raw and (by decide +native) (by evm_ov)]
  have rd6319 := rd6319₀
  rw [hmaskLiteral] at rd6319
  have rd6322pre := evm_run rd6319 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd6323 := rd6322pre.mstore 0 (wordAt0Mem (suckUMaskedWord I) mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6330pre := evm_run rd6323 with [
    raw push1 ⟨6⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd6331 := rd6330pre.mstore 0
    (twoWordHashMem (suckUMaskedWord I) ⟨6⟩ mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6335pre := evm_run rd6331 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov)]
  have rd6336 := rd6335pre.keccak256 0 (solcMappingSlot ⟨6⟩ (suckUMaskedWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd6339pre := evm_run rd6336 with [
    raw swap5 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd6340raw⟩ := rd6339pre.sstore hperm (by decide +native) (by evm_ov)
  have hpc :
      ({ val := 6307 } + { val := 1 } + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + { val := 1 } + { val := 1 } + { val := 1 } +
          { val := 1 } + { val := 1 } + UInt256.ofNat 2 + { val := 1 } +
          { val := 1 } + { val := 1 } + UInt256.ofNat 2 + UInt256.ofNat 2 +
          { val := 1 } + { val := 1 } + { val := 1 } + UInt256.ofNat 2 +
          { val := 1 } + { val := 1 } + { val := 1 } + { val := 1 } +
          { val := 1 } + { val := 1 } + { val := 1 } : UInt256) = ⟨6340⟩ := by
    decide +native
  have rd6340 := rd6340raw
  rw [hpc] at rd6340
  exact ⟨_, _, by simpa [hslotEq, hmaskDef] using rd6340⟩

theorem RD.vatSuckDaiLoadToAdd
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6340⟩
      (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: suckRadWord I ::
        suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6637⟩
      (suckRadWord I ::
        solcSlotWord σ I (solcMappingSlot ⟨5⟩ (suckVMaskedWord I)) ::
        ⟨6361⟩ :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmaskLiteral :
      UInt256.land (suckVMaskedWord I) solcAddrMask = suckVMaskedWord I :=
    solcAddrMask_clean (suckVMaskedWord_canonical I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ (suckVMaskedWord I) :=
    twoWordHashMem_solcMappingSlot ⟨5⟩ (suckVMaskedWord I) hmem
  have rd6342pre := evm_run h with [
    raw swap2 (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov)]
  have rd6343₀ := evm_run rd6342pre with [raw and (by decide +native) (by evm_ov)]
  have rd6343 := rd6343₀
  rw [hmaskLiteral] at rd6343
  have rd6344pre := evm_run rd6343 with [raw dup2 (by decide +native) (by evm_ov)]
  have rd6345 := rd6344pre.mstore 0 (wordAt0Mem (suckVMaskedWord I) mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6349pre := evm_run rd6345 with [
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have rd6350 := rd6349pre.mstore 0
    (twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6351 := rd6350.keccak256 0 (solcMappingSlot ⟨5⟩ (suckVMaskedWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨k6352, C6352, rd6352raw⟩ := rd6351.sload (by decide +native) (by evm_ov)
  have rd6352 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6352⟩
      (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (suckVMaskedWord I)) ::
        suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6352 C6352 := by
    simpa [solcSlotWord] using rd6352raw
  have rd6637pre := evm_run rd6352 with [
    raw push2 ⟨6361⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨6637⟩ (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd6637pre.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem RD.vatSuckDaiAddOverflow
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6340⟩
      (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: suckRadWord I ::
        suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hover : UInt256.size ≤
      (vatSlotWord (suckDaiSlot I) σ I).toNat + (suckRadWord I).toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) := by
  have hslotEq :
      solcSlotWord σ I (solcMappingSlot ⟨5⟩ (suckVMaskedWord I)) =
        vatSlotWord (suckDaiSlot I) σ I := by
    simp [vatSlotWord, suckDaiSlot_eq I]
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckDaiLoadToAdd h hmem
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (suckDaiSlot I) σ I) (b := suckRadWord I) (ret := ⟨6361⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa [hslotEq] using hroutine)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hover (by simp)

theorem RD.vatSuckDaiAddSuccess
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6340⟩
      (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: suckRadWord I ::
        suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hfit :
      (vatSlotWord (suckDaiSlot I) σ I).toNat + (suckRadWord I).toNat < UInt256.size) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6361⟩
      ((vatSlotWord (suckDaiSlot I) σ I + suckRadWord I) ::
        suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslotEq :
      solcSlotWord σ I (solcMappingSlot ⟨5⟩ (suckVMaskedWord I)) =
        vatSlotWord (suckDaiSlot I) σ I := by
    simp [vatSlotWord, suckDaiSlot_eq I]
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckDaiLoadToAdd h hmem
  obtain ⟨_, _, hafter⟩ := RD.solcCheckedAddSuccess
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (suckDaiSlot I) σ I) (b := suckRadWord I) (ret := ⟨6361⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa [hslotEq] using hroutine)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hfit (by jump_dest) (by jump_dest) (by simp)
  exact ⟨_, _, hafter⟩

theorem RD.vatSuckDaiStore
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel daiNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6361⟩
      (daiNew :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6387⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (suckDaiSlot I) daiNew) k' C' := by
  have hmaskLiteral :
      UInt256.land (suckVMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        suckVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (suckVMaskedWord_canonical I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ (suckVMaskedWord I) :=
    twoWordHashMem_solcMappingSlot ⟨5⟩ (suckVMaskedWord I) hmem
  have hslotEq : solcMappingSlot ⟨5⟩ (suckVMaskedWord I) = suckDaiSlot I := by
    rw [suckDaiSlot_eq]
  have rd6371pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov)]
  have rd6372₀ := evm_run rd6371pre with [raw and (by decide +native) (by evm_ov)]
  have rd6372 := rd6372₀
  rw [hmaskLiteral] at rd6372
  have rd6375pre := evm_run rd6372 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd6376 := rd6375pre.mstore 0 (wordAt0Mem (suckVMaskedWord I) mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6381pre := evm_run rd6376 with [
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd6382 := rd6381pre.mstore 0
    (twoWordHashMem (suckVMaskedWord I) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd6385pre := evm_run rd6382 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd6386 := rd6385pre.keccak256 0 (solcMappingSlot ⟨5⟩ (suckVMaskedWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd6387raw⟩ := rd6386.sstore hperm (by decide +native) (by evm_ov)
  have hpc :
      ({ val := 6361 } + { val := 1 } + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + { val := 1 } + { val := 1 } + { val := 1 } +
          { val := 1 } + UInt256.ofNat 2 + { val := 1 } + { val := 1 } +
          { val := 1 } + UInt256.ofNat 2 + UInt256.ofNat 2 + { val := 1 } +
          UInt256.ofNat 2 + { val := 1 } + { val := 1 } + { val := 1 } : UInt256) =
        ⟨6387⟩ := by
    decide +native
  have rd6387 := rd6387raw
  rw [hpc] at rd6387
  exact ⟨_, _, by simpa [hslotEq] using rd6387⟩

theorem RD.vatSuckViceLoadToAdd
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6387⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6637⟩
      (suckRadWord I :: vatSlotWord suckViceSlot σ I :: ⟨6399⟩ ::
        suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k6390, C6390, rd6390raw⟩ :=
    (h.push1 ⟨8⟩ (by decide +native) (by evm_ov)).sload (by decide +native) (by evm_ov)
  have rd6390 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6390⟩
      (vatSlotWord suckViceSlot σ I :: suckRadWord I :: suckVMaskedWord I ::
        suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6390 C6390 := by
    simpa [vatSlotWord, suckViceSlot, solcSlotWord] using rd6390raw
  have rd6637pre := evm_run rd6390 with [
    raw push2 ⟨6399⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨6637⟩ (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd6637pre.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem RD.vatSuckViceAddOverflow
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6387⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hover : UInt256.size ≤ (vatSlotWord suckViceSlot σ I).toNat + (suckRadWord I).toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckViceLoadToAdd h
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord suckViceSlot σ I) (b := suckRadWord I) (ret := ⟨6399⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa using hroutine)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hover (by simp)

theorem RD.vatSuckViceAddSuccess
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6387⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfit : (vatSlotWord suckViceSlot σ I).toNat + (suckRadWord I).toNat < UInt256.size) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6399⟩
      ((vatSlotWord suckViceSlot σ I + suckRadWord I) :: suckRadWord I ::
        suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckViceLoadToAdd h
  obtain ⟨_, _, hafter⟩ := RD.solcCheckedAddSuccess
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord suckViceSlot σ I) (b := suckRadWord I) (ret := ⟨6399⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa using hroutine)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hfit (by jump_dest) (by jump_dest) (by simp)
  exact ⟨_, _, hafter⟩

theorem RD.vatSuckViceStore
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel viceNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6399⟩
      (viceNew :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6403⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ suckViceSlot viceNew) k' C' := by
  have rd6402pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨8⟩ (by decide +native) (by evm_ov)]
  exact rd6402pre.sstore hperm (by decide +native) (by evm_ov)

theorem RD.vatSuckDebtLoadToAdd
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6403⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6637⟩
      (suckRadWord I :: vatSlotWord suckDebtSlot σ I :: ⟨6415⟩ ::
        suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k6406, C6406, rd6406raw⟩ :=
    (h.push1 ⟨7⟩ (by decide +native) (by evm_ov)).sload (by decide +native) (by evm_ov)
  have rd6406 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6406⟩
      (vatSlotWord suckDebtSlot σ I :: suckRadWord I :: suckVMaskedWord I ::
        suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6406 C6406 := by
    simpa [vatSlotWord, suckDebtSlot, solcSlotWord] using rd6406raw
  have rd6637pre := evm_run rd6406 with [
    raw push2 ⟨6415⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨6637⟩ (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd6637pre.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem RD.vatSuckDebtAddOverflow
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6403⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hover : UInt256.size ≤ (vatSlotWord suckDebtSlot σ I).toNat + (suckRadWord I).toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckDebtLoadToAdd h
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord suckDebtSlot σ I) (b := suckRadWord I) (ret := ⟨6415⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa using hroutine)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hover (by simp)

theorem RD.vatSuckDebtAddSuccess
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6403⟩
      (suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfit : (vatSlotWord suckDebtSlot σ I).toNat + (suckRadWord I).toNat < UInt256.size) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6415⟩
      ((vatSlotWord suckDebtSlot σ I + suckRadWord I) :: suckRadWord I ::
        suckVMaskedWord I :: suckUMaskedWord I :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, hroutine⟩ := RD.vatSuckDebtLoadToAdd h
  obtain ⟨_, _, hafter⟩ := RD.solcCheckedAddSuccess
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord suckDebtSlot σ I) (b := suckRadWord I) (ret := ⟨6415⟩)
    (R := [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel])
    (by simpa using hroutine)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    hfit (by jump_dest) (by jump_dest) (by simp)
  exact ⟨_, _, hafter⟩

theorem RD.vatSuckDebtStoreReturn
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel debtNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6415⟩
      (debtNew :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩
      [sel] mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ suckDebtSlot debtNew) k' C' := by
  have rd6418pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨7⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd6419⟩ := rd6418pre.sstore hperm (by decide +native) (by evm_ov)
  exact ⟨_, _, evm_run rd6419 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]⟩

theorem RD.vatSuckDebtStoreStop
    {cA gh bl σi σ σ₀ A I} {g : UInt256} {k C : ℕ} {sel debtNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I) ⟨6415⟩
      (debtNew :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σi σ₀ (Sat256.ofUInt256 g) A I)
      (cA, sstoreAccountMap I.codeOwner σ suckDebtSlot debtNew)
      ByteArray.empty := by
  obtain ⟨_, _, rd524⟩ := RD.vatSuckDebtStoreReturn h hperm
  have rd525 := rd524.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd525 (by decide +native) (by evm_ov)

theorem vatSuckFinishSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel sinNew daiNew viceNew debtNew : UInt256}
    {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg contract I.calldata = some suckTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
        (transitionSignature suckTransition).paramTypes I.calldata = some (suckStore I))
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (suckStore I) suckTransition.body
        (.returned { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
          (suckPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            I sinNew daiNew viceNew debtNew) none))
    (hAccountsDebt :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
              (suckDaiSlot I) daiNew)
            suckViceSlot viceNew)
          suckDebtSlot debtNew)
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
              (suckDaiSlot I) daiNew)
            suckViceSlot viceNew)
          suckDebtSlot debtNew))
    (hdebtOk : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6415⟩
      (debtNew :: suckRadWord I :: suckVMaskedWord I :: suckUMaskedWord I ::
        ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew)
        suckViceSlot viceNew) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hret := RD.vatSuckDebtStoreStop
    (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm)
    (σ := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
        (suckDaiSlot I) daiNew)
      suckViceSlot viceNew)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) (debtNew := debtNew)
    (mem := mem) hdebtOk hperm
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew)
          suckViceSlot viceNew)
        suckDebtSlot debtNew).1 =
        (suckPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          I sinNew daiNew viceNew debtNew).createdAccounts := by
    simp [suckPostState, initState, storageStore_createdAccounts]
  have haccountsFinal :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
              (suckDaiSlot I) daiNew)
            suckViceSlot viceNew)
          suckDebtSlot debtNew)
        (suckPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          I sinNew daiNew viceNew debtNew).accountMap := by
    simpa [suckPostState, initState, storageStore_accountMap, storageStore_executionEnv] using
      hAccountsDebt
  have henc : returnEquiv ByteArray.empty none suckTransition.returnType := by
    rw [show suckTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated haccountsFinal henc

theorem vatSuckAfterDaiViceOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel sinNew daiNew : UInt256}
    {mem : ByteArray} {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some suckTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
        (transitionSignature suckTransition).paramTypes I.calldata = some (suckStore I))
    (hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFitSolmVat :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hsinNewSolm :
      vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I = sinNew)
    (hdaiFitSolmVat :
      (vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hdaiNewSolm :
      vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I +
        suckRadWord I = daiNew)
    (hAccountsDai :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew)
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew))
    (hafterDaiStore : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6387⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
        (suckDaiSlot I) daiNew) k C)
    (hviceOverflow :
      UInt256.size ≤
        (vatSlotWord suckViceSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew) I).toNat +
          (suckRadWord I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σDaiEvm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
    (suckDaiSlot I) daiNew
  let σDaiSolm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
    (suckDaiSlot I) daiNew
  have hviceWord :
      vatSlotWord suckViceSlot σDaiEvm I =
        vatSlotWord suckViceSlot σDaiSolm I :=
    accountMapEquiv_storage_findD hAccountsDai I.codeOwner suckViceSlot ⟨0⟩
  have hviceOverflowSolmVat :
      UInt256.size ≤ (vatSlotWord suckViceSlot σDaiSolm I).toNat +
        (suckRadWord I).toNat := by
    rwa [← hviceWord]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (suckStore I) suckTransition.body .reverted :=
    vatSuckSourceRevertViceOverflowVat
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hwv hauthSolm hsinFitSolmVat
      (by simpa only [hsinNewSolm] using hdaiFitSolmVat)
      (by simpa only [σDaiSolm, hsinNewSolm, hdaiNewSolm] using hviceOverflowSolmVat)
  have hrev := RD.vatSuckViceAddOverflow
    (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm) (σ := σDaiEvm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) (mem := mem)
    (by simpa only [σDaiEvm] using hafterDaiStore)
    (by simpa only [σDaiEvm] using hviceOverflow)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatSuckAfterViceDebtOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel sinNew daiNew viceNew : UInt256}
    {mem : ByteArray} {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some suckTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
        (transitionSignature suckTransition).paramTypes I.calldata = some (suckStore I))
    (hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFitSolmVat :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hsinNewSolm :
      vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I = sinNew)
    (hdaiFitSolmVat :
      (vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hdaiNewSolm :
      vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I +
        suckRadWord I = daiNew)
    (hviceFitSolmVat :
      (vatSlotWord suckViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew) I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hviceNewSolm :
      vatSlotWord suckViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew) I +
        suckRadWord I = viceNew)
    (hAccountsVice :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew)
          suckViceSlot viceNew)
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew)
          suckViceSlot viceNew))
    (hafterViceStore : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6403⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew)
        suckViceSlot viceNew) k C)
    (hdebtOverflow :
      UInt256.size ≤
        (vatSlotWord suckDebtSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
              (suckDaiSlot I) daiNew)
            suckViceSlot viceNew) I).toNat +
          (suckRadWord I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σDaiSolm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
    (suckDaiSlot I) daiNew
  let σViceEvm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
      (suckDaiSlot I) daiNew)
    suckViceSlot viceNew
  let σViceSolm := sstoreAccountMap I.codeOwner σDaiSolm suckViceSlot viceNew
  have hdebtWord :
      vatSlotWord suckDebtSlot σViceEvm I =
        vatSlotWord suckDebtSlot σViceSolm I :=
    accountMapEquiv_storage_findD hAccountsVice I.codeOwner suckDebtSlot ⟨0⟩
  have hdebtOverflowSolmVat :
      UInt256.size ≤ (vatSlotWord suckDebtSlot σViceSolm I).toNat +
        (suckRadWord I).toNat := by
    rwa [← hdebtWord]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (suckStore I) suckTransition.body .reverted :=
    vatSuckSourceRevertDebtOverflowVat
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hwv hauthSolm hsinFitSolmVat
      (by simpa only [hsinNewSolm] using hdaiFitSolmVat)
      (by simpa only [σDaiSolm, hsinNewSolm, hdaiNewSolm] using hviceFitSolmVat)
      (by
        simpa only [σDaiSolm, σViceSolm, hsinNewSolm, hdaiNewSolm, hviceNewSolm] using
          hdebtOverflowSolmVat)
  have hrev := RD.vatSuckDebtAddOverflow
    (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm) (σ := σViceEvm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) (mem := mem)
    (by simpa only [σViceEvm] using hafterViceStore)
    (by simpa only [σViceEvm] using hdebtOverflow)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatSuckAfterDebtAddSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel sinNew daiNew viceNew debtNew : UInt256}
    {mem : ByteArray} {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg contract I.calldata = some suckTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
        (transitionSignature suckTransition).paramTypes I.calldata = some (suckStore I))
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (suckStore I) suckTransition.body
        (.returned { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
          (suckPostState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            I sinNew daiNew viceNew debtNew) none))
    (hAccountsVice :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew)
          suckViceSlot viceNew)
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
            (suckDaiSlot I) daiNew)
          suckViceSlot viceNew))
    (hdebtOk : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6415⟩
      [debtNew, suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew)
        suckViceSlot viceNew) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σDaiSolm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
    (suckDaiSlot I) daiNew
  let σViceEvm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
      (suckDaiSlot I) daiNew)
    suckViceSlot viceNew
  let σViceSolm := sstoreAccountMap I.codeOwner σDaiSolm suckViceSlot viceNew
  have hAccountsDebt :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σViceEvm suckDebtSlot debtNew)
        (sstoreAccountMap I.codeOwner σViceSolm suckDebtSlot debtNew) := by
    exact accountMapEquiv_sstoreAccountMap I.codeOwner suckDebtSlot debtNew
      hAccountsVice
  exact vatSuckFinishSuccess
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
    (debtNew := debtNew) (mem := mem)
    hcode hperm hdispatch hdecode hbody
    (by simpa only [σDaiSolm, σViceEvm, σViceSolm] using hAccountsDebt)
    (by simpa only [σViceEvm] using hdebtOk)

theorem vatSuckAfterDaiStore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel sinNew daiNew : UInt256}
    {mem : ByteArray} {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some suckTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
        (transitionSignature suckTransition).paramTypes I.calldata = some (suckStore I))
    (hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hsinFitSolmVat :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hsinNewSolm :
      vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I = sinNew)
    (hdaiFitSolmVat :
      (vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hdaiNewSolm :
      vatSlotWord (suckDaiSlot I)
        (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew) I +
        suckRadWord I = daiNew)
    (hAccountsDai :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew)
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
          (suckDaiSlot I) daiNew))
    (hafterDaiStore : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6387⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
        (suckDaiSlot I) daiNew) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σDaiEvm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
    (suckDaiSlot I) daiNew
  let σDaiSolm := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
    (suckDaiSlot I) daiNew
  have hviceWord :
      vatSlotWord suckViceSlot σDaiEvm I =
        vatSlotWord suckViceSlot σDaiSolm I :=
    accountMapEquiv_storage_findD hAccountsDai I.codeOwner suckViceSlot ⟨0⟩
  by_cases hviceOverflow :
      UInt256.size ≤ (vatSlotWord suckViceSlot σDaiEvm I).toNat +
        (suckRadWord I).toNat
  · exact vatSuckAfterDaiViceOverflow
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (sinNew := sinNew) (daiNew := daiNew) (mem := mem)
      hcode hwv hdispatch hdecode hauthSolm hsinFitSolmVat hsinNewSolm
      hdaiFitSolmVat hdaiNewSolm hAccountsDai hafterDaiStore
      (by simpa only [σDaiEvm] using hviceOverflow)
  · have hviceFit :
        (vatSlotWord suckViceSlot σDaiEvm I).toNat + (suckRadWord I).toNat <
          UInt256.size :=
      Nat.lt_of_not_ge hviceOverflow
    have hviceFitSolmVat :
        (vatSlotWord suckViceSlot σDaiSolm I).toNat + (suckRadWord I).toNat <
          UInt256.size := by
      rwa [← hviceWord]
    let viceNew := vatSlotWord suckViceSlot σDaiEvm I + suckRadWord I
    have hviceNewSolm :
        vatSlotWord suckViceSlot σDaiSolm I + suckRadWord I = viceNew := by
      rw [← hviceWord]
    obtain ⟨_, _, hviceOk⟩ := RD.vatSuckViceAddSuccess
      (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm) (σ := σDaiEvm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) (mem := mem)
      (by simpa only [σDaiEvm] using hafterDaiStore)
      (by simpa only [σDaiEvm] using hviceFit)
    obtain ⟨_, _, hafterViceStore⟩ := RD.vatSuckViceStore
      (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm) (σ := σDaiEvm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (viceNew := viceNew) (mem := mem)
      (by simpa only [viceNew, σDaiEvm] using hviceOk)
      hperm
    let σViceEvm := sstoreAccountMap I.codeOwner σDaiEvm suckViceSlot viceNew
    let σViceSolm := sstoreAccountMap I.codeOwner σDaiSolm suckViceSlot viceNew
    have hAccountsVice : accountMapEquiv σViceEvm σViceSolm := by
      exact accountMapEquiv_sstoreAccountMap I.codeOwner suckViceSlot viceNew hAccountsDai
    have hdebtWord :
        vatSlotWord suckDebtSlot σViceEvm I =
          vatSlotWord suckDebtSlot σViceSolm I :=
      accountMapEquiv_storage_findD hAccountsVice I.codeOwner suckDebtSlot ⟨0⟩
    by_cases hdebtOverflow :
        UInt256.size ≤ (vatSlotWord suckDebtSlot σViceEvm I).toNat +
          (suckRadWord I).toNat
    · exact vatSuckAfterViceDebtOverflow
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
        (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew) (mem := mem)
        hcode hwv hdispatch hdecode hauthSolm hsinFitSolmVat hsinNewSolm
        hdaiFitSolmVat hdaiNewSolm hviceFitSolmVat hviceNewSolm
        (by simpa only [σDaiEvm, σDaiSolm, σViceEvm, σViceSolm] using hAccountsVice)
        (by simpa only [σViceEvm] using hafterViceStore)
        (by simpa only [σViceEvm] using hdebtOverflow)
    · have hdebtFit :
          (vatSlotWord suckDebtSlot σViceEvm I).toNat + (suckRadWord I).toNat <
            UInt256.size :=
        Nat.lt_of_not_ge hdebtOverflow
      have hdebtFitSolmVat :
          (vatSlotWord suckDebtSlot σViceSolm I).toNat + (suckRadWord I).toNat <
            UInt256.size := by
        rwa [← hdebtWord]
      let debtNew := vatSlotWord suckDebtSlot σViceEvm I + suckRadWord I
      have hdebtNewSolm :
          vatSlotWord suckDebtSlot σViceSolm I + suckRadWord I = debtNew := by
        rw [← hdebtWord]
      obtain ⟨_, _, _hdebtOk⟩ := RD.vatSuckDebtAddSuccess
        (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm) (σ := σViceEvm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) (mem := mem)
        (by simpa only [σViceEvm] using hafterViceStore)
        (by simpa only [σViceEvm] using hdebtFit)
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (suckStore I) suckTransition.body
            (.returned { contract := contract, locals := suckStoreDebtNew I sinNew daiNew viceNew debtNew }
              (suckPostState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                I sinNew daiNew viceNew debtNew) none) :=
        vatSuckSourceSuccessVatEq
          (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hwv hauthSolm hsinFitSolmVat hsinNewSolm
          hdaiFitSolmVat hdaiNewSolm hviceFitSolmVat hviceNewSolm
          hdebtFitSolmVat hdebtNewSolm
      exact vatSuckAfterDebtAddSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
        (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
        (debtNew := debtNew) (mem := mem)
        hcode hperm hdispatch hdecode hbody
        (by simpa only [σDaiEvm, σDaiSolm, σViceEvm, σViceSolm] using hAccountsVice)
        (by simpa only [debtNew, σViceEvm] using _hdebtOk)

theorem vatSuckAfterDaiStoreLocal
    {cA gh bl σ_evm σ_solm σ₀ σSinEvm σSinSolm A I} {g sel sinNew daiNew : UInt256}
    {mem : ByteArray} {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some suckTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (suckTransition.params.map Param.name)
        (transitionSignature suckTransition).paramTypes I.calldata = some (suckStore I))
    (hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hσSinEvm : σSinEvm = sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew)
    (hσSinSolm : σSinSolm = sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew)
    (hsinFitSolmVat :
      (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hsinNewSolm :
      vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I = sinNew)
    (hdaiFitSolmVat :
      (vatSlotWord (suckDaiSlot I) σSinSolm I).toNat +
        (suckRadWord I).toNat < UInt256.size)
    (hdaiNewSolm :
      vatSlotWord (suckDaiSlot I) σSinSolm I + suckRadWord I = daiNew)
    (hAccountsDai :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σSinEvm (suckDaiSlot I) daiNew)
        (sstoreAccountMap I.codeOwner σSinSolm (suckDaiSlot I) daiNew))
    (hafterDaiStore : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6387⟩
      [suckRadWord I, suckVMaskedWord I, suckUMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σSinEvm (suckDaiSlot I) daiNew) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  subst σSinEvm
  subst σSinSolm
  exact vatSuckAfterDaiStore
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    (sinNew := sinNew) (daiNew := daiNew) (mem := mem)
    hcode hperm hwv hdispatch hdecode hauthSolm hsinFitSolmVat hsinNewSolm
    hdaiFitSolmVat hdaiNewSolm hAccountsDai hafterDaiStore

theorem vatSuckBodyCore : VatBodyTheorem 24 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 24) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some suckTransition :=
    vatDispatchSuck hsel
  have hreach := vatReachSuckBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := vatDecode_suck_ok (I := I) hsz100
    obtain ⟨_, _, hdecoded⟩ := vatSuckX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    let callerSlot := vatCallerWardsSlot I
    have hcallerWord : vatSlotWord callerSlot σ_evm I = vatSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    by_cases hauthEvm : vatSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : vatSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
        (code := vatBytecode) (pc := ⟨6190⟩) (okPc := ⟨6272⟩)
        (key := suckRadWord I) (ret := suckVMaskedWord I)
        (R := [suckUMaskedWord I, ⟨524⟩, vatSelWord I])
        (by simpa using hdecoded)
        (by
          unfold vatAuthCheckWf
          repeat' first | apply And.intro | decide +native)
        hauthSolc (by jump_dest) (by simp)
      let memAuth := twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem
      have hmemAuth : memAuth.size = 96 := by
        dsimp [memAuth]
        exact twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      let sinSlot := suckSinSlot I
      have hsinWord : vatSlotWord sinSlot σ_evm I = vatSlotWord sinSlot σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner sinSlot ⟨0⟩
      by_cases hsinOverflow :
          UInt256.size ≤ (vatSlotWord sinSlot σ_evm I).toNat + (suckRadWord I).toNat
      · have hsinOverflowSolm :
            UInt256.size ≤ (vatSlotWord sinSlot σ_solm I).toNat + (suckRadWord I).toNat := by
          rwa [← hsinWord]
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (suckStore I) suckTransition.body .reverted :=
          vatSuckSourceRevertSinOverflow
            (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv
            (by simpa [callerSlot] using hauthSolm)
            (by simpa [sinSlot] using hsinOverflowSolm)
        have hrev := RD.vatSuckSinAddOverflow
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := vatSelWord I)
          (memAuth := memAuth)
          (by simpa [memAuth] using hafterAuth) hmemAuth
          (by simpa [sinSlot] using hsinOverflow)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hsinFit :
            (vatSlotWord sinSlot σ_evm I).toNat + (suckRadWord I).toNat < UInt256.size :=
          Nat.lt_of_not_ge hsinOverflow
        let sinNew := vatSlotWord sinSlot σ_evm I + suckRadWord I
        obtain ⟨_, _, _hsinOk⟩ := RD.vatSuckSinAddSuccess
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := vatSelWord I)
          (memAuth := memAuth)
          (by simpa [memAuth] using hafterAuth) hmemAuth
          (by simpa [sinSlot] using hsinFit)
        let memSin := twoWordHashMem (suckUMaskedWord I) ⟨6⟩ memAuth
        have hmemSin : memSin.size = 96 := by
          dsimp [memSin]
          exact twoWordHashMem_size_96 (suckUMaskedWord I) ⟨6⟩ hmemAuth
        obtain ⟨_, _, _hafterSinStore⟩ := RD.vatSuckSinStore
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := vatSelWord I) (sinNew := sinNew)
          (mem := memSin)
          (by simpa [sinNew, sinSlot, memSin] using _hsinOk)
          hmemSin hperm
        let σSinEvm := sstoreAccountMap I.codeOwner σ_evm (suckSinSlot I) sinNew
        let σSinSolm := sstoreAccountMap I.codeOwner σ_solm (suckSinSlot I) sinNew
        have hAccountsSin : accountMapEquiv σSinEvm σSinSolm := by
          exact accountMapEquiv_sstoreAccountMap I.codeOwner (suckSinSlot I) sinNew
            hAccounts
        have hdaiWord :
            vatSlotWord (suckDaiSlot I) σSinEvm I =
              vatSlotWord (suckDaiSlot I) σSinSolm I :=
          accountMapEquiv_storage_findD hAccountsSin I.codeOwner (suckDaiSlot I) ⟨0⟩
        let memAfterSin := twoWordHashMem (suckUMaskedWord I) ⟨6⟩ memSin
        have hmemAfterSin : memAfterSin.size = 96 := by
          dsimp [memAfterSin]
          exact twoWordHashMem_size_96 (suckUMaskedWord I) ⟨6⟩ hmemSin
        by_cases hdaiOverflow :
            UInt256.size ≤
              (vatSlotWord (suckDaiSlot I) σSinEvm I).toNat + (suckRadWord I).toNat
        ·
          have hsinFitSolmVat :
              (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
                (suckRadWord I).toNat < UInt256.size := by
            have htmp := hsinFit
            rwa [hsinWord] at htmp
          have hdaiOverflowSolmVat :
              UInt256.size ≤
                (vatSlotWord (suckDaiSlot I) σSinSolm I).toNat + (suckRadWord I).toNat := by
            rwa [← hdaiWord]
          have hsinNewSolmEq :
              vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I = sinNew := by
            rw [← hsinWord]
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (suckStore I) suckTransition.body .reverted :=
            vatSuckSourceRevertDaiOverflowVat
              (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv
              (by simpa [callerSlot] using hauthSolm)
              hsinFitSolmVat
              (by simpa [σSinSolm, hsinNewSolmEq] using hdaiOverflowSolmVat)
          have hrev := RD.vatSuckDaiAddOverflow
            (cA := cA) (gh := gh) (bl := bl) (σ := σSinEvm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (sel := vatSelWord I)
            (mem := memAfterSin)
            (by simpa [σSinEvm, memAfterSin] using _hafterSinStore)
            hmemAfterSin
            (by simpa [σSinEvm] using hdaiOverflow)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdaiFit :
              (vatSlotWord (suckDaiSlot I) σSinEvm I).toNat +
                (suckRadWord I).toNat < UInt256.size :=
            Nat.lt_of_not_ge hdaiOverflow
          let daiNew := vatSlotWord (suckDaiSlot I) σSinEvm I + suckRadWord I
          obtain ⟨_, _, _hdaiOk⟩ := RD.vatSuckDaiAddSuccess
            (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm) (σ := σSinEvm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := vatSelWord I)
            (mem := memAfterSin)
            (by simpa [σSinEvm, memAfterSin] using _hafterSinStore)
            hmemAfterSin
            (by simpa [σSinEvm] using hdaiFit)
          let memDai := twoWordHashMem (suckVMaskedWord I) ⟨5⟩ memAfterSin
          have hmemDai : memDai.size = 96 := by
            dsimp [memDai]
            exact twoWordHashMem_size_96 (suckVMaskedWord I) ⟨5⟩ hmemAfterSin
          obtain ⟨kDaiStore, CDaiStore, hafterDaiStore⟩ := RD.vatSuckDaiStore
            (cA := cA) (gh := gh) (bl := bl) (σi := σ_evm) (σ := σSinEvm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := vatSelWord I)
            (daiNew := daiNew) (mem := memDai)
            (by simpa [daiNew, σSinEvm, memDai] using _hdaiOk)
            hmemDai hperm
          have hsinWordVat :
              vatSlotWord (suckSinSlot I) σ_evm I =
                vatSlotWord (suckSinSlot I) σ_solm I := by
            simpa only [sinSlot] using hsinWord
          have hsinFitSolmVat :
              (vatSlotWord (suckSinSlot I) σ_solm I).toNat +
                (suckRadWord I).toNat < UInt256.size := by
            simpa only [sinSlot, hsinWordVat] using hsinFit
          have hsinNewSolm :
              vatSlotWord (suckSinSlot I) σ_solm I + suckRadWord I = sinNew := by
            dsimp [sinNew]
            rw [← hsinWordVat]
          have hdaiFitSolmVat :
              (vatSlotWord (suckDaiSlot I) σSinSolm I).toNat +
                (suckRadWord I).toNat < UInt256.size := by
            simpa only [hdaiWord] using hdaiFit
          have hdaiNewSolm :
              vatSlotWord (suckDaiSlot I) σSinSolm I + suckRadWord I = daiNew := by
            dsimp [daiNew]
            rw [← hdaiWord]
          have hAccountsDai :
              accountMapEquiv
                (sstoreAccountMap I.codeOwner σSinEvm (suckDaiSlot I) daiNew)
                (sstoreAccountMap I.codeOwner σSinSolm (suckDaiSlot I) daiNew) := by
            exact accountMapEquiv_sstoreAccountMap I.codeOwner (suckDaiSlot I) daiNew
              hAccountsSin
          exact @vatSuckAfterDaiStoreLocal
            cA gh bl σ_evm σ_solm σ₀ σSinEvm σSinSolm A I
            g (vatSelWord I) sinNew daiNew
            (twoWordHashMem (suckVMaskedWord I) ⟨5⟩ memDai) kDaiStore CDaiStore
            hcode hperm hwv hdispatch hdecode
            (by simpa only [callerSlot] using hauthSolm)
            (by rfl) (by rfl) hsinFitSolmVat hsinNewSolm
            hdaiFitSolmVat hdaiNewSolm hAccountsDai hafterDaiStore
    · have hauthSolm : vatSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody config contract evm0 (suckStore I) suckTransition.body .reverted := by
        have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := suckStore I)
          (by simp [suckStore]) (by simpa [callerSlot] using hauthSolm)
        have hblock := nonpayableSecondRequireReverts
          (cfg := config) (solm := { contract := contract, locals := suckStore I })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest :=
            checkedAddUintInto "sinNew" (.storage (sinRef (.var "u"))) (.var "rad") ++
            [ .assign .storage (sinRef (.var "u")) (.var "sinNew") ] ++
            checkedAddUintInto "daiNew" (.storage (daiRef (.var "v"))) (.var "rad") ++
            [ .assign .storage (daiRef (.var "v")) (.var "daiNew") ] ++
            checkedAddUintInto "viceNew" (.storage viceRef) (.var "rad") ++
            [ .assign .storage viceRef (.var "viceNew") ] ++
            checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad") ++
            [ .assign .storage debtRef (.var "debtNew") ])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, suckTransition, nonpayable, auth, evm0, List.append_assoc]
          using ExecFuncBody.execBlockRevert hblock
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
      have hrev := RD.vatAuthCheckRevert
        (pc := ⟨6190⟩) (okPc := ⟨6272⟩) (key := suckRadWord I)
        (ret := suckVMaskedWord I) (R := [suckUMaskedWord I, ⟨524⟩, vatSelWord I])
        (by simpa using hdecoded)
        (by
          unfold vatAuthCheckWf
          repeat' first | apply And.intro | decide +native)
        (by
          unfold vatAuthRevertTailWf vatAuthTailPc
          repeat' first | apply And.intro | decide +native)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact vatSuckBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hsel hreach

end Benchmarks.Dss.Vat

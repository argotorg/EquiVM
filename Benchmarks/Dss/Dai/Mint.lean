import Benchmarks.Dss.Dai.Rely
import Benchmarks.Dss.Dai.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `mint(address,uint256)` -/

abbrev mintUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev mintUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (mintUsrWord I)

abbrev mintWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev mintSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev mintUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (mintUsrWord I).toNat)

abbrev mintWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (mintWadWord I).toNat)

abbrev mintUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (mintUsrWord I).toNat)

abbrev mintAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev mintStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "usr" (mintUsrValue I)).insert "wad" (mintWadValue I)

def mintUsrStorageSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (mintUsrKey I)

def mintAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (mintAuthKey I)

abbrev mintTotalSupplySlot : UInt256 :=
  ⟨1⟩

def mintAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (mintAuthStorageSlot I) ⟨0⟩)

def mintUsrBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintUsrStorageSlot I)

def mintTotalSupplyWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner mintTotalSupplySlot

def mintUsrCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (mintUsrBalanceWord evm I).toNat + (mintWadWord I).toNat

def mintUsrCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (mintUsrCreditNat evm I)

abbrev mintUsrCreditValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (mintUsrCreditNat evm I))

def mintAfterUsrCreditState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (mintUsrStorageSlot I)
    (mintUsrCreditWord evm I)

def mintSupplyCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (mintTotalSupplyWord evm).toNat + (mintWadWord I).toNat

def mintSupplyCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (mintSupplyCreditNat evm I)

abbrev mintSupplyCreditValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (mintSupplyCreditNat evm I))

def mintPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (mintAfterUsrCreditState evm I)
    (mintAfterUsrCreditState evm I).executionEnv.codeOwner mintTotalSupplySlot
    (mintSupplyCreditWord (mintAfterUsrCreditState evm I) I)

abbrev mintUsrBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (mintUsrKey I)] }

abbrev mintAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (mintAuthKey I)] }

abbrev mintTotalSupplyEvaledRef : EvaledStorageRef :=
  { base := "totalSupply", steps := [] }

theorem mintStore_get_usr (I : ExecutionEnv) :
    (mintStore I).get? "usr" = some (mintUsrValue I) := by
  unfold mintStore
  rw [store_get_ne
    (L := (∅ : Store).insert "usr" (mintUsrValue I))
    (k := "wad") (a := "usr") (mintWadValue I) (by native_decide)]
  simp

theorem mintStore_get_wad (I : ExecutionEnv) :
    (mintStore I).get? "wad" = some (mintWadValue I) := by
  unfold mintStore
  simp

theorem mintStore_balanceOf (I : ExecutionEnv) :
    (mintStore I).get? "balanceOf" = none := by
  unfold mintStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem mintStore_wards (I : ExecutionEnv) :
    (mintStore I).get? "wards" = none := by
  unfold mintStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem mintStore_totalSupply (I : ExecutionEnv) :
    (mintStore I).get? "totalSupply" = none := by
  unfold mintStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem mintStore_index_usr (I : ExecutionEnv) :
    (mintStore I)["usr"] = mintUsrValue I := by
  unfold mintStore
  simp [Std.HashMap.getElem_insert]

theorem mintUsrStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    mintUsrStorageSlot I = mapSlot (mintUsrMaskedWord I) ⟨2⟩ := by
  unfold mintUsrStorageSlot balanceOfSlot mintUsrKey mintUsrMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem mintAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    mintAuthStorageSlot I = mapSlot (mintSourceWord I) ⟨0⟩ := by
  unfold mintAuthStorageSlot wardsSlot mintAuthKey mintSourceWord
  rw [keyValueToWord_address]

theorem daiDecode_mint_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = some (mintStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = _
  simpa [mintStore, mintUsrValue, mintWadValue, mintUsrWord, mintWadWord, calldataWord]
    using decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "usr") (y := "wad") hsz68

theorem daiDecode_mint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "usr") (y := "wad") hsz4 hshort

theorem evalExpr_mint_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.var "wad") = .ok (mintWadValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintStore_get_wad]

theorem evalStorageRef_mint_usr_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := mintStore I } evm
      (balanceOfRef (.var "usr")) = .ok (mintUsrBalanceRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, mintUsrBalanceRef,
    mintUsrValue, mintUsrKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr?, mintStore_index_usr]

theorem evalStorageRef_mint_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := mintStore I } evm
      (wardsRef sender) = .ok (mintAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, mintAuthEvaledRef,
    mintAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalStorageRef_mint_totalSupply (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := mintStore I } evm
      totalSupplyRef = .ok mintTotalSupplyEvaledRef := by
  simp [evalStorageRef, totalSupplyRef, EvalResult.bind, bind, pure]

theorem evalExpr_mint_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := mintStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := mintStore I })
      (slot := wardsRef sender)
      (er := mintAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (mintAuthStorageSlot I) (.int uint256Int))
      (value := .int 1)
      (hbase := by
        simp [mintStore, wardsRef])
      (her := evalStorageRef_mint_auth evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, mintAuthKey, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [wordLoc, uint256Loc, uint256Int, hload] using
          storageLocLoad_uint256 evm (mintAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_mint_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := mintStore I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (mintAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := mintStore I })
      (slot := wardsRef sender)
      (er := mintAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (mintAuthStorageSlot I) (.int uint256Int))
      (hbase := by
        simp [mintStore, wardsRef])
      (her := evalStorageRef_mint_auth evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, mintAuthKey, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [wordLoc, uint256Loc, uint256Int] using
          storageLocLoad_uint256 evm (mintAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (mintAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (mintAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_mint_usr_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.storage (balanceOfRef (.var "usr"))) =
        .ok (.int (Int.ofNat (mintUsrBalanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := mintStore I })
    (slot := balanceOfRef (.var "usr"))
    (er := mintUsrBalanceRef I)
    (t := .int uint256Int)
    (loc := wordLoc (mintUsrStorageSlot I) (.int uint256Int))
    (value := .int (Int.ofNat (mintUsrBalanceWord evm I).toNat))
    (hbase := by
      simpa [balanceOfRef] using mintStore_balanceOf I)
    (her := evalStorageRef_mint_usr_balance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, mintUsrKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, mintUsrBalanceWord] using
        storageLocLoad_uint256 evm (mintUsrStorageSlot I))]

theorem evalExpr_mint_totalSupply (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat (mintTotalSupplyWord evm).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := mintStore I })
    (slot := totalSupplyRef)
    (er := mintTotalSupplyEvaledRef)
    (t := .int uint256Int)
    (loc := wordLoc mintTotalSupplySlot (.int uint256Int))
    (value := .int (Int.ofNat (mintTotalSupplyWord evm).toNat))
    (hbase := by
      simpa [totalSupplyRef] using mintStore_totalSupply I)
    (her := evalStorageRef_mint_totalSupply evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, mintTotalSupplyWord, mintTotalSupplySlot] using
        storageLocLoad_uint256 evm mintTotalSupplySlot)]

theorem evalExpr_mint_usr_add_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .add (.storage (balanceOfRef (.var "usr"))) (.var "wad")) =
        .ok (.int (Int.ofNat (mintUsrBalanceWord evm I).toNat +
          Int.ofNat (mintWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_mint_usr_balance, evalExpr_mint_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, mintWadValue]

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_usr_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintUsrCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (add256 (.storage (balanceOfRef (.var "usr"))) (.var "wad")) =
        .ok (mintUsrCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (mintUsrCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_mint_usr_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, mintUsrCreditValue, mintUsrCreditNat,
    mintWadValue, uint256Int, hlt]
  constructor
  · omega
  · have hfitNat :
        (mintUsrBalanceWord evm I).toNat + (mintWadWord I).toNat < 2 ^ 256 := by
      simpa [mintUsrCreditNat, UInt256.size] using hfit
    omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_usr_checkedAdd_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintUsrCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .ge (add256 (.storage (balanceOfRef (.var "usr"))) (.var "wad"))
        (.storage (balanceOfRef (.var "usr")))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_mint_usr_credit evm I hfit, evalExpr_mint_usr_balance]
  simp [EvalResult.bind, bind, evalBinaryOp?, mintUsrCreditValue, mintUsrCreditNat]

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_usr_credit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ mintUsrCreditNat evm I) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (add256 (.storage (balanceOfRef (.var "usr"))) (.var "wad")) = .revert := by
  have hge : (2 : Int) ^ 256 ≤ Int.ofNat (mintUsrCreditNat evm I) := by
    exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)
  have hnotNeg : ¬ Int.ofNat (mintUsrCreditNat evm I) < 0 := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_mint_usr_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, mintUsrCreditNat, mintWadValue,
    uint256Int, hnotNeg, hge]
  intro _
  simpa [mintUsrCreditNat] using hge

theorem evalExpr_mint_usr_checkedAdd_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ mintUsrCreditNat evm I) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .ge (add256 (.storage (balanceOfRef (.var "usr"))) (.var "wad"))
        (.storage (balanceOfRef (.var "usr")))) = .revert := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_mint_usr_credit_revert evm I hover]
  simp [EvalResult.bind, bind]

theorem evalExpr_mint_supply_add_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .add (.storage totalSupplyRef) (.var "wad")) =
        .ok (.int (Int.ofNat (mintTotalSupplyWord evm).toNat +
          Int.ofNat (mintWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_mint_totalSupply, evalExpr_mint_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, mintWadValue]

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_supply_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintSupplyCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (add256 (.storage totalSupplyRef) (.var "wad")) =
        .ok (mintSupplyCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (mintSupplyCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_mint_supply_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, mintSupplyCreditValue,
    mintSupplyCreditNat, mintWadValue, uint256Int, hlt]
  constructor
  · omega
  · have hfitNat :
        (mintTotalSupplyWord evm).toNat + (mintWadWord I).toNat < 2 ^ 256 := by
      simpa [mintSupplyCreditNat, UInt256.size] using hfit
    omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_supply_checkedAdd_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintSupplyCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .ge (add256 (.storage totalSupplyRef) (.var "wad"))
        (.storage totalSupplyRef)) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_mint_supply_credit evm I hfit, evalExpr_mint_totalSupply]
  simp [EvalResult.bind, bind, evalBinaryOp?, mintSupplyCreditValue, mintSupplyCreditNat]

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_supply_credit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ mintSupplyCreditNat evm I) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (add256 (.storage totalSupplyRef) (.var "wad")) = .revert := by
  have hge : (2 : Int) ^ 256 ≤ Int.ofNat (mintSupplyCreditNat evm I) := by
    exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)
  have hnotNeg : ¬ Int.ofNat (mintSupplyCreditNat evm I) < 0 := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_mint_supply_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, mintSupplyCreditNat, mintWadValue,
    uint256Int, hnotNeg, hge]
  intro _
  simpa [mintSupplyCreditNat] using hge

theorem evalExpr_mint_supply_checkedAdd_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ mintSupplyCreditNat evm I) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .ge (add256 (.storage totalSupplyRef) (.var "wad"))
        (.storage totalSupplyRef)) = .revert := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_mint_supply_credit_revert evm I hover]
  simp [EvalResult.bind, bind]

theorem mintAssignUsr (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintUsrCreditNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := mintStore I } evm
      .storage (balanceOfRef (.var "usr")) (mintUsrCreditValue evm I) =
        .ok ({ contract := contract, locals := mintStore I },
          mintAfterUsrCreditState evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := balanceOfRef (.var "usr"))
      (er := mintUsrBalanceRef I)
      (ty := uint256St)
      (loc := wordLoc (mintUsrStorageSlot I) (.int uint256Int))
      (hbase := by
        simpa [balanceOfRef] using mintStore_balanceOf I)
      (her := evalStorageRef_mint_usr_balance evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, mintUsrKey, uint256St])
      (hloc := by rfl)
  have htoNat : (mintUsrCreditWord evm I).toNat = mintUsrCreditNat evm I := by
    unfold mintUsrCreditWord
    exact ulit_toNat' _ hfit
  rw [← htoNat]
  rw [show wordLoc (mintUsrStorageSlot I) (ElemType.int uint256Int) =
    uint256Loc (mintUsrStorageSlot I) by rfl]
  rw [storageLocStore_uint256]
  rfl

theorem mintAssignSupply (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintSupplyCreditNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := mintStore I } evm
      .storage totalSupplyRef (mintSupplyCreditValue evm I) =
        .ok ({ contract := contract, locals := mintStore I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner mintTotalSupplySlot
            (mintSupplyCreditWord evm I)) := by
  apply assignStorageRef_storage_scalar
      (slot := totalSupplyRef)
      (er := mintTotalSupplyEvaledRef)
      (ty := uint256St)
      (loc := wordLoc mintTotalSupplySlot (.int uint256Int))
      (hbase := by
        simpa [totalSupplyRef] using mintStore_totalSupply I)
      (her := evalStorageRef_mint_totalSupply evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  have htoNat : (mintSupplyCreditWord evm I).toNat = mintSupplyCreditNat evm I := by
    unfold mintSupplyCreditWord
    exact ulit_toNat' _ hfit
  rw [← htoNat]
  rw [show wordLoc mintTotalSupplySlot (ElemType.int uint256Int) =
    uint256Loc mintTotalSupplySlot by rfl]
  rw [storageLocStore_uint256]

set_option maxHeartbeats 1000000 in
theorem daiMintBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintAuthStorageSlot I) = ⟨1⟩)
    (hfitUsr : mintUsrCreditNat evm I < UInt256.size)
    (hfitSupply : mintSupplyCreditNat (mintAfterUsrCreditState evm I) I < UInt256.size) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body
      (.returned { contract := contract, locals := mintStore I }
        (mintPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simp only [mintTransition, nonpayable, auth, creditBalance, checkedAdd, List.append_assoc,
    List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_mint_auth_true evm I hsrc hauth)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_mint_usr_checkedAdd_true evm I hfitUsr)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_mint_usr_credit evm I hfitUsr)
      (mintAssignUsr evm I hfitUsr)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_mint_supply_checkedAdd_true (mintAfterUsrCreditState evm I) I
        hfitSupply)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_mint_supply_credit (mintAfterUsrCreditState evm I) I hfitSupply)
      (by simpa [mintPostState] using
        mintAssignSupply (mintAfterUsrCreditState evm I) I hfitSupply)) ?_
  exact ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem daiMintBodyReverts_auth (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [mintTransition, nonpayable, auth, creditBalance, checkedAdd, List.append_assoc,
    List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_mint_auth_false evm I hsrc hauth))

set_option maxHeartbeats 1000000 in
theorem daiMintBodyReverts_usrOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintAuthStorageSlot I) = ⟨1⟩)
    (hover : UInt256.size ≤ mintUsrCreditNat evm I) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [mintTransition, nonpayable, auth, creditBalance, checkedAdd, List.append_assoc,
    List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_mint_auth_true evm I hsrc hauth)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert (evalExpr_mint_usr_checkedAdd_revert evm I hover))

set_option maxHeartbeats 1000000 in
theorem daiMintBodyReverts_supplyOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mintAuthStorageSlot I) = ⟨1⟩)
    (hfitUsr : mintUsrCreditNat evm I < UInt256.size)
    (hover : UInt256.size ≤ mintSupplyCreditNat (mintAfterUsrCreditState evm I) I) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [mintTransition, nonpayable, auth, creditBalance, checkedAdd, List.append_assoc,
    List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_mint_auth_true evm I hsrc hauth)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_mint_usr_checkedAdd_true evm I hfitUsr)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_mint_usr_credit evm I hfitUsr)
      (mintAssignUsr evm I hfitUsr)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_mint_supply_checkedAdd_revert (mintAfterUsrCreditState evm I) I hover))

/-! ## EVM trace -/

noncomputable abbrev mintAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintSourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev mintUsrHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintUsrMaskedWord I) ⟨2⟩ (mintAuthHashMem I)

noncomputable abbrev mintUsrStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintUsrMaskedWord I) ⟨2⟩ (mintUsrHashMem I)

noncomputable abbrev mintLogMem (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (mintUsrHashMem I) (mintWadWord I)

noncomputable abbrev mintStoreLogMem (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (mintUsrStoreHashMem I) (mintWadWord I)

abbrev mintEvmAuthSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (mintSourceWord I) ⟨0⟩

abbrev mintEvmUsrSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (mintUsrMaskedWord I) ⟨2⟩

abbrev mintEvmUsrBalanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (mintEvmUsrSlot I)

abbrev mintEvmUsrCreditWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  mintEvmUsrBalanceWord σ I + mintWadWord I

abbrev mintEvmAfterUsrAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (mintEvmUsrSlot I) (mintEvmUsrCreditWord σ I)

abbrev mintEvmTotalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord (mintEvmAfterUsrAccountMap σ I) I mintTotalSupplySlot

abbrev mintEvmSupplyCreditWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  mintEvmTotalSupplyWord σ I + mintWadWord I

abbrev mintEvmPostAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (mintEvmAfterUsrAccountMap σ I) mintTotalSupplySlot
    (mintEvmSupplyCreditWord σ I)

theorem mintUsrMaskedWord_canonical (I : ExecutionEnv) :
    (mintUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold mintUsrMaskedWord
  rw [u256_land_comm solcAddrMask (mintUsrWord I)]
  exact solcAddrMask_result_canonical (mintUsrWord I)

theorem mintAuthHashMem_size (I : ExecutionEnv) :
    (mintAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (mintSourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem mintAuthHashMem_read64 (I : ExecutionEnv) :
    (mintAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (mintSourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem mintUsrHashMem_size (I : ExecutionEnv) :
    (mintUsrHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (mintUsrMaskedWord I) ⟨2⟩ (mintAuthHashMem_size I)

theorem mintUsrHashMem_read64 (I : ExecutionEnv) :
    (mintUsrHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (mintUsrMaskedWord I) ⟨2⟩ (mintAuthHashMem_size I)
    (mintAuthHashMem_read64 I)

theorem mintUsrStoreHashMem_size (I : ExecutionEnv) :
    (mintUsrStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (mintUsrMaskedWord I) ⟨2⟩ (mintUsrHashMem_size I)

theorem mintUsrStoreHashMem_read64 (I : ExecutionEnv) :
    (mintUsrStoreHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (mintUsrMaskedWord I) ⟨2⟩ (mintUsrHashMem_size I)
    (mintUsrHashMem_read64 I)

theorem mintLogMem_size (I : ExecutionEnv) :
    (mintLogMem I).size = 160 := by
  exact solcScratchReturnMem_size (mintWadWord I) (mintUsrHashMem_size I)

theorem mintLogMem_read64 (I : ExecutionEnv) :
    (mintLogMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact solcScratchReturnMem_read64 (mintWadWord I) (mintUsrHashMem_size I)
    (mintUsrHashMem_read64 I)

theorem mintLogMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (mintLogMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((mintLogMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 (mintWadWord I) (mintUsrHashMem_size I)
    (mintUsrHashMem_read64 I)

theorem mintStoreLogMem_size (I : ExecutionEnv) :
    (mintStoreLogMem I).size = 160 := by
  exact solcScratchReturnMem_size (mintWadWord I) (mintUsrStoreHashMem_size I)

theorem mintStoreLogMem_read64 (I : ExecutionEnv) :
    (mintStoreLogMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact solcScratchReturnMem_read64 (mintWadWord I) (mintUsrStoreHashMem_size I)
    (mintUsrStoreHashMem_read64 I)

theorem mintStoreLogMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (mintStoreLogMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((mintStoreLogMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 (mintWadWord I) (mintUsrStoreHashMem_size I)
    (mintUsrStoreHashMem_read64 I)

theorem daiMintX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨642⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2011⟩
        [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd664⟩ := RD.daiAddressUint256ExternalLenOk
    (entry := ⟨642⟩) (ret := ⟨686⟩) (routine := ⟨2011⟩) hreach
    dai_address_uint256_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd2011⟩ := RD.daiAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨642⟩) (ret := ⟨686⟩) (routine := ⟨2011⟩) (R := [sel])
    rd664 dai_address_uint256_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [mintWadWord, mintUsrMaskedWord, mintUsrWord, calldataWord] using rd2011⟩

theorem daiMintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨642⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiAddressUint256ExternalShort
    (entry := ⟨642⟩) (ret := ⟨686⟩) (routine := ⟨2011⟩)
    hreach dai_address_uint256_external_entry_wf hsz4 hsize hshort

set_option maxHeartbeats 1000000 in
theorem daiMintX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : mintAuthWord σ I = ⟨1⟩)
    (h : RD daiBytecode I g s0 ⟨2011⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨2100⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((mintAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (mintSourceWord I) ⟨0⟩ := by
    simpa [mintAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (mintSourceWord I)
        solcFreePtrMem_size
  have rd2017pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2018 := rd2017pre.mstore 0 (wordAt0Mem (mintSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2022pre := evm_run rd2018 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2023 := rd2022pre.mstore 0 (mintAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2026pre := evm_run rd2023 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2027 := rd2026pre.keccak256 0 (mapSlot (mintSourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2028, C2028, rd2028raw⟩ := rd2027.sload (by native_decide) (by evm_ov)
  have rd2028 : RD daiBytecode I g s0 ⟨2028⟩
      (mintAuthWord σ I :: mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
      (mintAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2028 C2028 := by
    simpa [mintAuthWord, mintAuthStorageSlot_eq_mapSlot_source I] using rd2028raw
  have rd2031pre := evm_run rd2028 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd2031pre
  have rd2034 := rd2031pre.pushConst (⟨2100⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2034.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiMintX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : mintAuthWord σ I ≠ ⟨1⟩)
    (h : RD daiBytecode I g s0 ⟨2011⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((mintAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (mintSourceWord I) ⟨0⟩ := by
    simpa [mintAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (mintSourceWord I)
        solcFreePtrMem_size
  have rd2017pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2018 := rd2017pre.mstore 0 (wordAt0Mem (mintSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2022pre := evm_run rd2018 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2023 := rd2022pre.mstore 0 (mintAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2026pre := evm_run rd2023 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2027 := rd2026pre.keccak256 0 (mapSlot (mintSourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2028, C2028, rd2028raw⟩ := rd2027.sload (by native_decide) (by evm_ov)
  have rd2028 : RD daiBytecode I g s0 ⟨2028⟩
      (mintAuthWord σ I :: mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
      (mintAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2028 C2028 := by
    simpa [mintAuthWord, mintAuthStorageSlot_eq_mapSlot_source I] using rd2028raw
  have rd2031pre := evm_run rd2028 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (mintAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd2031pre
  have rd2034 := rd2031pre.pushConst (⟨2100⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd2035 := rd2034.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2035⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x11185a4bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4461692f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd2035
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (mintAuthHashMem_size I)
    (mintAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiMintX_logAndJump {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hSlen : S.length + 10 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (h : RD daiBytecode I g s0 ⟨2177⟩
      (mintWadWord I :: mintUsrMaskedWord I :: ret :: S)
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret S
      (mintStoreLogMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
  have husrMask :
      UInt256.land (mintUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        mintUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (mintUsrMaskedWord_canonical I)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (mintUsrStoreHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((mintUsrStoreHashMem I).readWithPadding
           (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [mintUsrStoreHashMem_size I]; decide) (by decide)
      (mintUsrStoreHashMem_read64 I)
  have rd2180 := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd2183pre := evm_run rd2180 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2184 := rd2183pre.mstore 6 (mintStoreLogMem I) (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2196pre := evm_run rd2184 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (mintStoreLogMem_mload64 I) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMask] at rd2196pre
  have rd2200 := evm_run rd2196pre with [
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2233 := rd2200.pushConst transferFromTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd2241pre := evm_run rd2233 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2242 := rd2241pre.log3 0 (UInt256.ofNat 5) (by native_decide) hperm
    mem_cost (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRet := evm_run rd2242 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) hretDest (by evm_ov)]
  exact ⟨_, _, rdRet⟩

set_option maxHeartbeats 2000000 in
theorem daiMintX_usrAddReady {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD daiBytecode I g s0 ⟨2100⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3982⟩
      (mintWadWord I :: mintEvmUsrBalanceWord σ I :: ⟨2135⟩ ::
        mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
      (mintUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have husrMaskLiteral :
      UInt256.land (mintUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        mintUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (mintUsrMaskedWord_canonical I)
  have hUsrSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((mintUsrHashMem I).readWithPadding 0 64))) =
        mintEvmUsrSlot I := by
    simpa [mintUsrHashMem, mintEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (mintUsrMaskedWord I)
        (mintAuthHashMem_size I)
  have rd2111 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rd2111
  have rd2115pre := evm_run rd2111 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2116 := rd2115pre.mstore 0
    (wordAt0Mem (mintUsrMaskedWord I) (mintAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2120pre := evm_run rd2116 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2121 := rd2120pre.mstore 0 (mintUsrHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2124pre := evm_run rd2121 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2125 := rd2124pre.keccak256 0 (mintEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hUsrSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2126, C2126, rd2126raw⟩ := rd2125.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2126 : RD daiBytecode I g s0 ⟨2126⟩
      (mintEvmUsrBalanceWord σ I :: mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
      (mintUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2126 C2126 := by
    simpa [mintEvmUsrBalanceWord, mintEvmUsrSlot] using rd2126raw
  have rd2134pre := evm_run rd2126 with [
    raw push2 ⟨2135⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3982⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd2134pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiCheckedAddRevert0 {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3982⟩ (b :: a :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have haddWf : solcCheckedAddSuccessWf daiBytecode ⟨3982⟩ ⟨1399⟩ := by
    unfold solcCheckedAddSuccessWf
    repeat' first | apply And.intro | native_decide
  rcases haddWf with
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
  have rd7 := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  rw [hlt] at rd7
  have rd8 := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 ⟨1399⟩ hd8 (by evm_ov)]
  have rdTail := rdPush.jumpiNT hd11 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdTail
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 4000000 in
theorem daiMintX_storeUsr_success {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hfitUsr :
      (mintEvmUsrBalanceWord σ I).toNat + (mintWadWord I).toNat < UInt256.size)
    (h : RD daiBytecode I g s0 ⟨2100⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨2161⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmAfterUsrAccountMap σ I) k' C' := by
  have husrMaskLiteral :
      UInt256.land (mintUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        mintUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (mintUsrMaskedWord_canonical I)
  obtain ⟨_, _, rdAddUsr⟩ := daiMintX_usrAddReady (I := I) (sel := sel) h
  have haddWf : solcCheckedAddSuccessWf daiBytecode ⟨3982⟩ ⟨1399⟩ := by
    unfold solcCheckedAddSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨k2135, C2135, rd2135raw⟩ := RD.solcCheckedAddSuccess
    (pc := ⟨3982⟩) (okPc := ⟨1399⟩)
    (a := mintEvmUsrBalanceWord σ I) (b := mintWadWord I)
    (ret := ⟨2135⟩)
    (R := mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
    rdAddUsr haddWf hfitUsr (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2135 : RD daiBytecode I g s0 ⟨2135⟩
      [mintEvmUsrCreditWord σ I, mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2135 C2135 := by
    simpa [mintEvmUsrCreditWord] using rd2135raw
  have rd2146 := evm_run rd2135 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rd2146
  have rd2150pre := evm_run rd2146 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2151 := rd2150pre.mstore 0
    (wordAt0Mem (mintUsrMaskedWord I) (mintUsrHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2155pre := evm_run rd2151 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2156 := rd2155pre.mstore 0 (mintUsrStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hUsrStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((mintUsrStoreHashMem I).readWithPadding 0 64))) =
        mintEvmUsrSlot I := by
    simpa [mintUsrStoreHashMem, mintEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (mintUsrMaskedWord I)
        (mintUsrHashMem_size I)
  have rd2159pre := evm_run rd2156 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2160 := rd2159pre.keccak256 0 (mintEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hUsrStoreSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2161, C2161, rd2161raw⟩ := rd2160.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2161 : RD daiBytecode I g s0 ⟨2161⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmAfterUsrAccountMap σ I) k2161 C2161 := by
    simpa [mintEvmAfterUsrAccountMap, mintEvmUsrCreditWord, mintEvmUsrSlot] using rd2161raw
  exact ⟨k2161, C2161, rd2161⟩

theorem daiMintX_usrOverflowRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hover :
      UInt256.size ≤ (mintEvmUsrBalanceWord σ I).toNat + (mintWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨2100⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rdAddUsr⟩ := daiMintX_usrAddReady (I := I) (sel := sel) h
  exact daiCheckedAddRevert0
    (a := mintEvmUsrBalanceWord σ I) (b := mintWadWord I) (ret := ⟨2135⟩)
    (R := mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
    hover (by simp only [List.length_cons, List.length_nil]; omega) rdAddUsr

set_option maxHeartbeats 4000000 in
theorem daiMintX_storeSupply_success {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hfitSupply :
      (mintEvmTotalSupplyWord σ I).toNat + (mintWadWord I).toNat < UInt256.size)
    (h : RD daiBytecode I g s0 ⟨2161⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmAfterUsrAccountMap σ I) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨2177⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmPostAccountMap σ I) k' C' := by
  have haddWf : solcCheckedAddSuccessWf daiBytecode ⟨3982⟩ ⟨1399⟩ := by
    unfold solcCheckedAddSuccessWf
    repeat' first | apply And.intro | native_decide
  let rd2161 := h
  have rd2164pre := evm_run rd2161 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2164, C2164, rd2164raw⟩ := rd2164pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2164 : RD daiBytecode I g s0 ⟨2164⟩
      (mintEvmTotalSupplyWord σ I :: mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmAfterUsrAccountMap σ I) k2164 C2164 := by
    simpa [mintEvmTotalSupplyWord, mintTotalSupplySlot] using rd2164raw
  have rd2172pre := evm_run rd2164 with [
    raw push2 ⟨2173⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3982⟩ (by native_decide) (by evm_ov)]
  have rdAddSupply := rd2172pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k2173, C2173, rd2173raw⟩ := RD.solcCheckedAddSuccess
    (pc := ⟨3982⟩) (okPc := ⟨1399⟩)
    (a := mintEvmTotalSupplyWord σ I) (b := mintWadWord I)
    (ret := ⟨2173⟩)
    (R := mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
    rdAddSupply haddWf hfitSupply (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2173 : RD daiBytecode I g s0 ⟨2173⟩
      [mintEvmSupplyCreditWord σ I, mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmAfterUsrAccountMap σ I) k2173 C2173 := by
    simpa [mintEvmSupplyCreditWord] using rd2173raw
  have rd2176pre := evm_run rd2173 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2177, C2177, rd2177raw⟩ := rd2176pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2177 : RD daiBytecode I g s0 ⟨2177⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmPostAccountMap σ I) k2177 C2177 := by
    simpa [mintEvmPostAccountMap, mintEvmSupplyCreditWord, mintTotalSupplySlot] using rd2177raw
  exact ⟨k2177, C2177, rd2177⟩

theorem daiMintX_supplyOverflowRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hover :
      UInt256.size ≤ (mintEvmTotalSupplyWord σ I).toNat + (mintWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨2161⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmAfterUsrAccountMap σ I) k C) :
    RDrev daiBytecode g s0 := by
  have rd2164pre := evm_run h with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2164, C2164, rd2164raw⟩ := rd2164pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2164 : RD daiBytecode I g s0 ⟨2164⟩
      (mintEvmTotalSupplyWord σ I :: mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
      (mintUsrStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmAfterUsrAccountMap σ I) k2164 C2164 := by
    simpa [mintEvmTotalSupplyWord, mintTotalSupplySlot] using rd2164raw
  have rd2172pre := evm_run rd2164 with [
    raw push2 ⟨2173⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3982⟩ (by native_decide) (by evm_ov)]
  have rdAddSupply := rd2172pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact daiCheckedAddRevert0
    (a := mintEvmTotalSupplyWord σ I) (b := mintWadWord I) (ret := ⟨2173⟩)
    (R := mintWadWord I :: mintUsrMaskedWord I :: ⟨686⟩ :: [sel])
    hover (by simp only [List.length_cons, List.length_nil]; omega) rdAddSupply

set_option maxHeartbeats 1000000 in
theorem daiMintX_success {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hfitUsr :
      (mintEvmUsrBalanceWord σ I).toNat + (mintWadWord I).toNat < UInt256.size)
    (hfitSupply :
      (mintEvmTotalSupplyWord σ I).toNat + (mintWadWord I).toNat < UInt256.size)
    (h : RD daiBytecode I g s0 ⟨2100⟩
      [mintWadWord I, mintUsrMaskedWord I, ⟨686⟩, sel]
      (mintAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g s0 (cA, mintEvmPostAccountMap σ I) ByteArray.empty := by
  obtain ⟨k2161, C2161, rd2161⟩ :=
    daiMintX_storeUsr_success (I := I) (sel := sel) hperm hfitUsr h
  obtain ⟨_, _, rd2177⟩ :=
    daiMintX_storeSupply_success (I := I) (sel := sel) hperm hfitSupply rd2161
  obtain ⟨_, _, rd686⟩ := daiMintX_logAndJump
    (I := I) (ret := ⟨686⟩) (S := [sel]) hperm
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd2177
  have rd687 := rd686.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd687 (by native_decide) (by evm_ov)

theorem mintAfterUsrCredit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (mintAfterUsrCreditState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [mintAfterUsrCreditState, storageStore_executionEnv]

set_option maxHeartbeats 1000000 in
theorem mintSolmAfterUsrBridge {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hfitUsr :
      (mintEvmUsrBalanceWord σ I).toNat + (mintWadWord I).toNat < UInt256.size) :
    mintUsrCreditNat evm I < UInt256.size ∧
    accountMapEquiv (mintEvmAfterUsrAccountMap σ I)
      (mintAfterUsrCreditState evm I).accountMap ∧
    mintSupplyCreditNat (mintAfterUsrCreditState evm I) I =
      (mintEvmTotalSupplyWord σ I).toNat + (mintWadWord I).toNat := by
  have husrWord :
      mintEvmUsrBalanceWord σ I = mintUsrBalanceWord evm I := by
    have hread :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (mintEvmUsrSlot I)
        (⟨0⟩ : UInt256)
    simpa [mintEvmUsrBalanceWord, mintUsrBalanceWord, mintEvmUsrSlot,
      mintUsrStorageSlot_eq_mapSlot_masked, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWord, howner] using hread
  have hfitUsrSolm : mintUsrCreditNat evm I < UInt256.size := by
    unfold mintUsrCreditNat
    rw [← husrWord]
    exact hfitUsr
  have hcreditEq :
      mintEvmUsrCreditWord σ I = mintUsrCreditWord evm I := by
    apply u256_inj
    unfold mintEvmUsrCreditWord mintUsrCreditWord
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitUsr]
    rw [ulit_toNat' _ hfitUsrSolm]
    unfold mintUsrCreditNat
    rw [← husrWord]
  have hafterMap :
      accountMapEquiv (mintEvmAfterUsrAccountMap σ I)
        (mintAfterUsrCreditState evm I).accountMap := by
    simpa [mintEvmAfterUsrAccountMap, mintAfterUsrCreditState, storageStore_accountMap,
      mintEvmUsrSlot, mintUsrStorageSlot_eq_mapSlot_masked, howner, hcreditEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (mintEvmUsrSlot I)
        (mintEvmUsrCreditWord σ I) hAccounts
  have hsupplyWord :
      mintEvmTotalSupplyWord σ I =
        mintTotalSupplyWord (mintAfterUsrCreditState evm I) := by
    have hread :=
      accountMapEquiv_storage_findD hafterMap I.codeOwner mintTotalSupplySlot
        (⟨0⟩ : UInt256)
    have hownerAfter :
        (mintAfterUsrCreditState evm I).executionEnv.codeOwner = I.codeOwner := by
      simpa [mintAfterUsrCredit_codeOwner evm I] using howner
    simpa [mintEvmTotalSupplyWord, mintTotalSupplyWord, mintTotalSupplySlot,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord,
      hownerAfter] using hread
  have hsupplyNat :
      mintSupplyCreditNat (mintAfterUsrCreditState evm I) I =
        (mintEvmTotalSupplyWord σ I).toNat + (mintWadWord I).toNat := by
    unfold mintSupplyCreditNat
    rw [← hsupplyWord]
  exact ⟨hfitUsrSolm, hafterMap, hsupplyNat⟩

set_option maxHeartbeats 1000000 in
theorem mintSolmBridge {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hfitUsr :
      (mintEvmUsrBalanceWord σ I).toNat + (mintWadWord I).toNat < UInt256.size)
    (hfitSupply :
      (mintEvmTotalSupplyWord σ I).toNat + (mintWadWord I).toNat < UInt256.size) :
    mintUsrCreditNat evm I < UInt256.size ∧
    mintSupplyCreditNat (mintAfterUsrCreditState evm I) I < UInt256.size ∧
    accountMapEquiv (mintEvmPostAccountMap σ I) (mintPostState evm I).accountMap := by
  rcases mintSolmAfterUsrBridge howner hAccounts hfitUsr with
    ⟨hfitUsrSolm, hafterMap, hsupplyNat⟩
  have hfitSupplySolm :
      mintSupplyCreditNat (mintAfterUsrCreditState evm I) I < UInt256.size := by
    rw [hsupplyNat]
    exact hfitSupply
  have hsupplyCreditEq :
      mintEvmSupplyCreditWord σ I =
        mintSupplyCreditWord (mintAfterUsrCreditState evm I) I := by
    apply u256_inj
    unfold mintEvmSupplyCreditWord mintSupplyCreditWord
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitSupply]
    rw [ulit_toNat' _ hfitSupplySolm]
    exact hsupplyNat.symm
  have hownerAfter :
      (mintAfterUsrCreditState evm I).executionEnv.codeOwner = I.codeOwner := by
    simpa [mintAfterUsrCredit_codeOwner evm I] using howner
  have hfinal :
      accountMapEquiv (mintEvmPostAccountMap σ I) (mintPostState evm I).accountMap := by
    simpa [mintEvmPostAccountMap, mintPostState, storageStore_accountMap,
      mintTotalSupplySlot, hownerAfter, hsupplyCreditEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner mintTotalSupplySlot
        (mintEvmSupplyCreditWord σ I) hafterMap
  exact ⟨hfitUsrSolm, hfitSupplySolm, hfinal⟩

/-- `mint(address,uint256)` body refines its Solm transition. -/
theorem daiMintBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 7) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some mintTransition :=
    daiDispatchMint hsel
  have hreach := daiReachMintBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := daiDecode_mint_ok (I := I) hsz68
    obtain ⟨_, _, rd2011⟩ :=
      daiMintX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hownerSolm : evmSolm.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm, initState]
    have hsourceSolm : evmSolm.executionEnv.source = I.source := by
      simp [evmSolm, initState]
    have hauthLoadEq :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (mintAuthStorageSlot I) =
          mintAuthWord σ_evm I := by
      have hword : mintAuthWord σ_evm I = mintAuthWord σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner (mintAuthStorageSlot I)
          (⟨0⟩ : UInt256)
      calc
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (mintAuthStorageSlot I) = mintAuthWord σ_solm I := by
          simp [evmSolm, initState, mintAuthWord, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]
        _ = mintAuthWord σ_evm I := hword.symm
    have hUsrCreditNat :
        mintUsrCreditNat evmSolm I =
          (mintEvmUsrBalanceWord σ_evm I).toNat + (mintWadWord I).toNat := by
      have hword :
          mintEvmUsrBalanceWord σ_evm I = mintUsrBalanceWord evmSolm I := by
        have hread :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (mintEvmUsrSlot I)
            (⟨0⟩ : UInt256)
        simpa [mintEvmUsrBalanceWord, mintUsrBalanceWord, mintEvmUsrSlot,
          mintUsrStorageSlot_eq_mapSlot_masked, Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage, solcSlotWord, hownerSolm] using hread
      unfold mintUsrCreditNat
      rw [← hword]
    by_cases hauth : mintAuthWord σ_evm I = ⟨1⟩
    · obtain ⟨_, _, rd2100⟩ := daiMintX_authorized (I := I) hauth rd2011
      have hauthBody :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (mintAuthStorageSlot I) = ⟨1⟩ := by
        rw [hauthLoadEq]
        exact hauth
      by_cases hfitUsr :
          (mintEvmUsrBalanceWord σ_evm I).toNat + (mintWadWord I).toNat <
            UInt256.size
      · rcases mintSolmAfterUsrBridge hownerSolm hAccounts hfitUsr with
          ⟨hfitUsrBody, _hafterMap, hsupplyNat⟩
        by_cases hfitSupply :
            (mintEvmTotalSupplyWord σ_evm I).toNat + (mintWadWord I).toNat <
              UInt256.size
        · rcases mintSolmBridge hownerSolm hAccounts hfitUsr hfitSupply with
            ⟨hfitUsrBody', hfitSupplyBody, hfinal⟩
          have hbody :
              ExecTransitionBody config contract evmSolm (mintStore I)
                mintTransition.body
                (.returned { contract := contract, locals := mintStore I }
                  (mintPostState evmSolm I) none) := by
            simpa [evmSolm] using
              daiMintBodyReturns evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                hsourceSolm
                hauthBody
                hfitUsrBody'
                hfitSupplyBody
          exact (daiMintX_success (g := Sat256.ofUInt256 g) hperm hfitUsr hfitSupply rd2100)
            |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by
                simp [mintPostState, mintAfterUsrCreditState, evmSolm, initState,
                  storageStore_createdAccounts])
              hfinal
              (by
                simpa [mintTransition] using
                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                    (dvs := []) rfl (by native_decide) (by native_decide)))
        · have hover :
              UInt256.size ≤
                (mintEvmTotalSupplyWord σ_evm I).toNat + (mintWadWord I).toNat := by
            omega
          have hoverBody :
              UInt256.size ≤ mintSupplyCreditNat (mintAfterUsrCreditState evmSolm I) I := by
            rw [hsupplyNat]
            exact hover
          have hbody :
              ExecTransitionBody config contract evmSolm (mintStore I)
                mintTransition.body .reverted := by
            simpa [evmSolm] using
              daiMintBodyReverts_supplyOverflow evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                hsourceSolm
                hauthBody
                hfitUsrBody
                hoverBody
          obtain ⟨_, _, rd2161⟩ :=
            daiMintX_storeUsr_success (I := I) (sel := daiSelWord I)
              hperm hfitUsr rd2100
          exact (daiMintX_supplyOverflowRevert (I := I) (sel := daiSelWord I)
              hover rd2161)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hover :
            UInt256.size ≤
              (mintEvmUsrBalanceWord σ_evm I).toNat + (mintWadWord I).toNat := by
          omega
        have hoverBody : UInt256.size ≤ mintUsrCreditNat evmSolm I := by
          rw [hUsrCreditNat]
          exact hover
        have hbody :
            ExecTransitionBody config contract evmSolm (mintStore I)
              mintTransition.body .reverted := by
          simpa [evmSolm] using
            daiMintBodyReverts_usrOverflow evmSolm I
              (by simp only [evmSolm, initState]; exact hwv)
              hsourceSolm
              hauthBody
              hoverBody
        exact (daiMintX_usrOverflowRevert (I := I) (sel := daiSelWord I)
            hover rd2100)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthBody :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (mintAuthStorageSlot I) ≠ ⟨1⟩ := by
        rw [hauthLoadEq]
        exact hauth
      have hbody :
          ExecTransitionBody config contract evmSolm (mintStore I)
            mintTransition.body .reverted := by
        simpa [evmSolm] using
          daiMintBodyReverts_auth evmSolm I
            (by simp only [evmSolm, initState]; exact hwv)
            hsourceSolm
            hauthBody
      exact (daiMintX_unauthorized (I := I) hauth rd2011)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdec := daiDecode_mint_none_short (I := I) hsz4 (by omega)
    exact (daiMintX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch hdec

end Benchmarks.Dss.Dai

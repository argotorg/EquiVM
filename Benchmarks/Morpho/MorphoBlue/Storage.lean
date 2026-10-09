import Benchmarks.Morpho.MorphoBlue.PackedStorage

/-! Morpho storage reads and writes used by the function proofs. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MorphoBlue

theorem evalMorphoAddress (evm : EVM.State) (locals imms : Store) (name : Ident)
    (slot : UInt256) (hbase : locals.get? name = none)
    (hty : storageTypeAt? contract.storage ⟨name, []⟩ = some (.elem .address))
    (hloc : Syntax.modelLayout ⟨name, []⟩ = some (.leaf (addressOffset0Loc slot))) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨name, []⟩) =
      .ok (.address (AccountAddress.ofNat
        (solcAddressSlotWord slot evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]) hty rfl hloc
    (storageLocLoad_address_offset0 evm slot)

-- LIBRARY CANDIDATE: evaluate a single mapping subscript without array bounds.
theorem evalStorageRef_mindex {cfg : Config} {solm : Frame} {evm : EVM.State}
    {base : Ident} {expr : Expr} {value : Value} {key : KeyValue}
    (heval : evalExpr? cfg solm evm expr = .ok value)
    (hkey : valueToKey? value = some key) :
    evalStorageRef cfg solm evm ⟨base, [.mindex expr]⟩ = .ok ⟨base, [.mindex key]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, heval,
    hkey, EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem morphoLayout_isLltvEnabled (w : UInt256) :
    Syntax.modelLayout ⟨"isLltvEnabled", [.mindex (.int (Int.ofNat w.toNat))]⟩ =
      some (.leaf (boolOffset0Loc (solcMappingSlot ⟨5⟩ w))) := by
  change some (StorageAddr.leaf (boolOffset0Loc
    (solcMappingSlot ⟨5⟩ (keyValueToWord (.int (Int.ofNat w.toNat)))))) = _
  rw [keyValueToWord_uint256]

theorem evalMorphoLltvEnabled (evm : EVM.State) (locals imms : Store) (key : Expr) (w : UInt256)
    (hbase : locals.get? "isLltvEnabled" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"isLltvEnabled", [.mindex key]⟩) =
      .ok (wordToElem .bool (UInt256.land
        (solcSlotWordAt (solcMappingSlot ⟨5⟩ w) evm.accountMap evm.executionEnv) ⟨255⟩)) := by
  apply evalExpr_storage_scalar_value hbase (er := ⟨"isLltvEnabled", [.mindex (.int (Int.ofNat w.toNat))]⟩)
  · exact evalStorageRef_mindex hkey rfl
  · rfl
  · rfl
  · exact morphoLayout_isLltvEnabled w
  · exact storageLocLoad_bool_offset0 evm _

theorem morphoLayout_isIrmEnabled (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    Syntax.modelLayout ⟨"isIrmEnabled", [.mindex (.address (AccountAddress.ofNat w.toNat))]⟩ =
      some (.leaf (boolOffset0Loc (solcMappingSlot ⟨4⟩ w))) := by
  change some (StorageAddr.leaf (boolOffset0Loc
    (solcMappingSlot ⟨4⟩ (keyValueToWord (.address (AccountAddress.ofNat w.toNat)))))) = _
  rw [keyValueToWord_address_of_canonical w hcanon]

theorem evalMorphoIrmEnabled (evm : EVM.State) (locals imms : Store) (key : Expr) (w : UInt256)
    (hbase : locals.get? "isIrmEnabled" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"isIrmEnabled", [.mindex key]⟩) =
      .ok (wordToElem .bool (UInt256.land
        (solcSlotWordAt (solcMappingSlot ⟨4⟩ w) evm.accountMap evm.executionEnv) ⟨255⟩)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"isIrmEnabled", [.mindex (.address (AccountAddress.ofNat w.toNat))]⟩)
  · exact evalStorageRef_mindex hkey rfl
  · rfl
  · rfl
  · exact morphoLayout_isIrmEnabled w hcanon
  · exact storageLocLoad_bool_offset0 evm _

theorem morphoLayout_nonce (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    Syntax.modelLayout ⟨"nonce", [.mindex (.address (AccountAddress.ofNat w.toNat))]⟩ =
      some (.leaf (uint256Loc (solcMappingSlot ⟨7⟩ w))) := by
  change some (StorageAddr.leaf (uint256Loc
    (solcMappingSlot ⟨7⟩ (keyValueToWord (.address (AccountAddress.ofNat w.toNat)))))) = _
  rw [keyValueToWord_address_of_canonical w hcanon]

theorem evalMorphoNonce (evm : EVM.State) (locals imms : Store) (key : Expr) (w : UInt256)
    (hbase : locals.get? "nonce" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"nonce", [.mindex key]⟩) =
      .ok (.int (Int.ofNat
        (solcSlotWordAt (solcMappingSlot ⟨7⟩ w) evm.accountMap evm.executionEnv).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"nonce", [.mindex (.address (AccountAddress.ofNat w.toNat))]⟩)
  · exact evalStorageRef_mindex hkey rfl
  · rfl
  · rfl
  · exact morphoLayout_nonce w hcanon
  · exact storageLocLoad_uint256 evm _

def authorizationSlot (authorizer authorized : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨6⟩ authorizer) authorized

theorem morphoLayout_isAuthorized (authorizer authorized : UInt256)
    (hcanon0 : authorizer.toNat < EVM.addressModulus)
    (hcanon1 : authorized.toNat < EVM.addressModulus) :
    Syntax.modelLayout ⟨"isAuthorized",
        [.mindex (.address (AccountAddress.ofNat authorizer.toNat)),
         .mindex (.address (AccountAddress.ofNat authorized.toNat))]⟩ =
      some (.leaf (boolOffset0Loc (authorizationSlot authorizer authorized))) := by
  change some (StorageAddr.leaf (boolOffset0Loc (authorizationSlot
    (keyValueToWord (.address (AccountAddress.ofNat authorizer.toNat)))
    (keyValueToWord (.address (AccountAddress.ofNat authorized.toNat)))))) = _
  rw [keyValueToWord_address_of_canonical authorizer hcanon0,
    keyValueToWord_address_of_canonical authorized hcanon1]

theorem evalMorphoIsAuthorized (evm : EVM.State) (locals imms : Store) (key0 key1 : Expr)
    (authorizer authorized : UInt256)
    (hbase : locals.get? "isAuthorized" = none)
    (hkey0 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key0 = .ok (.address (AccountAddress.ofNat authorizer.toNat)))
    (hkey1 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key1 = .ok (.address (AccountAddress.ofNat authorized.toNat)))
    (hcanon0 : authorizer.toNat < EVM.addressModulus)
    (hcanon1 : authorized.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"isAuthorized", [.mindex key0, .mindex key1]⟩) =
      .ok (wordToElem .bool (UInt256.land
        (solcSlotWordAt (authorizationSlot authorizer authorized)
          evm.accountMap evm.executionEnv) ⟨255⟩)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"isAuthorized", [.mindex (.address (AccountAddress.ofNat authorizer.toNat)),
      .mindex (.address (AccountAddress.ofNat authorized.toNat))]⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey0, hkey1,
      valueToKey?, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact morphoLayout_isAuthorized _ _ hcanon0 hcanon1
  · exact storageLocLoad_bool_offset0 evm _

def marketParamsAddressField : Fin 4 → Ident
  | ⟨0, _⟩ => "loanToken"
  | ⟨1, _⟩ => "collateralToken"
  | ⟨2, _⟩ => "oracle"
  | ⟨3, _⟩ => "irm"

def marketParamsFieldSlot (id : UInt256) (i : Nat) : UInt256 :=
  solcMappingSlot ⟨8⟩ id + UInt256.ofNat i

theorem morphoLayout_marketParamsAddress (id : UInt256) (i : Fin 4) :
    Syntax.modelLayout ⟨"idToMarketParams",
      [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
       .field (marketParamsAddressField i)]⟩ =
      some (.leaf (addressOffset0Loc (marketParamsFieldSlot id i))) := by
  have hloc : Syntax.modelLayout ⟨"idToMarketParams",
      [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
       .field (marketParamsAddressField i)]⟩ =
      some (.leaf (addressOffset0Loc (marketParamsFieldSlot
        (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) i))) := by
    fin_cases i
    all_goals simp only [marketParamsFieldSlot,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
    all_goals rfl
  rw [keyValueToWord_fixedBytes32] at hloc
  exact hloc

theorem morphoLayout_marketParamsLltv (id : UInt256) :
    Syntax.modelLayout ⟨"idToMarketParams",
      [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)), .field "lltv"]⟩ =
      some (.leaf (uint256Loc (marketParamsFieldSlot id 4))) := by
  change some (StorageAddr.leaf (uint256Loc (marketParamsFieldSlot
    (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) 4))) = _
  rw [keyValueToWord_fixedBytes32]

def marketParamsWord (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (i : Nat) : UInt256 :=
  solcSlotWordAt (marketParamsFieldSlot id i) σ I

theorem evalMorphoMarketParamsAddress (evm : EVM.State) (locals imms : Store)
    (key : Expr) (id : UInt256) (i : Fin 4)
    (hbase : locals.get? "idToMarketParams" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"idToMarketParams", [.mindex key, .field (marketParamsAddressField i)]⟩) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (marketParamsWord evm.accountMap evm.executionEnv id i) solcAddrMask).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"idToMarketParams", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .field (marketParamsAddressField i)]⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1), ↓reduceIte,
      EvalResult.ofOption, pure, bind, EvalResult.bind]
  · fin_cases i <;> rfl
  · rfl
  · exact morphoLayout_marketParamsAddress id i
  · exact storageLocLoad_address_offset0 evm _

theorem evalMorphoMarketParamsLltv (evm : EVM.State) (locals imms : Store)
    (key : Expr) (id : UInt256)
    (hbase : locals.get? "idToMarketParams" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"idToMarketParams", [.mindex key, .field "lltv"]⟩) =
      .ok (.int (Int.ofNat (marketParamsWord evm.accountMap evm.executionEnv id 4).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"idToMarketParams", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .field "lltv"]⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1), ↓reduceIte,
      EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact morphoLayout_marketParamsLltv id
  · exact storageLocLoad_uint256 evm _

def marketFieldName : Fin 6 → Ident
  | ⟨0, _⟩ => "totalSupplyAssets"
  | ⟨1, _⟩ => "totalSupplyShares"
  | ⟨2, _⟩ => "totalBorrowAssets"
  | ⟨3, _⟩ => "totalBorrowShares"
  | ⟨4, _⟩ => "lastUpdate"
  | ⟨5, _⟩ => "fee"

def marketFieldSlot (id : UInt256) (i : Nat) : UInt256 :=
  solcMappingSlot ⟨3⟩ id + UInt256.ofNat (i / 2)

def marketFieldWord (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (i : Nat) : UInt256 :=
  halfWord (decide (i % 2 = 1)) (solcSlotWordAt (marketFieldSlot id i) σ I)

theorem morphoLayout_marketField (id : UInt256) (i : Fin 6) :
    Syntax.modelLayout ⟨"market",
      [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
       .field (marketFieldName i)]⟩ =
      some (.leaf (uint128HalfLoc (marketFieldSlot id i) (decide (i.val % 2 = 1)))) := by
  have hloc : Syntax.modelLayout ⟨"market",
      [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
       .field (marketFieldName i)]⟩ =
      some (.leaf (uint128HalfLoc (marketFieldSlot
        (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) i)
          (decide (i.val % 2 = 1)))) := by
    fin_cases i
    all_goals simp only [marketFieldSlot,
      show UInt256.ofNat (0 / 2) = (⟨0⟩ : UInt256) from rfl,
      show UInt256.ofNat (1 / 2) = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
    all_goals rfl
  rw [keyValueToWord_fixedBytes32] at hloc
  exact hloc

theorem evalMorphoMarketField (evm : EVM.State) (locals imms : Store)
    (key : Expr) (id : UInt256) (i : Fin 6)
    (hbase : locals.get? "market" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"market", [.mindex key, .field (marketFieldName i)]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord evm.accountMap evm.executionEnv id i).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"market", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .field (marketFieldName i)]⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1), ↓reduceIte,
      EvalResult.ofOption, pure, bind, EvalResult.bind]
  · fin_cases i <;> rfl
  · rfl
  · exact morphoLayout_marketField id i
  · exact storageLocLoad_uint128Half evm _ _

def positionSlot (id account : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨2⟩ id) account

def positionFieldName : Fin 3 → Ident
  | ⟨0, _⟩ => "supplyShares"
  | ⟨1, _⟩ => "borrowShares"
  | ⟨2, _⟩ => "collateral"

def positionFieldLoc (id account : UInt256) (i : Fin 3) : StorageLoc :=
  if i.val = 0 then uint256Loc (positionSlot id account)
  else uint128HalfLoc (positionSlot id account + ⟨1⟩) (decide (i.val = 2))

def positionFieldWord (σ : AccountMap) (I : ExecutionEnv) (id account : UInt256)
    (i : Fin 3) : UInt256 :=
  if i.val = 0 then solcSlotWordAt (positionSlot id account) σ I
  else halfWord (decide (i.val = 2)) (solcSlotWordAt (positionSlot id account + ⟨1⟩) σ I)

theorem morphoLayout_position (id account : UInt256) (i : Fin 3)
    (hcanon : account.toNat < EVM.addressModulus) :
    Syntax.modelLayout ⟨"position",
      [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
       .mindex (.address (AccountAddress.ofNat account.toNat)), .field (positionFieldName i)]⟩ =
      some (.leaf (positionFieldLoc id account i)) := by
  have hloc : Syntax.modelLayout ⟨"position",
      [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
       .mindex (.address (AccountAddress.ofNat account.toNat)), .field (positionFieldName i)]⟩ =
      some (.leaf (positionFieldLoc
        (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)))
        (keyValueToWord (.address (AccountAddress.ofNat account.toNat))) i)) := by
    fin_cases i <;> rfl
  rw [keyValueToWord_fixedBytes32, keyValueToWord_address_of_canonical account hcanon] at hloc
  exact hloc

theorem evalMorphoPositionField (evm : EVM.State) (locals imms : Store)
    (key0 key1 : Expr) (id account : UInt256) (i : Fin 3)
    (hbase : locals.get? "position" = none)
    (hkey0 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key0 = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)))
    (hkey1 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key1 = .ok (.address (AccountAddress.ofNat account.toNat)))
    (hcanon : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"position", [.mindex key0, .mindex key1, .field (positionFieldName i)]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord evm.accountMap evm.executionEnv id account i).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"position", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .mindex (.address (AccountAddress.ofNat account.toNat)), .field (positionFieldName i)]⟩)
    (loc := positionFieldLoc id account i)
    (t := if i.val = 0 then .int (.uint ⟨256, by decide⟩) else .int (.uint ⟨128, by decide⟩))
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey0, hkey1,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1), ↓reduceIte,
      EvalResult.ofOption, pure, bind, EvalResult.bind]
  · fin_cases i <;> rfl
  · rfl
  · exact morphoLayout_position id account i hcanon
  · fin_cases i
    · exact storageLocLoad_uint256 evm _
    · exact storageLocLoad_uint128Half evm _ false
    · exact storageLocLoad_uint128Half evm _ true

-- LIBRARY CANDIDATE: address-value equality agrees with equality of canonical words.
theorem canonicalAddress_beq (a b : UInt256)
    (ha : a.toNat < EVM.addressModulus) (hb : b.toNat < EVM.addressModulus) :
    (Value.address (AccountAddress.ofNat a.toNat) ==
      Value.address (AccountAddress.ofNat b.toNat)) = decide (a = b) := by
  have hab : AccountAddress.ofNat a.toNat = AccountAddress.ofNat b.toNat ↔ a = b := by
    simpa only [u256_land_comm solcAddrMask, solcAddrMask_clean ha, solcAddrMask_clean hb] using
      addressOfNat_eq_iff_solcAddrMask_eq a b
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq, hab]

theorem evalMorphoOwnerCheck (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "owner" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .eq (.env .caller) (.storage ⟨"owner", []⟩)) =
      .ok (.bool (decide (solcSourceWord evm.executionEnv =
        solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv))) := by
  have hload := evalMorphoAddress evm locals imms "owner" ⟨0⟩ hbase rfl rfl
  simp only [evalExpr?, hload, envValue, evalBinaryOp?, bind, pure, EvalResult.bind]
  rw [← solcSource_ofNat evm.executionEnv]
  rw [canonicalAddress_beq _ _ (solcSourceWord_canonical _) (solcAddrMask_result_canonical _)]

theorem evalMorphoAddressNe (evm : EVM.State) (locals imms : Store)
    (name : Ident) (slot value : UInt256) (expr : Expr)
    (hbase : locals.get? name = none)
    (hty : storageTypeAt? contract.storage ⟨name, []⟩ = some (.elem .address))
    (hloc : Syntax.modelLayout ⟨name, []⟩ = some (.leaf (addressOffset0Loc slot)))
    (hexpr : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (.address (AccountAddress.ofNat value.toNat)))
    (hcanon : value.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .ne expr (.storage ⟨name, []⟩)) =
      .ok (.bool (decide (value ≠ solcAddressSlotWord slot evm.accountMap evm.executionEnv))) := by
  have hload := evalMorphoAddress evm locals imms name slot hbase hty hloc
  simp only [evalExpr?, hload, hexpr, evalBinaryOp?, bind, pure, EvalResult.bind]
  rw [canonicalAddress_beq _ _ hcanon (solcAddrMask_result_canonical _)]
  simp only [decide_not]

theorem assignMorphoAddress (evm : EVM.State) (locals imms : Store)
    (name : Ident) (slot value : UInt256)
    (hbase : locals.get? name = none)
    (hty : storageTypeAt? contract.storage ⟨name, []⟩ = some (.elem .address))
    (hloc : Syntax.modelLayout ⟨name, []⟩ = some (.leaf (addressOffset0Loc slot)))
    (hcanon : value.toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage ⟨name, []⟩ (.address (AccountAddress.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  apply assignStorageRef_storage_scalar_value hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind])
    hty rfl hloc (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_address_offset0 evm slot value hcanon

-- LIBRARY CANDIDATE: negating a storage boolean tests whether its low byte is zero.
theorem evalNotBoolWord {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm e = .ok (wordToElem .bool w)) :
    evalExpr? cfg frame evm (.unary .not e) = .ok (.bool (decide (w = ⟨0⟩))) := by
  simp only [evalExpr?, he, wordToElemBool, evalUnaryOp?, bind, pure, EvalResult.bind,
    Bool.not_not, EvalResult.ofOption]

-- LIBRARY CANDIDATE: a boolean mapping write, given its resolved storage layout.
theorem assignBoolMappingTrue {cfg : Config} {frame : Frame} {evm : EVM.State}
    {layout : StorageLayout} {name : Ident} {key : Expr} {value : Value} {kv : KeyValue}
    {slot : UInt256}
    (hbase : frame.locals.get? name = none)
    (hkey : evalExpr? cfg frame evm key = .ok value)
    (hkv : valueToKey? value = some kv)
    (hty : storageTypeAt? frame.contract.storage ⟨name, [.mindex kv]⟩ = some (.elem .bool))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout ⟨name, [.mindex kv]⟩ = some (.leaf (boolOffset0Loc slot))) :
    assignStorageRef? cfg frame evm .storage ⟨name, [.mindex key]⟩ (.bool true) =
      .ok (frame, Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  exact assignStorageRef_storage_scalar_value hbase (evalStorageRef_mindex hkey hkv)
    hty hbackend hloc (Or.inl ⟨_, rfl⟩) (storageLocStore_bool_true_offset0 evm slot)

-- LIBRARY CANDIDATE: boolean values agree exactly when their normalized EVM words agree.
theorem wordToElemBool_beq (a b : UInt256) :
    (wordToElem .bool a == wordToElem .bool b) =
      decide (UInt256.isZero (UInt256.isZero a) = UInt256.isZero (UInt256.isZero b)) := by
  have hn (w : UInt256) : UInt256.isZero (UInt256.isZero w) =
      if w = ⟨0⟩ then ⟨0⟩ else ⟨1⟩ := by
    by_cases hw : w = ⟨0⟩
    · rw [hw]; decide
    · rw [if_neg hw, isZero_eq_zero_of_ne hw]
      decide
  simp only [wordToElemBool, hn]
  by_cases ha : a = ⟨0⟩ <;> by_cases hb : b = ⟨0⟩ <;> simp [ha, hb]
  all_goals decide

-- LIBRARY CANDIDATE: boolean inequality evaluation in terms of EVM normalization.
theorem evalBoolWordNe {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (wordToElem .bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (wordToElem .bool b)) :
    evalExpr? cfg frame evm (.binary .ne lhs rhs) = .ok (.bool
      (decide (UInt256.isZero (UInt256.isZero a) ≠ UInt256.isZero (UInt256.isZero b)))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  have hab := wordToElemBool_beq a b
  simp only [wordToElemBool] at hab
  simp only [bind, pure, EvalResult.bind, wordToElemBool, evalBinaryOp?, hab, decide_not]

-- LIBRARY CANDIDATE: a normalized boolean fits in one storage byte.
theorem boolWordClean_land255 (w : UInt256) :
    UInt256.land (UInt256.isZero (UInt256.isZero w)) ⟨255⟩ = UInt256.isZero (UInt256.isZero w) := by
  by_cases hw : w = ⟨0⟩
  · rw [hw]; decide
  · rw [isZero_eq_zero_of_ne hw]; decide

-- LIBRARY CANDIDATE: canonical word view of the current caller.
theorem evalCallerWord (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg frame evm (.env .caller) =
      .ok (.address (AccountAddress.ofNat (solcSourceWord evm.executionEnv).toNat)) := by
  simp only [evalExpr?, envValue, pure, solcSource_ofNat]

theorem assignMorphoIsAuthorized (evm : EVM.State) (locals imms : Store)
    (key0 key1 : Expr) (authorizer authorized word : UInt256)
    (hbase : locals.get? "isAuthorized" = none)
    (hkey0 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key0 = .ok (.address (AccountAddress.ofNat authorizer.toNat)))
    (hkey1 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key1 = .ok (.address (AccountAddress.ofNat authorized.toNat)))
    (hcanon0 : authorizer.toNat < EVM.addressModulus)
    (hcanon1 : authorized.toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage ⟨"isAuthorized", [.mindex key0, .mindex key1]⟩ (wordToElem .bool word) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (authorizationSlot authorizer authorized)
          (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (authorizationSlot authorizer authorized)) word)) := by
  apply assignStorageRef_storage_scalar_value hbase
    (er := ⟨"isAuthorized", [.mindex (.address (AccountAddress.ofNat authorizer.toNat)),
      .mindex (.address (AccountAddress.ofNat authorized.toNat))]⟩)
    (loc := boolOffset0Loc (authorizationSlot authorizer authorized))
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey0, hkey1,
      valueToKey?, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact morphoLayout_isAuthorized _ _ hcanon0 hcanon1
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_bool_word_offset0 evm _ word

end Benchmarks.Morpho.MorphoBlue

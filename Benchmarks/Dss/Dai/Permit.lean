import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.DomainSeparator
import Benchmarks.Dss.Dai.Storage
import Ethereum.Theory.OpcodeLemmas
import Reasoning.ExternalCall
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level locals for `permit(...)` -/

abbrev permitHolderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev permitHolderMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (permitHolderWord I)

abbrev permitSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev permitSpenderMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (permitSpenderWord I)

abbrev permitNonceWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev permitExpiryWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev permitAllowedWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev permitVWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 164

abbrev permitVMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (permitVWord I) ⟨255⟩

abbrev permitAllowedCleanWord (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (permitAllowedWord I))

abbrev permitRWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 196

abbrev permitSWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 228

abbrev permitRBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 196).take 32

abbrev permitSBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 228).take 32

abbrev permitHolderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (permitHolderWord I).toNat)

abbrev permitSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (permitSpenderWord I).toNat)

abbrev permitNonceValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (permitNonceWord I).toNat)

abbrev permitExpiryValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (permitExpiryWord I).toNat)

abbrev permitAllowedValue (I : ExecutionEnv) : Value :=
  if (permitAllowedWord I).toNat = 0 then .bool false else .bool true

abbrev permitVValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat ((permitVWord I).toNat % EVM.twoPow 8))

abbrev permitRValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (permitRBytes I)

abbrev permitSValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (permitSBytes I)

abbrev permitStore (I : ExecutionEnv) : Store :=
  ((((((((∅ : Store).insert "holder" (permitHolderValue I)).insert "spender"
    (permitSpenderValue I)).insert "nonce" (permitNonceValue I)).insert "expiry"
    (permitExpiryValue I)).insert "allowed" (permitAllowedValue I)).insert "v"
    (permitVValue I)).insert "r" (permitRValue I)).insert "s" (permitSValue I)

abbrev permitHolderKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (permitHolderWord I).toNat)

abbrev permitSpenderKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (permitSpenderWord I).toNat)

def permitNonceStorageSlot (I : ExecutionEnv) : UInt256 :=
  noncesSlot (permitHolderKey I)

def permitAllowanceStorageSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (permitHolderKey I) (permitSpenderKey I)

abbrev permitNonceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "nonces", steps := [.mindex (permitHolderKey I)] }

abbrev permitAllowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (permitHolderKey I), .mindex (permitSpenderKey I)] }

def permitNonceStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (permitNonceStorageSlot I) ⟨0⟩)

abbrev permitEvmNonceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  permitNonceStoredWord σ I

abbrev permitEvmAfterNonceAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (permitNonceStorageSlot I)
    (permitEvmNonceWord σ I + ⟨1⟩)

abbrev permitWadWord (I : ExecutionEnv) : UInt256 :=
  if (permitAllowedWord I).toNat = 0 then ⟨0⟩ else UInt256.lnot ⟨0⟩

abbrev permitEvmPostAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (permitEvmAfterNonceAccountMap σ I)
    (permitAllowanceStorageSlot I) (permitWadWord I)

def permitPostNonceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (permitNonceStorageSlot I)
    (UInt256.add (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (permitNonceStorageSlot I)) ⟨1⟩)

def permitPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (permitPostNonceState evm I) evm.executionEnv.codeOwner
    (permitAllowanceStorageSlot I) (permitWadWord I)

abbrev permitStructPackedBytes (I : ExecutionEnv) : List UInt8 :=
  permitTypehashBytes ++
    EVM.Word.toBytesBE (permitHolderMaskedWord I) ++
    EVM.Word.toBytesBE (permitSpenderMaskedWord I) ++
    EVM.Word.toBytesBE (permitNonceWord I) ++
    EVM.Word.toBytesBE (permitExpiryWord I) ++
    EVM.Word.toBytesBE (permitAllowedCleanWord I)

abbrev permitStructPackedByteArray (I : ExecutionEnv) : ByteArray :=
  permitTypehashBytes.toByteArray ++
    ((EVM.Word.toBytesBE (permitHolderMaskedWord I)).toByteArray ++
      ((EVM.Word.toBytesBE (permitSpenderMaskedWord I)).toByteArray ++
        ((EVM.Word.toBytesBE (permitNonceWord I)).toByteArray ++
          ((EVM.Word.toBytesBE (permitExpiryWord I)).toByteArray ++
            (EVM.Word.toBytesBE (permitAllowedCleanWord I)).toByteArray))))

abbrev permitStructHashBytes (I : ExecutionEnv) : List UInt8 :=
  (ffi.KEC (permitStructPackedByteArray I)).toList

abbrev permitStructHashWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (ffi.KEC (permitStructPackedByteArray I))

abbrev permitDigestPackedBytes (evm : EVM.State) (I : ExecutionEnv) : List UInt8 :=
  [25, 1] ++
    EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      domainSeparatorStorageSlot) ++
    permitStructHashBytes I

abbrev permitDigestPackedByteArray (evm : EVM.State) (I : ExecutionEnv) : ByteArray :=
  ([25, 1] ++ EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    domainSeparatorStorageSlot)).toByteArray ++ (permitStructHashBytes I).toByteArray

abbrev permitDigestBytes (evm : EVM.State) (I : ExecutionEnv) : List UInt8 :=
  (ffi.KEC (permitDigestPackedByteArray evm I)).toList

abbrev permitDigestWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (ffi.KEC (permitDigestPackedByteArray evm I))

abbrev permitEcrecoverCalldata (evm : EVM.State) (I : ExecutionEnv) : ByteArray :=
  (permitDigestBytes evm I).toByteArray ++
    ((EVM.Word.toBytesBE (permitVMaskedWord I)).toByteArray ++
      ((permitRBytes I).toByteArray ++ (permitSBytes I).toByteArray))

abbrev permitDigestStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (permitStore I).insert "digest" (.fixedBytes bytes32Width (permitDigestBytes evm I))

theorem permitStore_get_holder (I : ExecutionEnv) :
    (permitStore I).get? "holder" = some (permitHolderValue I) := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_spender (I : ExecutionEnv) :
    (permitStore I).get? "spender" = some (permitSpenderValue I) := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_nonce (I : ExecutionEnv) :
    (permitStore I).get? "nonce" = some (permitNonceValue I) := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_expiry (I : ExecutionEnv) :
    (permitStore I).get? "expiry" = some (permitExpiryValue I) := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_allowed (I : ExecutionEnv) :
    (permitStore I).get? "allowed" = some (permitAllowedValue I) := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_v (I : ExecutionEnv) :
    (permitStore I).get? "v" = some (permitVValue I) := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_r (I : ExecutionEnv) :
    (permitStore I).get? "r" = some (permitRValue I) := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_s (I : ExecutionEnv) :
    (permitStore I).get? "s" = some (permitSValue I) := by
  unfold permitStore
  simp

theorem permitStore_get_DOMAIN_SEPARATOR (I : ExecutionEnv) :
    (permitStore I).get? "DOMAIN_SEPARATOR" = none := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_nonces (I : ExecutionEnv) :
    (permitStore I).get? "nonces" = none := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitStore_get_allowance (I : ExecutionEnv) :
    (permitStore I).get? "allowance" = none := by
  unfold permitStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem permitDigestStore_get_v (evm : EVM.State) (I : ExecutionEnv) :
    (permitDigestStore evm I).get? "v" = some (permitVValue I) := by
  unfold permitDigestStore
  rw [store_get_ne _ _ (by native_decide)]
  exact permitStore_get_v I

theorem permitDigestStore_get_r (evm : EVM.State) (I : ExecutionEnv) :
    (permitDigestStore evm I).get? "r" = some (permitRValue I) := by
  unfold permitDigestStore
  rw [store_get_ne _ _ (by native_decide)]
  exact permitStore_get_r I

theorem permitDigestStore_get_s (evm : EVM.State) (I : ExecutionEnv) :
    (permitDigestStore evm I).get? "s" = some (permitSValue I) := by
  unfold permitDigestStore
  rw [store_get_ne _ _ (by native_decide)]
  exact permitStore_get_s I

theorem permitNonceStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    permitNonceStorageSlot I = mapSlot (permitHolderMaskedWord I) ⟨4⟩ := by
  unfold permitNonceStorageSlot noncesSlot permitHolderKey permitHolderMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem permitAllowanceStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    permitAllowanceStorageSlot I =
      mapSlot (permitSpenderMaskedWord I) (mapSlot (permitHolderMaskedWord I) ⟨3⟩) := by
  unfold permitAllowanceStorageSlot allowanceSlot allowanceOwnerSlot permitHolderKey permitSpenderKey
    permitHolderMaskedWord permitSpenderMaskedWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address_ofNat_mask]

theorem permitRBytes_length {I : ExecutionEnv} (hsz260 : 260 ≤ I.calldata.size) :
    (permitRBytes I).length = 32 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold permitRBytes
  rw [List.length_take, List.length_drop, htlen]
  omega

theorem permitSBytes_length {I : ExecutionEnv} (hsz260 : 260 ≤ I.calldata.size) :
    (permitSBytes I).length = 32 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold permitSBytes
  rw [List.length_take, List.length_drop, htlen]
  omega

theorem permitStructHashWord_toBytesBE (I : ExecutionEnv) :
    EVM.Word.toBytesBE (permitStructHashWord I) = permitStructHashBytes I := by
  unfold permitStructHashWord permitStructHashBytes
  exact toBytesBE_uInt256OfByteArray_of_size (keccak_size _)

theorem permitDigestWord_toBytesBE (evm : EVM.State) (I : ExecutionEnv) :
    EVM.Word.toBytesBE (permitDigestWord evm I) = permitDigestBytes evm I := by
  unfold permitDigestWord permitDigestBytes
  exact toBytesBE_uInt256OfByteArray_of_size (keccak_size _)

theorem permitStructHashBytes_length (I : ExecutionEnv) :
    (permitStructHashBytes I).length = 32 := by
  unfold permitStructHashBytes
  rw [byteArray_toList_eq, Array.length_toList]
  exact keccak_size _

theorem permitDigestBytes_length (evm : EVM.State) (I : ExecutionEnv) :
    (permitDigestBytes evm I).length = 32 := by
  unfold permitDigestBytes
  rw [byteArray_toList_eq, Array.length_toList]
  exact keccak_size _

theorem permitTypehashBytes_length : permitTypehashBytes.length = 32 := by
  native_decide

theorem permitAllowedCleanWord_stable (I : ExecutionEnv) :
    UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)) = permitAllowedCleanWord I := by
  unfold permitAllowedCleanWord
  by_cases h : permitAllowedWord I = ⟨0⟩
  · rw [h]
    native_decide
  · rw [isZero_eq_zero_of_ne h]
    native_decide

theorem word_toBytesBE_length_32 (w : UInt256) :
    (EVM.Word.toBytesBE w).length = 32 := by
  simpa using word_toBytesBE_toByteArray_size w

theorem byteArray_mk_toArray_eq_toByteArray (xs : List UInt8) :
    ByteArray.mk xs.toArray = xs.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change xs.toArray.toList = xs.toByteArray.data.toList
  rw [show xs.toArray.toList = xs by simp]
  rw [List.toList_data_toByteArray]

theorem eip191ByteArray_toList : (⟨#[25, 1]⟩ : ByteArray).toList = [25, 1] := by
  native_decide

theorem permitStructPackedByteArray_eq (I : ExecutionEnv) :
    ByteArray.mk
        (permitTypehashBytes ++
          (EVM.Word.toBytesBE (permitHolderMaskedWord I) ++
            (EVM.Word.toBytesBE (permitSpenderMaskedWord I) ++
              (EVM.Word.toBytesBE (permitNonceWord I) ++
                (EVM.Word.toBytesBE (permitExpiryWord I) ++
                  EVM.Word.toBytesBE (permitAllowedCleanWord I)))))).toArray =
      permitStructPackedByteArray I := by
  unfold permitStructPackedByteArray
  rw [byteArray_mk_toArray_eq_toByteArray]
  simp only [List.toByteArray_append, ByteArray.append_assoc]

theorem permitDigestPackedByteArray_eq (evm : EVM.State) (I : ExecutionEnv) :
    ByteArray.mk
        ([25, 1] ++
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            domainSeparatorStorageSlot) ++ permitStructHashBytes I)).toArray =
      permitDigestPackedByteArray evm I := by
  unfold permitDigestPackedByteArray
  rw [byteArray_mk_toArray_eq_toByteArray]
  simp only [List.toByteArray_append, ByteArray.append_assoc]

theorem permitEcrecoverCalldata_eq (evm : EVM.State) (I : ExecutionEnv) :
    ByteArray.mk
        (permitDigestBytes evm I ++
          (EVM.Word.toBytesBE (permitVMaskedWord I) ++
            (permitRBytes I ++ permitSBytes I))).toArray =
      permitEcrecoverCalldata evm I := by
  unfold permitEcrecoverCalldata
  rw [byteArray_mk_toArray_eq_toByteArray]
  simp only [List.toByteArray_append, ByteArray.append_assoc]

theorem permitEcrecoverCalldata_initState_accountMapEquiv {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : Sat256} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    permitEcrecoverCalldata (initState cA gh bl σ_evm σ₀ g A I) I =
      permitEcrecoverCalldata (initState cA gh bl σ_solm σ₀ g A I) I := by
  have hload :
      Solm.EVM.storageLoad (initState cA gh bl σ_evm σ₀ g A I)
          (initState cA gh bl σ_evm σ₀ g A I).executionEnv.codeOwner
          domainSeparatorStorageSlot =
        Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
          (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
          domainSeparatorStorageSlot := by
    simpa [initState] using
      storageLoad_accountMapEquiv (by simpa [initState] using hAccounts) I.codeOwner
        domainSeparatorStorageSlot
  have hpacked :
      permitDigestPackedByteArray (initState cA gh bl σ_evm σ₀ g A I) I =
        permitDigestPackedByteArray (initState cA gh bl σ_solm σ₀ g A I) I := by
    unfold permitDigestPackedByteArray
    rw [hload]
  unfold permitEcrecoverCalldata permitDigestBytes
  rw [hpacked]

theorem addressOfNat_toNat_masked (w : UInt256) :
    (AccountAddress.ofNat w.toNat).toNat = (UInt256.land w solcAddrMask).toNat := by
  have hmaskAddr :
      AccountAddress.ofNat w.toNat = AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat := by
    apply Fin.ext
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    rw [uland_toNat]
    change w.val.val % AccountAddress.size =
      Nat.land w.val.val solcAddrMask.toNat % AccountAddress.size
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_mask_eq_mod]
    rw [show AccountAddress.size = 2 ^ 160 by rfl]
    rw [Nat.mod_mod]
  have hcanon : (UInt256.land w solcAddrMask).toNat < AccountAddress.size := by
    simpa [EVM.addressModulus] using solcAddrMask_result_canonical w
  rw [hmaskAddr]
  unfold AccountAddress.ofNat
  change (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
    (UInt256.land w solcAddrMask).toNat
  exact Nat.mod_eq_of_lt hcanon

theorem addressOfNat_eq_iff_solcAddrMask_eq (a b : UInt256) :
    AccountAddress.ofNat a.toNat = AccountAddress.ofNat b.toNat ↔
      UInt256.land solcAddrMask a = UInt256.land solcAddrMask b := by
  constructor
  · intro haddr
    have h := congrArg (fun addr : AccountAddress => keyValueToWord (.address addr)) haddr
    simpa [keyValueToWord_address_ofNat_mask] using h
  · intro hmask
    apply Fin.ext
    change (AccountAddress.ofNat a.toNat).toNat = (AccountAddress.ofNat b.toNat).toNat
    have ha := addressOfNat_toNat_masked a
    have hb := addressOfNat_toNat_masked b
    rw [ha, hb]
    have hmask' : UInt256.land a solcAddrMask = UInt256.land b solcAddrMask := by
      simpa [u256_land_comm solcAddrMask a, u256_land_comm solcAddrMask b] using hmask
    rw [hmask']

theorem encodePacked_uint256_word (value : UInt256) :
    encodePackedValue? uint256 (.int (Int.ofNat value.toNat)) =
      some (EVM.Word.toBytesBE value) := by
  have hword : EVM.word value.toNat = value := u256_ofNat_toNat value
  have hlt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < EVM.twoPow 256
    exact value.val.isLt
  simp [encodePackedValue?, uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem encodePacked_uint256_v (I : ExecutionEnv) :
    encodePackedValue? uint256 (permitVValue I) =
      some (EVM.Word.toBytesBE (permitVMaskedWord I)) := by
  unfold permitVValue permitVMaskedWord
  have hmod :
      (permitVWord I).toNat % EVM.twoPow 8 =
        (UInt256.land (permitVWord I) ⟨255⟩).toNat := by
    have hland :
        (UInt256.land (permitVWord I) ⟨255⟩).toNat =
          (permitVWord I).toNat % EVM.twoPow 8 := by
      rw [uland_toNat]
      rw [show (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 by decide]
      change Nat.land (permitVWord I).toNat (2 ^ 8 - 1) =
        (permitVWord I).toNat % EVM.twoPow 8
      rw [nat_land_mask_eq_mod]
      rfl
    exact hland.symm
  rw [hmod]
  exact encodePacked_uint256_word (UInt256.land (permitVWord I) ⟨255⟩)

theorem encodePacked_bytes32_of_length {bytes : List UInt8}
    (hlen : bytes.length = fixedBytesSize bytes32Width) :
    encodePackedValue? bytes32 (.fixedBytes bytes32Width bytes) = some bytes := by
  simp [encodePackedValue?, bytes32, fixedBytesSize, hlen]

theorem encodePacked_dynamic_bytes (bytes : ByteArray) :
    encodePackedValue? ABIType.bytes (.bytes bytes) = some bytes.toList := by
  rfl

theorem evalPackedArgs_cons_ok {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head tailBytes : List UInt8}
    {rest : List (ABIType × Expr)}
    (heval : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head)
    (htail : evalPackedArgs? cfg solm evm rest = .ok tailBytes) :
    evalPackedArgs? cfg solm evm ((ty, e) :: rest) = .ok (head ++ tailBytes) := by
  rw [evalPackedArgs?]
  simp only [heval, henc, htail, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_zeroAddr (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  unfold zeroAddr addrSt
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_permitStore_holder (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm (.var "holder") =
      .ok (permitHolderValue I) := by
  rw [evalExpr?]
  rw [permitStore_get_holder]
  simp [EvalResult.ofOption]

theorem evalExpr_permitStore_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm (.var "spender") =
      .ok (permitSpenderValue I) := by
  rw [evalExpr?]
  rw [permitStore_get_spender]
  simp [EvalResult.ofOption]

theorem evalExpr_permitStore_nonce (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm (.var "nonce") =
      .ok (permitNonceValue I) := by
  rw [evalExpr?]
  rw [permitStore_get_nonce]
  simp [EvalResult.ofOption]

theorem evalExpr_permitStore_expiry (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm (.var "expiry") =
      .ok (permitExpiryValue I) := by
  rw [evalExpr?]
  rw [permitStore_get_expiry]
  simp [EvalResult.ofOption]

theorem evalExpr_permitStore_allowed (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm (.var "allowed") =
      .ok (permitAllowedValue I) := by
  rw [evalExpr?]
  rw [permitStore_get_allowed]
  simp [EvalResult.ofOption]

theorem evalExpr_permitStore_holder_uint256 (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (addressAsUint256 (.var "holder")) =
        .ok (.int (Int.ofNat (permitHolderMaskedWord I).toNat)) := by
  unfold addressAsUint256 uint256St
  have haddrLt :
      (AccountAddress.ofNat (permitHolderWord I).toNat).toNat < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (AccountAddress.ofNat (permitHolderWord I).toNat).isLt
      (show AccountAddress.size ≤ EVM.twoPow 256 from by decide)
  have haddrLt' : ↑(AccountAddress.ofNat (permitHolderWord I).toNat) < EVM.twoPow 256 := haddrLt
  rw [evalExpr?]
  simp [evalExpr_permitStore_holder, permitHolderValue, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, uint256Int]
  rw [if_pos haddrLt']
  have haddrEq :
      ↑(AccountAddress.ofNat (permitHolderWord I).toNat) = (permitHolderMaskedWord I).toNat := by
    change (AccountAddress.ofNat (permitHolderWord I).toNat).toNat =
      (permitHolderMaskedWord I).toNat
    rw [addressOfNat_toNat_masked]
    rw [u256_land_comm (permitHolderWord I) solcAddrMask]
  simp [haddrEq]

theorem evalExpr_permitStore_spender_uint256 (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (addressAsUint256 (.var "spender")) =
        .ok (.int (Int.ofNat (permitSpenderMaskedWord I).toNat)) := by
  unfold addressAsUint256 uint256St
  have haddrLt :
      (AccountAddress.ofNat (permitSpenderWord I).toNat).toNat < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (AccountAddress.ofNat (permitSpenderWord I).toNat).isLt
      (show AccountAddress.size ≤ EVM.twoPow 256 from by decide)
  have haddrLt' : ↑(AccountAddress.ofNat (permitSpenderWord I).toNat) < EVM.twoPow 256 :=
    haddrLt
  rw [evalExpr?]
  simp [evalExpr_permitStore_spender, permitSpenderValue, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, uint256Int]
  rw [if_pos haddrLt']
  have haddrEq :
      ↑(AccountAddress.ofNat (permitSpenderWord I).toNat) = (permitSpenderMaskedWord I).toNat := by
    change (AccountAddress.ofNat (permitSpenderWord I).toNat).toNat =
      (permitSpenderMaskedWord I).toNat
    rw [addressOfNat_toNat_masked]
    rw [u256_land_comm (permitSpenderWord I) solcAddrMask]
  simp [haddrEq]

theorem evalExpr_permitStore_allowed_clean (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.ite (.var "allowed") (.intLit 1) (.intLit 0)) =
        .ok (.int (Int.ofNat (permitAllowedCleanWord I).toNat)) := by
  rw [evalExpr?]
  rw [evalExpr_permitStore_allowed]
  simp only [EvalResult.bind, bind, pure]
  unfold permitAllowedValue permitAllowedCleanWord
  by_cases hzero : (permitAllowedWord I).toNat = 0
  · rw [if_pos hzero]
    have hclean : permitAllowedCleanWord I = ⟨0⟩ := by
      unfold permitAllowedCleanWord
      rw [uint256_toNat_eq_zero hzero]
      decide
    change
      (match Value.bool false with
      | Value.bool true => evalExpr? config { contract := contract, locals := permitStore I } evm (Expr.intLit 1)
      | Value.bool false => evalExpr? config { contract := contract, locals := permitStore I } evm (Expr.intLit 0)
      | x => EvalResult.error EvalError.typeError) =
        EvalResult.ok (Value.int (Int.ofNat (permitAllowedCleanWord I).toNat))
    rw [hclean]
    simp only [evalExpr?]
    change EvalResult.ok (Value.int 0) = EvalResult.ok (Value.int 0)
    rfl
  · have hnz : permitAllowedWord I ≠ ⟨0⟩ := by
      intro hbad
      exact hzero (congrArg UInt256.toNat hbad)
    rw [if_neg hzero]
    have hclean : permitAllowedCleanWord I = ⟨1⟩ := by
      unfold permitAllowedCleanWord
      rw [isZero_eq_zero_of_ne hnz]
      decide
    change
      (match Value.bool true with
      | Value.bool true => evalExpr? config { contract := contract, locals := permitStore I } evm (Expr.intLit 1)
      | Value.bool false => evalExpr? config { contract := contract, locals := permitStore I } evm (Expr.intLit 0)
      | x => EvalResult.error EvalError.typeError) =
        EvalResult.ok (Value.int (Int.ofNat (permitAllowedCleanWord I).toNat))
    rw [hclean]
    simp only [evalExpr?]
    change EvalResult.ok (Value.int 1) = EvalResult.ok (Value.int 1)
    rfl

theorem evalExpr_permitDigestStore_holder (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      (.var "holder") = .ok (permitHolderValue I) := by
  rw [evalExpr?]
  unfold permitDigestStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [permitStore_get_holder]
  simp [EvalResult.ofOption]

theorem evalExpr_permitDigestStore_digest (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      (.var "digest") = .ok (.fixedBytes bytes32Width (permitDigestBytes evm I)) := by
  rw [evalExpr?]
  unfold permitDigestStore
  simp [EvalResult.ofOption]

theorem evalExpr_permitDigestStore_v (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      (.var "v") = .ok (permitVValue I) := by
  rw [evalExpr?]
  rw [permitDigestStore_get_v]
  simp [EvalResult.ofOption]

theorem evalExpr_permitDigestStore_r (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      (.var "r") = .ok (permitRValue I) := by
  rw [evalExpr?]
  rw [permitDigestStore_get_r]
  simp [EvalResult.ofOption]

theorem evalExpr_permitDigestStore_s (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      (.var "s") = .ok (permitSValue I) := by
  rw [evalExpr?]
  rw [permitDigestStore_get_s]
  simp [EvalResult.ofOption]

theorem evalExpr_permit_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.storage domainSeparatorRef) =
    .ok (.fixedBytes bytes32Width
      (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        domainSeparatorStorageSlot))) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := permitStore I })
    (slot := domainSeparatorRef)
    (er := ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef))
    (t := .bytes bytes32Width)
    (loc := wordLoc domainSeparatorStorageSlot (.bytes bytes32Width))
    (value := .fixedBytes bytes32Width
      (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        domainSeparatorStorageSlot)))
    (hbase := by simp [domainSeparatorRef, permitStore_get_DOMAIN_SEPARATOR])
    (her := by simp [evalStorageRef, domainSeparatorRef, permitStore_get_DOMAIN_SEPARATOR,
      EvalResult.bind, bind, pure])
    (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (hloc := by rfl)
    (hload := by simpa [wordLoc, bytes32Loc, bytes32Width] using
      storageLocLoad_bytes32 evm domainSeparatorStorageSlot)]

theorem evalExpr_permitStructHash (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm permitStructHashExpr =
      .ok (.fixedBytes bytes32Width (permitStructHashBytes I)) := by
  have hpacked :
      evalPackedArgs? config { contract := contract, locals := permitStore I } evm
        [ (bytes32, permitTypehashExpr),
          (uint256, addressAsUint256 (.var "holder")),
          (uint256, addressAsUint256 (.var "spender")),
          (uint256, .var "nonce"),
          (uint256, .var "expiry"),
          (uint256, .ite (.var "allowed") (.intLit 1) (.intLit 0)) ] =
        .ok (permitTypehashBytes ++
          (EVM.Word.toBytesBE (permitHolderMaskedWord I) ++
            (EVM.Word.toBytesBE (permitSpenderMaskedWord I) ++
              (EVM.Word.toBytesBE (permitNonceWord I) ++
                (EVM.Word.toBytesBE (permitExpiryWord I) ++
                  EVM.Word.toBytesBE (permitAllowedCleanWord I)))))) := by
    refine evalPackedArgs_cons_ok
      (cfg := config) (solm := { contract := contract, locals := permitStore I })
      (evm := evm) (ty := bytes32) (e := permitTypehashExpr)
      (v := .fixedBytes bytes32Width permitTypehashBytes) (head := permitTypehashBytes)
      (tailBytes :=
        EVM.Word.toBytesBE (permitHolderMaskedWord I) ++
          (EVM.Word.toBytesBE (permitSpenderMaskedWord I) ++
            (EVM.Word.toBytesBE (permitNonceWord I) ++
              (EVM.Word.toBytesBE (permitExpiryWord I) ++
                EVM.Word.toBytesBE (permitAllowedCleanWord I)))))
      (rest :=
        [ (uint256, addressAsUint256 (.var "holder")),
          (uint256, addressAsUint256 (.var "spender")),
          (uint256, .var "nonce"),
          (uint256, .var "expiry"),
          (uint256, .ite (.var "allowed") (.intLit 1) (.intLit 0)) ])
      ?_ (encodePacked_bytes32_of_length (by simpa [fixedBytesSize] using permitTypehashBytes_length))
      ?_
    · unfold permitTypehashExpr
      rw [evalExpr?]
      rfl
    · refine evalPackedArgs_cons_ok
        (cfg := config) (solm := { contract := contract, locals := permitStore I })
        (evm := evm) (ty := uint256) (e := addressAsUint256 (.var "holder"))
        (v := .int (Int.ofNat (permitHolderMaskedWord I).toNat))
        (head := EVM.Word.toBytesBE (permitHolderMaskedWord I))
        (tailBytes :=
          EVM.Word.toBytesBE (permitSpenderMaskedWord I) ++
            (EVM.Word.toBytesBE (permitNonceWord I) ++
              (EVM.Word.toBytesBE (permitExpiryWord I) ++
                EVM.Word.toBytesBE (permitAllowedCleanWord I))))
        ?_ ?_ ?_
      · exact evalExpr_permitStore_holder_uint256 evm I
      · exact encodePacked_uint256_word (permitHolderMaskedWord I)
      · refine evalPackedArgs_cons_ok
          (cfg := config) (solm := { contract := contract, locals := permitStore I })
          (evm := evm) (ty := uint256) (e := addressAsUint256 (.var "spender"))
          (v := .int (Int.ofNat (permitSpenderMaskedWord I).toNat))
          (head := EVM.Word.toBytesBE (permitSpenderMaskedWord I))
          (tailBytes :=
            EVM.Word.toBytesBE (permitNonceWord I) ++
              (EVM.Word.toBytesBE (permitExpiryWord I) ++
                EVM.Word.toBytesBE (permitAllowedCleanWord I)))
          ?_ ?_ ?_
        · exact evalExpr_permitStore_spender_uint256 evm I
        · exact encodePacked_uint256_word (permitSpenderMaskedWord I)
        · refine evalPackedArgs_cons_ok
            (cfg := config) (solm := { contract := contract, locals := permitStore I })
            (evm := evm) (ty := uint256) (e := .var "nonce")
            (v := .int (Int.ofNat (permitNonceWord I).toNat))
            (head := EVM.Word.toBytesBE (permitNonceWord I))
            (tailBytes :=
              EVM.Word.toBytesBE (permitExpiryWord I) ++
                EVM.Word.toBytesBE (permitAllowedCleanWord I))
            ?_ ?_ ?_
          · simpa [permitNonceValue] using evalExpr_permitStore_nonce evm I
          · exact encodePacked_uint256_word (permitNonceWord I)
          · refine evalPackedArgs_cons_ok
              (cfg := config) (solm := { contract := contract, locals := permitStore I })
              (evm := evm) (ty := uint256) (e := .var "expiry")
              (v := .int (Int.ofNat (permitExpiryWord I).toNat))
              (head := EVM.Word.toBytesBE (permitExpiryWord I))
              (tailBytes := EVM.Word.toBytesBE (permitAllowedCleanWord I))
              ?_ ?_ ?_
            · simpa [permitExpiryValue] using evalExpr_permitStore_expiry evm I
            · exact encodePacked_uint256_word (permitExpiryWord I)
            · simpa using
                evalPackedArgs_cons_ok
                  (cfg := config) (solm := { contract := contract, locals := permitStore I })
                  (evm := evm) (ty := uint256)
                  (e := .ite (.var "allowed") (.intLit 1) (.intLit 0))
                  (v := .int (Int.ofNat (permitAllowedCleanWord I).toNat))
                  (head := EVM.Word.toBytesBE (permitAllowedCleanWord I))
                  (tailBytes := []) (rest := [])
                  (evalExpr_permitStore_allowed_clean evm I)
                  (encodePacked_uint256_word (permitAllowedCleanWord I))
                  (by rw [evalPackedArgs?]; rfl)
  unfold permitStructHashExpr permitStructHashBytes permitStructPackedByteArray
  rw [evalExpr?]
  rw [evalExpr?]
  rw [hpacked]
  simp [EvalResult.bind, bind, pure, bytes32Width, permitStructPackedByteArray_eq]

theorem evalExpr_permitDigest (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm permitDigestExpr =
      .ok (.fixedBytes bytes32Width (permitDigestBytes evm I)) := by
  have hpacked :
      evalPackedArgs? config { contract := contract, locals := permitStore I } evm
        [ (ABIType.bytes, eip191Prefix),
          (bytes32, .storage domainSeparatorRef),
          (bytes32, permitStructHashExpr) ] =
        .ok ([25, 1] ++
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            domainSeparatorStorageSlot) ++ permitStructHashBytes I)) := by
    refine evalPackedArgs_cons_ok
      (cfg := config) (solm := { contract := contract, locals := permitStore I })
      (evm := evm) (ty := ABIType.bytes) (e := eip191Prefix)
      (v := .bytes ⟨#[25, 1]⟩) (head := [25, 1])
      (tailBytes :=
        EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          domainSeparatorStorageSlot) ++ permitStructHashBytes I)
      (rest := [(bytes32, .storage domainSeparatorRef), (bytes32, permitStructHashExpr)])
      ?_ (by rw [encodePacked_dynamic_bytes, eip191ByteArray_toList]) ?_
    · unfold eip191Prefix
      rw [evalExpr?]
      rfl
    · refine evalPackedArgs_cons_ok
        (cfg := config) (solm := { contract := contract, locals := permitStore I })
        (evm := evm) (ty := bytes32) (e := .storage domainSeparatorRef)
        (v := .fixedBytes bytes32Width
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            domainSeparatorStorageSlot)))
        (head := EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          domainSeparatorStorageSlot))
        (tailBytes := permitStructHashBytes I)
        ?_ ?_ ?_
      · exact evalExpr_permit_domainSeparator evm I
      · exact encodePacked_bytes32_of_length
          (by rw [word_toBytesBE_length_32]; rfl)
      · simpa using
          evalPackedArgs_cons_ok
            (cfg := config) (solm := { contract := contract, locals := permitStore I })
            (evm := evm) (ty := bytes32) (e := permitStructHashExpr)
            (v := .fixedBytes bytes32Width (permitStructHashBytes I))
            (head := permitStructHashBytes I) (tailBytes := []) (rest := [])
            (evalExpr_permitStructHash evm I)
            (encodePacked_bytes32_of_length
              (by simpa [fixedBytesSize] using permitStructHashBytes_length I))
            (by rw [evalPackedArgs?]; rfl)
  unfold permitDigestExpr permitDigestBytes
  rw [evalExpr?]
  rw [evalExpr?]
  rw [hpacked]
  change EvalResult.ok (Value.fixedBytes ⟨31, by decide⟩
      (ffi.KEC
        (ByteArray.mk
          ([25, 1] ++
            (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              domainSeparatorStorageSlot) ++ permitStructHashBytes I)).toArray)).toList) =
    EvalResult.ok (Value.fixedBytes bytes32Width (ffi.KEC (permitDigestPackedByteArray evm I)).toList)
  rw [permitDigestPackedByteArray_eq]
  rfl

theorem evalExpr_ecrecoverCalldata (evm : EVM.State) {I : ExecutionEnv}
    (hsz260 : 260 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      ecrecoverCalldataExpr = .ok (.bytes (permitEcrecoverCalldata evm I)) := by
  have hpacked :
      evalPackedArgs? config { contract := contract, locals := permitDigestStore evm I } evm
        [ (bytes32, .var "digest"),
          (uint256, .var "v"),
          (bytes32, .var "r"),
          (bytes32, .var "s") ] =
        .ok (permitDigestBytes evm I ++
          (EVM.Word.toBytesBE (permitVMaskedWord I) ++
            (permitRBytes I ++ permitSBytes I))) := by
    refine evalPackedArgs_cons_ok
      (cfg := config) (solm := { contract := contract, locals := permitDigestStore evm I })
      (evm := evm) (ty := bytes32) (e := .var "digest")
      (v := .fixedBytes bytes32Width (permitDigestBytes evm I))
      (head := permitDigestBytes evm I)
      (tailBytes :=
        EVM.Word.toBytesBE (permitVMaskedWord I) ++ (permitRBytes I ++ permitSBytes I))
      (rest := [(uint256, .var "v"), (bytes32, .var "r"), (bytes32, .var "s")])
      (evalExpr_permitDigestStore_digest evm I)
      (encodePacked_bytes32_of_length
        (by simpa [fixedBytesSize] using permitDigestBytes_length evm I))
      ?_
    refine evalPackedArgs_cons_ok
      (cfg := config) (solm := { contract := contract, locals := permitDigestStore evm I })
      (evm := evm) (ty := uint256) (e := .var "v")
      (v := permitVValue I)
      (head := EVM.Word.toBytesBE (permitVMaskedWord I))
      (tailBytes := permitRBytes I ++ permitSBytes I)
      (rest := [(bytes32, .var "r"), (bytes32, .var "s")])
      (evalExpr_permitDigestStore_v evm I)
      (encodePacked_uint256_v I)
      ?_
    refine evalPackedArgs_cons_ok
      (cfg := config) (solm := { contract := contract, locals := permitDigestStore evm I })
      (evm := evm) (ty := bytes32) (e := .var "r")
      (v := permitRValue I)
      (head := permitRBytes I)
      (tailBytes := permitSBytes I)
      (rest := [(bytes32, .var "s")])
      (evalExpr_permitDigestStore_r evm I)
      ?_ ?_
    · unfold permitRValue
      exact encodePacked_bytes32_of_length (by rw [permitRBytes_length hsz260]; rfl)
    · simpa using
        evalPackedArgs_cons_ok
          (cfg := config) (solm := { contract := contract, locals := permitDigestStore evm I })
          (evm := evm) (ty := bytes32) (e := .var "s")
          (v := permitSValue I)
          (head := permitSBytes I) (tailBytes := []) (rest := [])
          (evalExpr_permitDigestStore_s evm I)
          (by
            unfold permitSValue
            exact encodePacked_bytes32_of_length
              (by rw [permitSBytes_length hsz260]; rfl))
          (by rw [evalPackedArgs?]; rfl)
  unfold ecrecoverCalldataExpr permitEcrecoverCalldata
  rw [evalExpr?]
  rw [hpacked]
  simp [EvalResult.bind, bind, pure, permitEcrecoverCalldata_eq]

theorem evalExpr_ecrecoverPrecompile (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm ecrecoverPrecompile =
      .ok (.address (AccountAddress.ofNat 1)) := by
  unfold ecrecoverPrecompile addrSt
  simp [evalExpr?, castValue?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem evalExpr_zeroInt (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
      .ok (.int 0) := by
  simp [evalExpr?, pure]

theorem evalExpr_ecrecoverSuccess_false
    (evm : EVM.State) (locals : Store) (out : ByteArray) :
    evalExpr? config
        { contract := contract,
          locals := (locals.insert "ecrecoverSuccess" (.bool false)).insert
            "ecrecoverData" (.bytes out) }
        evm (.var "ecrecoverSuccess") =
      .ok (.bool false) := by
  rw [evalExpr?]
  simp only [EvalResult.ofOption]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem evalExpr_ecrecoverSuccess_true
    (evm : EVM.State) (locals : Store) (out : ByteArray) :
    evalExpr? config
        { contract := contract,
          locals := (locals.insert "ecrecoverSuccess" (.bool true)).insert
            "ecrecoverData" (.bytes out) }
        evm (.var "ecrecoverSuccess") =
      .ok (.bool true) := by
  rw [evalExpr?]
  simp only [EvalResult.ofOption]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem decodeReturnValueWithMode_legacy_addr_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 addr returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0n : ¬ ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [addr].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  unfold addr
  simp only
  rw [decodeScalarWord_legacyAddress_none_short (bytes := returndata.toList) (start := 0)
    htake0n]
  rfl

theorem decodeReturnValueWithMode_legacy_addr_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 addr returndata =
      some (.address (AccountAddress.ofNat
        (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [addr].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  unfold addr
  simp only
  rw [decodeScalarWord_legacyAddress_ok (bytes := returndata.toList) (start := 0) htake0]
  simp [hword, UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

abbrev permitEcrecoverCallStore (evm : EVM.State) (I : ExecutionEnv)
    (success : Bool) (out : ByteArray) : Store :=
  ((permitDigestStore evm I).insert "ecrecoverSuccess" (.bool success)).insert
    "ecrecoverData" (.bytes out)

abbrev permitRecoveredStore (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) : Store :=
  (permitEcrecoverCallStore evm I true out).insert "recovered" (.address recovered)

theorem evalExpr_permitEcrecoverCallStore_data (evm evm' : EVM.State) (I : ExecutionEnv)
    (success : Bool) (out : ByteArray) :
    evalExpr? config
        { contract := contract, locals := permitEcrecoverCallStore evm I success out }
        evm' (.var "ecrecoverData") =
      .ok (.bytes out) := by
  rw [evalExpr?]
  simp [permitEcrecoverCallStore, EvalResult.ofOption]

theorem evalExpr_permitEcrecoverCallStore_recovered_revert
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out = none) :
    evalExpr? config
        { contract := contract, locals := permitEcrecoverCallStore evm I true out }
        evm' (.abiDecode addr (.var "ecrecoverData")) =
      .revert := by
  rw [evalExpr?]
  rw [evalExpr_permitEcrecoverCallStore_data]
  simp [EvalResult.bind, bind, hdec]

theorem evalExpr_permitEcrecoverCallStore_recovered_ok
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hdec :
      ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out =
        some (.address recovered)) :
    evalExpr? config
        { contract := contract, locals := permitEcrecoverCallStore evm I true out }
        evm' (.abiDecode addr (.var "ecrecoverData")) =
      .ok (.address recovered) := by
  rw [evalExpr?]
  rw [evalExpr_permitEcrecoverCallStore_data]
  simp only [EvalResult.bind, bind, hdec]
  change EvalResult.ok (Value.address recovered) = EvalResult.ok (Value.address recovered)
  rfl

theorem evalExpr_permitRecoveredStore_holder (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.var "holder") =
      .ok (permitHolderValue I) := by
  rw [evalExpr?]
  unfold permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  simp only [EvalResult.ofOption]
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem evalExpr_permitRecoveredStore_spender (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.var "spender") =
      .ok (permitSpenderValue I) := by
  rw [evalExpr?]
  unfold permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  simp only [EvalResult.ofOption]
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem evalExpr_permitRecoveredStore_nonce (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.var "nonce") =
      .ok (permitNonceValue I) := by
  rw [evalExpr?]
  unfold permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  simp only [EvalResult.ofOption]
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem evalExpr_permitRecoveredStore_expiry (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.var "expiry") =
      .ok (permitExpiryValue I) := by
  rw [evalExpr?]
  unfold permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  simp only [EvalResult.ofOption]
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem evalExpr_permitRecoveredStore_allowed (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.var "allowed") =
      .ok (permitAllowedValue I) := by
  rw [evalExpr?]
  unfold permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  simp only [EvalResult.ofOption]
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem evalExpr_permitRecoveredStore_recovered (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.var "recovered") =
      .ok (.address recovered) := by
  rw [evalExpr?]
  simp [permitRecoveredStore, EvalResult.ofOption]

theorem permitRecoveredStore_get_nonces (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    (permitRecoveredStore evm I out recovered).get? "nonces" = none := by
  unfold permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact permitStore_get_nonces I

theorem evalExpr_binary_nonshort {cfg solm evm op lhs rhs}
    (hand : op ≠ BinaryOp.and) (hor : op ≠ BinaryOp.or) :
    evalExpr? cfg solm evm (.binary op lhs rhs) =
      (do
        let lhsValue <- evalExpr? cfg solm evm lhs
        let rhsValue <- evalExpr? cfg solm evm rhs
        evalBinaryOp? op lhsValue rhsValue) := by
  cases op <;> simp [evalExpr?] at hand hor ⊢

theorem evalExpr_permitRecoveredStore_holder_eq_recovered_true
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (heq : AccountAddress.ofNat (permitHolderWord I).toNat = recovered) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .eq (.var "holder") (.var "recovered")) =
      .ok (.bool true) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_holder, evalExpr_permitRecoveredStore_recovered]
  simp only [EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq (permitHolderValue I) (.address recovered) = .ok (.bool true)
  have hval : permitHolderValue I = .address recovered := by
    simpa [permitHolderValue] using congrArg Value.address heq
  simp [evalBinaryOp?, hval]

theorem evalExpr_permitRecoveredStore_holder_eq_recovered_false
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hne : AccountAddress.ofNat (permitHolderWord I).toNat ≠ recovered) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .eq (.var "holder") (.var "recovered")) =
      .ok (.bool false) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_holder, evalExpr_permitRecoveredStore_recovered]
  simp only [EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq (permitHolderValue I) (.address recovered) = .ok (.bool false)
  have hval : permitHolderValue I ≠ .address recovered := by
    intro hbad
    exact hne (by simpa [permitHolderValue] using hbad)
  simp [evalBinaryOp?, hval]

theorem evalStorageRef_permitRecoveredStore_nonces (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalStorageRef config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (noncesRef (.var "holder")) =
      .ok (permitNonceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, noncesRef, evalExpr_permitRecoveredStore_holder,
    permitHolderValue, permitHolderKey, permitNonceEvaledRef, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem evalExpr_permitRecoveredStore_nonce_storage
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.storage (noncesRef (.var "holder"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (permitNonceStorageSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := permitRecoveredStore evm I out recovered })
    (slot := noncesRef (.var "holder"))
    (er := permitNonceEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (permitNonceStorageSlot I) (.int uint256Int))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
        (permitNonceStorageSlot I)).toNat))
    (hbase := permitRecoveredStore_get_nonces evm I out recovered)
    (her := evalStorageRef_permitRecoveredStore_nonces evm evm' I out recovered)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
      permitNonceEvaledRef, permitHolderKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm' (permitNonceStorageSlot I))

theorem evalExpr_permitRecoveredStore_nonce_eq_storage_true
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hmatch :
      permitNonceWord I =
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner (permitNonceStorageSlot I)) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .eq (.var "nonce") (.storage (noncesRef (.var "holder")))) =
      .ok (.bool true) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_nonce, evalExpr_permitRecoveredStore_nonce_storage]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, permitNonceValue, hmatch]

theorem evalExpr_permitRecoveredStore_nonce_eq_storage_false
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hne :
      permitNonceWord I ≠
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner (permitNonceStorageSlot I)) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .eq (.var "nonce") (.storage (noncesRef (.var "holder")))) =
      .ok (.bool false) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_nonce, evalExpr_permitRecoveredStore_nonce_storage]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, permitNonceValue]
  intro hbad
  apply hne
  apply u256_inj
  exact_mod_cast hbad

theorem evalExpr_permitRecoveredStore_expiry_eq_zero_true
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress) (hz : permitExpiryWord I = ⟨0⟩) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .eq (.var "expiry") (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_expiry]
  rw [show evalExpr? config
      { contract := contract, locals := permitRecoveredStore evm I out recovered }
      evm' (.intLit 0) = .ok (.int 0) by
    rw [evalExpr?]
    change EvalResult.ok (Value.int 0) = EvalResult.ok (Value.int 0)
    rfl]
  change evalBinaryOp? BinaryOp.eq (permitExpiryValue I) (.int 0) = .ok (.bool true)
  simp [evalBinaryOp?, permitExpiryValue, hz]

theorem evalExpr_permitRecoveredStore_expiry_eq_zero_false
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress) (hnz : permitExpiryWord I ≠ ⟨0⟩) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .eq (.var "expiry") (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_expiry]
  rw [show evalExpr? config
      { contract := contract, locals := permitRecoveredStore evm I out recovered }
      evm' (.intLit 0) = .ok (.int 0) by
    rw [evalExpr?]
    change EvalResult.ok (Value.int 0) = EvalResult.ok (Value.int 0)
    rfl]
  have hnzNat : ¬(permitExpiryWord I).toNat = 0 := by
    intro hzero
    exact hnz (uint256_toNat_eq_zero hzero)
  change evalBinaryOp? BinaryOp.eq (permitExpiryValue I) (.int 0) = .ok (.bool false)
  simp [evalBinaryOp?, permitExpiryValue, hnzNat]

theorem evalExpr_permitRecoveredStore_timestamp_le_expiry_true
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hle :
      (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat ≤ (permitExpiryWord I).toNat) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .le (.env .timestamp) (.var "expiry")) =
      .ok (.bool true) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_expiry]
  rw [show evalExpr? config
      { contract := contract, locals := permitRecoveredStore evm I out recovered }
      evm' (.env .timestamp) =
        .ok (.int (Int.ofNat (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat)) by
    rw [evalExpr?]
    change EvalResult.ok (envValue evm' .timestamp) =
      EvalResult.ok (.int (Int.ofNat (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat))
    simp [envValue]]
  change evalBinaryOp? BinaryOp.le
    (.int (Int.ofNat (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat))
    (permitExpiryValue I) = .ok (.bool true)
  simp [evalBinaryOp?, permitExpiryValue, hle]

theorem evalExpr_permitRecoveredStore_timestamp_le_expiry_false
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hlt : (permitExpiryWord I).toNat < (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (.binary .le (.env .timestamp) (.var "expiry")) =
      .ok (.bool false) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_expiry]
  rw [show evalExpr? config
      { contract := contract, locals := permitRecoveredStore evm I out recovered }
      evm' (.env .timestamp) =
        .ok (.int (Int.ofNat (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat)) by
    rw [evalExpr?]
    change EvalResult.ok (envValue evm' .timestamp) =
      EvalResult.ok (.int (Int.ofNat (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat))
    simp [envValue]]
  change evalBinaryOp? BinaryOp.le
    (.int (Int.ofNat (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat))
    (permitExpiryValue I) = .ok (.bool false)
  simp [evalBinaryOp?, permitExpiryValue]
  omega

theorem evalExpr_permitRecoveredStore_expiry_ok
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hok :
      permitExpiryWord I = ⟨0⟩ ∨
        (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat ≤ (permitExpiryWord I).toNat) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm'
        (.binary .or
          (.binary .eq (.var "expiry") (.intLit 0))
          (.binary .le (.env .timestamp) (.var "expiry"))) =
      .ok (.bool true) := by
  rw [evalExpr?]
  cases hok with
  | inl hz =>
      rw [evalExpr_permitRecoveredStore_expiry_eq_zero_true evm evm' I out recovered hz]
      by_cases hle :
          (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat ≤ (permitExpiryWord I).toNat
      · rw [evalExpr_permitRecoveredStore_timestamp_le_expiry_true evm evm' I out recovered hle]
        rfl
      · rw [evalExpr_permitRecoveredStore_timestamp_le_expiry_false evm evm' I out recovered
          (by omega)]
        rfl
  | inr hle =>
      by_cases hz : permitExpiryWord I = ⟨0⟩
      · rw [evalExpr_permitRecoveredStore_expiry_eq_zero_true evm evm' I out recovered hz]
        rw [evalExpr_permitRecoveredStore_timestamp_le_expiry_true evm evm' I out recovered hle]
        rfl
      · rw [evalExpr_permitRecoveredStore_expiry_eq_zero_false evm evm' I out recovered hz]
        rw [evalExpr_permitRecoveredStore_timestamp_le_expiry_true evm evm' I out recovered hle]
        rfl

theorem evalExpr_permitRecoveredStore_expiry_false
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hnz : permitExpiryWord I ≠ ⟨0⟩)
    (hlt : (permitExpiryWord I).toNat < (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm'
        (.binary .or
          (.binary .eq (.var "expiry") (.intLit 0))
          (.binary .le (.env .timestamp) (.var "expiry"))) =
      .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_permitRecoveredStore_expiry_eq_zero_false evm evm' I out recovered hnz]
  rw [evalExpr_permitRecoveredStore_timestamp_le_expiry_false evm evm' I out recovered hlt]
  rfl

theorem evalExpr_permitRecoveredStore_nonce_increment
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress)
    (hmatch :
      permitNonceWord I =
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner (permitNonceStorageSlot I)) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' (uncheckedAdd256 (.storage (noncesRef (.var "holder"))) (.intLit 1)) =
      .ok (.int (Int.ofNat (permitNonceWord I).toNat + 1)) := by
  rw [uncheckedAdd256]
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  rw [evalExpr_permitRecoveredStore_nonce_storage]
  rw [show evalExpr? config
      { contract := contract, locals := permitRecoveredStore evm I out recovered }
      evm' (.intLit 1) = .ok (.int 1) by
    rw [evalExpr?]
    change EvalResult.ok (Value.int 1) = EvalResult.ok (Value.int 1)
    rfl]
  change evalBinaryOp? BinaryOp.add
      (.int (Int.ofNat
        (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (permitNonceStorageSlot I)).toNat))
      (.int 1) =
    .ok (.int (Int.ofNat (permitNonceWord I).toNat + 1))
  simp [evalBinaryOp?, hmatch]

theorem storageLocStore_uint256_ofNat (evm : EVM.State) (slot : UInt256) (n : Nat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat n)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (EVM.word (Int.ofNat n).toNat)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  rw [wordOfInt_nonneg]
  · have hslen := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.word (Int.ofNat n).toNat)).2
    congr 2
    apply u256_inj
    show fromBytes'
        (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
          ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
        (EVM.word (Int.ofNat n).toNat).toNat
    rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
      List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
      List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]
  · simp

theorem permitAssignNonce (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress)
    (hmatch :
      permitNonceWord I =
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner (permitNonceStorageSlot I)) :
    assignStorageRef? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm' .storage (noncesRef (.var "holder"))
        (.int (Int.ofNat (permitNonceWord I).toNat + 1)) =
      .ok ({ contract := contract, locals := permitRecoveredStore evm I out recovered },
        permitPostNonceState evm' I) := by
  have hbase :
      (permitRecoveredStore evm I out recovered).get? "nonces" = none :=
    permitRecoveredStore_get_nonces evm I out recovered
  have her :
      evalStorageRef config
          { contract := contract, locals := permitRecoveredStore evm I out recovered }
          evm' (noncesRef (.var "holder")) =
        .ok (permitNonceEvaledRef I) :=
    evalStorageRef_permitRecoveredStore_nonces evm evm' I out recovered
  have hty :
      storageTypeAt? contract.storage (permitNonceEvaledRef I) = some uint256St := by
    simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
      permitNonceEvaledRef, permitHolderKey, uint256St]
  have hloc :
      config.storage.layout (permitNonceEvaledRef I) =
        fun _ => some (wordLoc (permitNonceStorageSlot I) (.int uint256Int)) := by
    rfl
  have hstore :
      storageLocStore evm' (wordLoc (permitNonceStorageSlot I) (.int uint256Int))
          (.int (Int.ofNat (permitNonceWord I).toNat + 1)) =
        some (permitPostNonceState evm' I) := by
    rw [show wordLoc (permitNonceStorageSlot I) (ElemType.int uint256Int) =
      uint256Loc (permitNonceStorageSlot I) by rfl]
    rw [show Int.ofNat (permitNonceWord I).toNat + 1 =
        Int.ofNat ((permitNonceWord I).toNat + 1) by
          exact Eq.symm (Int.natCast_add (permitNonceWord I).toNat 1)]
    rw [storageLocStore_uint256_ofNat]
    rw [show (Int.ofNat ((permitNonceWord I).toNat + 1)).toNat =
        (permitNonceWord I).toNat + 1 by simp]
    have hword : EVM.word ((permitNonceWord I).toNat + 1) =
        UInt256.add (permitNonceWord I) ⟨1⟩ := by
      rw [show UInt256.add (permitNonceWord I) ⟨1⟩ =
        EVM.word ((permitNonceWord I).toNat + 1) by
          rw [← u256_ofNat_toNat (permitNonceWord I)]
          rfl]
    unfold permitPostNonceState
    rw [← hmatch, hword]
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := permitRecoveredStore evm I out recovered })
    (evm := evm') (evm' := permitPostNonceState evm' I)
    (slot := noncesRef (.var "holder")) (er := permitNonceEvaledRef I)
    (ty := uint256St) (loc := wordLoc (permitNonceStorageSlot I) (.int uint256Int))
    hbase her hty hloc hstore

theorem evalExpr_permitRecoveredStore_wad
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitRecoveredStore evm I out recovered }
        evm'
        (.ite (.var "allowed") (.intLit maxUint256) (.intLit 0)) =
      .ok (.int (Int.ofNat (permitWadWord I).toNat)) := by
  rw [evalExpr?]
  rw [evalExpr_permitRecoveredStore_allowed]
  simp only [EvalResult.bind, bind]
  unfold permitAllowedValue permitWadWord
  by_cases hzero : (permitAllowedWord I).toNat = 0
  · rw [if_pos hzero, if_pos hzero]
    simp only [evalExpr?]
    rfl
  · rw [if_neg hzero, if_neg hzero]
    simp only [evalExpr?]
    native_decide

abbrev permitWadStore (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) : Store :=
  (permitRecoveredStore evm I out recovered).insert "wad"
    (.int (Int.ofNat (permitWadWord I).toNat))

theorem permitRecoveredStore_get_allowance (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    (permitRecoveredStore evm I out recovered).get? "allowance" = none := by
  unfold permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact permitStore_get_allowance I

theorem permitWadStore_get_allowance (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    (permitWadStore evm I out recovered).get? "allowance" = none := by
  unfold permitWadStore
  rw [store_get_ne _ _ (by native_decide)]
  exact permitRecoveredStore_get_allowance evm I out recovered

theorem evalExpr_permitWadStore_wad
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitWadStore evm I out recovered }
        evm' (.var "wad") =
      .ok (.int (Int.ofNat (permitWadWord I).toNat)) := by
  rw [evalExpr?]
  unfold permitWadStore
  simp only [EvalResult.ofOption]
  rw [store_get_self]

theorem evalExpr_permitWadStore_holder
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitWadStore evm I out recovered }
        evm' (.var "holder") =
      .ok (permitHolderValue I) := by
  rw [evalExpr?]
  unfold permitWadStore permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  simp only [EvalResult.ofOption]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [permitStore_get_holder]

theorem evalExpr_permitWadStore_spender
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (recovered : AccountAddress) :
    evalExpr? config
        { contract := contract, locals := permitWadStore evm I out recovered }
        evm' (.var "spender") =
      .ok (permitSpenderValue I) := by
  rw [evalExpr?]
  unfold permitWadStore permitRecoveredStore permitEcrecoverCallStore permitDigestStore
  simp only [EvalResult.ofOption]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [permitStore_get_spender]

theorem evalStorageRef_permitWadStore_allowance (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    evalStorageRef config
        { contract := contract, locals := permitWadStore evm I out recovered }
        evm' (allowanceRef (.var "holder") (.var "spender")) =
      .ok (permitAllowanceEvaledRef I) := by
  have hholder :
      evalExpr? config { contract := contract, locals := permitWadStore evm I out recovered }
        evm' (.var "holder") = .ok (permitHolderValue I) :=
    evalExpr_permitWadStore_holder evm evm' I out recovered
  have hspender :
      evalExpr? config { contract := contract, locals := permitWadStore evm I out recovered }
        evm' (.var "spender") = .ok (permitSpenderValue I) :=
    evalExpr_permitWadStore_spender evm evm' I out recovered
  rw [evalStorageRef]
  simp only [allowanceRef, evalStorageRefSteps, evalStorageRefStep, hholder, hspender,
    EvalResult.bind, bind, EvalResult.ofOption, pure]
  simp only [permitHolderValue, permitSpenderValue, permitHolderKey, permitSpenderKey,
    permitAllowanceEvaledRef, valueToKey?]

theorem permitAssignAllowance (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress) :
    assignStorageRef? config
        { contract := contract, locals := permitWadStore evm I out recovered }
        (permitPostNonceState evm' I) .storage (allowanceRef (.var "holder") (.var "spender"))
        (.int (Int.ofNat (permitWadWord I).toNat)) =
      .ok ({ contract := contract, locals := permitWadStore evm I out recovered },
        permitPostState evm' I) := by
  have hbase :
      (permitWadStore evm I out recovered).get? "allowance" = none :=
    permitWadStore_get_allowance evm I out recovered
  have her :
      evalStorageRef config
          { contract := contract, locals := permitWadStore evm I out recovered }
          (permitPostNonceState evm' I) (allowanceRef (.var "holder") (.var "spender")) =
        .ok (permitAllowanceEvaledRef I) :=
    evalStorageRef_permitWadStore_allowance evm (permitPostNonceState evm' I) I out recovered
  have hty :
      storageTypeAt? contract.storage (permitAllowanceEvaledRef I) = some uint256St := by
    simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
      permitAllowanceEvaledRef, permitHolderKey, permitSpenderKey, uint256St]
  have hloc :
      config.storage.layout (permitAllowanceEvaledRef I) =
        fun _ => some (wordLoc (permitAllowanceStorageSlot I) (.int uint256Int)) := by
    rfl
  have hstore :
      storageLocStore (permitPostNonceState evm' I)
          (wordLoc (permitAllowanceStorageSlot I) (.int uint256Int))
          (.int (Int.ofNat (permitWadWord I).toNat)) =
        some (permitPostState evm' I) := by
    rw [show wordLoc (permitAllowanceStorageSlot I) (ElemType.int uint256Int) =
      uint256Loc (permitAllowanceStorageSlot I) by rfl]
    rw [storageLocStore_uint256]
    unfold permitPostState
    rw [show (permitPostNonceState evm' I).executionEnv.codeOwner =
        evm'.executionEnv.codeOwner by
      unfold permitPostNonceState
      rw [storageStore_executionEnv]]
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := permitWadStore evm I out recovered })
    (evm := permitPostNonceState evm' I) (evm' := permitPostState evm' I)
    (slot := allowanceRef (.var "holder") (.var "spender"))
    (er := permitAllowanceEvaledRef I) (ty := uint256St)
    (loc := wordLoc (permitAllowanceStorageSlot I) (.int uint256Int))
    hbase her hty hloc hstore

theorem permitHolderMaskedWord_eq_zero_of_address_zero (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (permitHolderWord I).toNat = AccountAddress.ofNat 0) :
    permitHolderMaskedWord I = ⟨0⟩ := by
  have hmask := keyValueToWord_address_ofNat_mask (permitHolderWord I)
  rw [heq] at hmask
  simpa [permitHolderMaskedWord, keyValueToWord_address] using hmask.symm

theorem permitHolderAddress_eq_zero_of_masked_zero (I : ExecutionEnv)
    (heq : permitHolderMaskedWord I = ⟨0⟩) :
    AccountAddress.ofNat (permitHolderWord I).toNat = AccountAddress.ofNat 0 := by
  have hmaskAddr :
      AccountAddress.ofNat (permitHolderWord I).toNat =
        AccountAddress.ofNat (UInt256.land (permitHolderWord I) solcAddrMask).toNat := by
    apply Fin.ext
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    rw [uland_toNat]
    change (permitHolderWord I).val.val % AccountAddress.size =
      Nat.land (permitHolderWord I).val.val solcAddrMask.toNat % AccountAddress.size
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_mask_eq_mod]
    rw [show AccountAddress.size = 2 ^ 160 by rfl]
    rw [Nat.mod_mod]
  have hmasked :
      AccountAddress.ofNat (UInt256.land (permitHolderWord I) solcAddrMask).toNat =
        AccountAddress.ofNat 0 := by
    have hword : UInt256.land (permitHolderWord I) solcAddrMask = ⟨0⟩ := by
      rw [u256_land_comm]
      exact heq
    rw [hword]
    simp [UInt256.toNat]
  exact hmaskAddr.trans hmasked

theorem evalExpr_permit_holder_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.binary .ne (.var "holder") zeroAddr) = .ok (.bool true) := by
  have haddrNe : AccountAddress.ofNat (permitHolderWord I).toNat ≠ AccountAddress.ofNat 0 := by
    intro hbad
    exact hnz (permitHolderMaskedWord_eq_zero_of_address_zero I hbad)
  have hlhs := evalExpr_permitStore_holder evm I
  have hrhs := evalExpr_zeroAddr evm (permitStore I)
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [hlhs, hrhs, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.ne (permitHolderValue I)
      (.address (AccountAddress.ofNat 0)) = .ok (.bool true)
  have hvalNe : permitHolderValue I ≠ .address (AccountAddress.ofNat 0) := by
    intro hbad
    exact haddrNe (by simpa [permitHolderValue] using hbad)
  simp [evalBinaryOp?, hvalNe]

theorem evalExpr_permit_holder_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hz : permitHolderMaskedWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.binary .ne (.var "holder") zeroAddr) = .ok (.bool false) := by
  have haddr := permitHolderAddress_eq_zero_of_masked_zero I hz
  have hlhs := evalExpr_permitStore_holder evm I
  have hrhs := evalExpr_zeroAddr evm (permitStore I)
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [hlhs, hrhs, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.ne (permitHolderValue I)
      (.address (AccountAddress.ofNat 0)) = .ok (.bool false)
  have hvalEq : permitHolderValue I = .address (AccountAddress.ofNat 0) := by
    simpa [permitHolderValue] using haddr
  simp [evalBinaryOp?, hvalEq]

theorem evalExpr_permitDigestStore_holder_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      (.binary .ne (.var "holder") zeroAddr) = .ok (.bool true) := by
  have haddrNe : AccountAddress.ofNat (permitHolderWord I).toNat ≠ AccountAddress.ofNat 0 := by
    intro hbad
    exact hnz (permitHolderMaskedWord_eq_zero_of_address_zero I hbad)
  have hlhs := evalExpr_permitDigestStore_holder evm I
  have hrhs := evalExpr_zeroAddr evm (permitDigestStore evm I)
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [hlhs, hrhs, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.ne (permitHolderValue I)
      (.address (AccountAddress.ofNat 0)) = .ok (.bool true)
  have hvalNe : permitHolderValue I ≠ .address (AccountAddress.ofNat 0) := by
    intro hbad
    exact haddrNe (by simpa [permitHolderValue] using hbad)
  simp [evalBinaryOp?, hvalNe]

theorem evalExpr_permitDigestStore_holder_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hz : permitHolderMaskedWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := permitDigestStore evm I } evm
      (.binary .ne (.var "holder") zeroAddr) = .ok (.bool false) := by
  have haddr := permitHolderAddress_eq_zero_of_masked_zero I hz
  have hlhs := evalExpr_permitDigestStore_holder evm I
  have hrhs := evalExpr_zeroAddr evm (permitDigestStore evm I)
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [hlhs, hrhs, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.ne (permitHolderValue I)
      (.address (AccountAddress.ofNat 0)) = .ok (.bool false)
  have hvalEq : permitHolderValue I = .address (AccountAddress.ofNat 0) := by
    simpa [permitHolderValue] using haddr
  simp [evalBinaryOp?, hvalEq]

/-- The Solm `permit(...)` body reverts at the holder nonzero guard. -/
theorem daiPermitBodyReverts_holderZero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hz : permitHolderMaskedWord I = ⟨0⟩) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <| by
    simpa [permitTransition, nonpayable, permitDigestStore] using
      ((ABlock.start
        |>.requireStep (evalCallvalueEq_true hwv)
        |>.letStep (evalExpr_permitDigest evm I))
        |>.requireRevert (evalExpr_permitDigestStore_holder_ne_zero_false evm I hz))

/-- The Solm `permit(...)` body reverts when the `ecrecover` staticcall reports failure. -/
theorem daiPermitBodyReverts_ecrecoverFailed (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hsz260 : 260 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩)
    (hcall : callViaEVM evm (EVM.address (AccountAddress.ofNat 1)) 0
      (permitEcrecoverCalldata evm I) (false, evm', out) false) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [permitTransition, nonpayable] using
    (((ABlock.start
      |>.requireStep (evalCallvalueEq_true hwv)
      |>.letStep (evalExpr_permitDigest evm I))
      |>.requireStep (evalExpr_permitDigestStore_holder_ne_zero_true evm I hnz)).run <|
        ExecBlock.consNormal
          (ExecStmt.lowLevelCallFailure
            (evalExpr_ecrecoverPrecompile evm (permitDigestStore evm I))
            (evalExpr_zeroInt evm (permitDigestStore evm I))
            (evalExpr_ecrecoverCalldata evm hsz260)
            hcall)
          (ExecBlock.consRevert
            (ExecStmt.requireFalse
              (evalExpr_ecrecoverSuccess_false evm'
                (permitDigestStore evm I) out))))

/-- The Solm `permit(...)` body reverts when successful `ecrecover` returns undecodable data. -/
theorem daiPermitBodyReverts_recoveredDecode (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hsz260 : 260 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩)
    (hcall : callViaEVM evm (EVM.address (AccountAddress.ofNat 1)) 0
      (permitEcrecoverCalldata evm I) (true, evm', out) false)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out = none) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [permitTransition, nonpayable, permitEcrecoverCallStore] using
    (((ABlock.start
      |>.requireStep (evalCallvalueEq_true hwv)
      |>.letStep (evalExpr_permitDigest evm I))
      |>.requireStep (evalExpr_permitDigestStore_holder_ne_zero_true evm I hnz)).run <|
        ExecBlock.consNormal
          (ExecStmt.lowLevelCallSuccess
            (evalExpr_ecrecoverPrecompile evm (permitDigestStore evm I))
            (evalExpr_zeroInt evm (permitDigestStore evm I))
            (evalExpr_ecrecoverCalldata evm hsz260)
            hcall)
          (ExecBlock.consNormal
            (ExecStmt.requireTrue
              (evalExpr_ecrecoverSuccess_true evm'
                (permitDigestStore evm I) out))
            (ExecBlock.consRevert
              (ExecStmt.letDeclRevert
                (evalExpr_permitEcrecoverCallStore_recovered_revert
                  evm evm' I out hdec)))))

/-- The Solm `permit(...)` body reverts when `ecrecover` recovers a non-holder address. -/
theorem daiPermitBodyReverts_badRecovered (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress)
    (hsz260 : 260 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩)
    (hcall : callViaEVM evm (EVM.address (AccountAddress.ofNat 1)) 0
      (permitEcrecoverCalldata evm I) (true, evm', out) false)
    (hdec :
      ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out =
        some (.address recovered))
    (hne : AccountAddress.ofNat (permitHolderWord I).toNat ≠ recovered) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [permitTransition, nonpayable, permitEcrecoverCallStore, permitRecoveredStore] using
    ((((ABlock.start
      |>.requireStep (evalCallvalueEq_true hwv)
      |>.letStep (evalExpr_permitDigest evm I))
      |>.requireStep (evalExpr_permitDigestStore_holder_ne_zero_true evm I hnz)).run <|
        ExecBlock.consNormal
          (ExecStmt.lowLevelCallSuccess
            (evalExpr_ecrecoverPrecompile evm (permitDigestStore evm I))
            (evalExpr_zeroInt evm (permitDigestStore evm I))
            (evalExpr_ecrecoverCalldata evm hsz260)
            hcall)
          (ExecBlock.consNormal
            (ExecStmt.requireTrue
              (evalExpr_ecrecoverSuccess_true evm'
                (permitDigestStore evm I) out))
            (ExecBlock.consNormal
              (ExecStmt.letDecl
                (evalExpr_permitEcrecoverCallStore_recovered_ok
                  evm evm' I out recovered hdec))
              (ExecBlock.consRevert
                (ExecStmt.requireFalse
                  (evalExpr_permitRecoveredStore_holder_eq_recovered_false
                    evm evm' I out recovered hne)))))))

/-- The Solm `permit(...)` body reverts when the signature is expired. -/
theorem daiPermitBodyReverts_expired (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress)
    (hsz260 : 260 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩)
    (hcall : callViaEVM evm (EVM.address (AccountAddress.ofNat 1)) 0
      (permitEcrecoverCalldata evm I) (true, evm', out) false)
    (hdec :
      ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out =
        some (.address recovered))
    (heq : AccountAddress.ofNat (permitHolderWord I).toNat = recovered)
    (hexpiryNonzero : permitExpiryWord I ≠ ⟨0⟩)
    (hexpired :
      (permitExpiryWord I).toNat < (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [permitTransition, nonpayable, permitEcrecoverCallStore, permitRecoveredStore] using
    ((((ABlock.start
      |>.requireStep (evalCallvalueEq_true hwv)
      |>.letStep (evalExpr_permitDigest evm I))
      |>.requireStep (evalExpr_permitDigestStore_holder_ne_zero_true evm I hnz)).run <|
        ExecBlock.consNormal
          (ExecStmt.lowLevelCallSuccess
            (evalExpr_ecrecoverPrecompile evm (permitDigestStore evm I))
            (evalExpr_zeroInt evm (permitDigestStore evm I))
            (evalExpr_ecrecoverCalldata evm hsz260)
            hcall)
          (ExecBlock.consNormal
            (ExecStmt.requireTrue
              (evalExpr_ecrecoverSuccess_true evm'
                (permitDigestStore evm I) out))
            (ExecBlock.consNormal
              (ExecStmt.letDecl
                (evalExpr_permitEcrecoverCallStore_recovered_ok
                  evm evm' I out recovered hdec))
              (ExecBlock.consNormal
                (ExecStmt.requireTrue
                  (evalExpr_permitRecoveredStore_holder_eq_recovered_true
                    evm evm' I out recovered heq))
                (ExecBlock.consRevert
                  (ExecStmt.requireFalse
                    (evalExpr_permitRecoveredStore_expiry_false evm evm' I out recovered
                      hexpiryNonzero hexpired))))))))

/-- The Solm `permit(...)` body reverts when calldata nonce mismatches storage. -/
theorem daiPermitBodyReverts_nonceMismatch (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress)
    (hsz260 : 260 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩)
    (hcall : callViaEVM evm (EVM.address (AccountAddress.ofNat 1)) 0
      (permitEcrecoverCalldata evm I) (true, evm', out) false)
    (hdec :
      ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out =
        some (.address recovered))
    (heq : AccountAddress.ofNat (permitHolderWord I).toNat = recovered)
    (hexpiryOk :
      permitExpiryWord I = ⟨0⟩ ∨
        (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat ≤ (permitExpiryWord I).toNat)
    (hnonce :
      permitNonceWord I ≠
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner (permitNonceStorageSlot I)) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [permitTransition, nonpayable, permitEcrecoverCallStore, permitRecoveredStore] using
    ((((ABlock.start
      |>.requireStep (evalCallvalueEq_true hwv)
      |>.letStep (evalExpr_permitDigest evm I))
      |>.requireStep (evalExpr_permitDigestStore_holder_ne_zero_true evm I hnz)).run <|
        ExecBlock.consNormal
          (ExecStmt.lowLevelCallSuccess
            (evalExpr_ecrecoverPrecompile evm (permitDigestStore evm I))
            (evalExpr_zeroInt evm (permitDigestStore evm I))
            (evalExpr_ecrecoverCalldata evm hsz260)
            hcall)
          (ExecBlock.consNormal
            (ExecStmt.requireTrue
              (evalExpr_ecrecoverSuccess_true evm'
                (permitDigestStore evm I) out))
            (ExecBlock.consNormal
              (ExecStmt.letDecl
                (evalExpr_permitEcrecoverCallStore_recovered_ok
                  evm evm' I out recovered hdec))
              (ExecBlock.consNormal
                (ExecStmt.requireTrue
                  (evalExpr_permitRecoveredStore_holder_eq_recovered_true
                    evm evm' I out recovered heq))
                (ExecBlock.consNormal
                  (ExecStmt.requireTrue
                    (evalExpr_permitRecoveredStore_expiry_ok
                      evm evm' I out recovered hexpiryOk))
                  (ExecBlock.consRevert
                    (ExecStmt.requireFalse
                      (evalExpr_permitRecoveredStore_nonce_eq_storage_false
                        evm evm' I out recovered hnonce)))))))))

set_option maxHeartbeats 10000000
/-- The Solm `permit(...)` body updates nonce and allowance after successful recovery. -/
theorem daiPermitBodyReturns_success (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (recovered : AccountAddress)
    (hsz260 : 260 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩)
    (hcall : callViaEVM evm (EVM.address (AccountAddress.ofNat 1)) 0
      (permitEcrecoverCalldata evm I) (true, evm', out) false)
    (hdec :
      ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out =
        some (.address recovered))
    (heq : AccountAddress.ofNat (permitHolderWord I).toNat = recovered)
    (hexpiryOk :
      permitExpiryWord I = ⟨0⟩ ∨
        (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat ≤ (permitExpiryWord I).toNat)
    (hnonce :
      permitNonceWord I =
        Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner (permitNonceStorageSlot I)) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body
      (.returned { contract := contract, locals := permitWadStore evm I out recovered }
        (permitPostState evm' I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [permitTransition, nonpayable, permitEcrecoverCallStore, permitRecoveredStore,
    permitWadStore] using
    ((((ABlock.start
      |>.requireStep (evalCallvalueEq_true hwv)
      |>.letStep (evalExpr_permitDigest evm I))
      |>.requireStep (evalExpr_permitDigestStore_holder_ne_zero_true evm I hnz)).run <|
        ExecBlock.consNormal
          (ExecStmt.lowLevelCallSuccess
            (evalExpr_ecrecoverPrecompile evm (permitDigestStore evm I))
            (evalExpr_zeroInt evm (permitDigestStore evm I))
            (evalExpr_ecrecoverCalldata evm hsz260)
            hcall)
          (ExecBlock.consNormal
            (ExecStmt.requireTrue
              (evalExpr_ecrecoverSuccess_true evm'
                (permitDigestStore evm I) out))
            (ExecBlock.consNormal
              (ExecStmt.letDecl
                (evalExpr_permitEcrecoverCallStore_recovered_ok
                  evm evm' I out recovered hdec))
              (ExecBlock.consNormal
                (ExecStmt.requireTrue
                  (evalExpr_permitRecoveredStore_holder_eq_recovered_true
                    evm evm' I out recovered heq))
                (ExecBlock.consNormal
                  (ExecStmt.requireTrue
                    (evalExpr_permitRecoveredStore_expiry_ok
                      evm evm' I out recovered hexpiryOk))
                  (ExecBlock.consNormal
                    (ExecStmt.requireTrue
                      (evalExpr_permitRecoveredStore_nonce_eq_storage_true
                        evm evm' I out recovered hnonce))
                    (ExecBlock.consNormal
                      (ExecStmt.assign
                        (evalExpr_permitRecoveredStore_nonce_increment
                          evm evm' I out recovered hnonce)
                        (permitAssignNonce evm evm' I out recovered hnonce))
                      (ExecBlock.consNormal
                        (ExecStmt.letDecl
                          (evalExpr_permitRecoveredStore_wad
                            evm (permitPostNonceState evm' I) I out recovered))
                        (ExecBlock.consNormal
                          (ExecStmt.assign
                            (evalExpr_permitWadStore_wad
                              evm (permitPostNonceState evm' I) I out recovered)
                            (permitAssignAllowance evm evm' I out recovered))
                          ExecBlock.nil))))))))))

theorem decodeScalarWordWithMode_legacy_uint8_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 (ABIType.elem (ElemType.int uint8Int))
        bytes start =
      some (.int (Int.ofNat ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat %
        EVM.twoPow 8)), start + 32) := by
  simp only [uint8Int, decodeScalarWordWithMode?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_pos hlen]
  rfl

theorem decodeABIValue_legacy_bytes32_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? (ABIType.elem (ElemType.bytes bytes32Width)) bytes start
        DecodeMode.legacySolc05 =
      some (.fixedBytes bytes32Width ((bytes.drop start).take 32), start + 32) := by
  simp only [bytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
  rw [if_pos hlen]
  have htake : List.take 32 ((bytes.drop start).take 32) = (bytes.drop start).take 32 :=
    List.take_of_length_le (by rw [hlen])
  simp [htake]

theorem decodeABIValues_permit_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hlen160 : ((bytes.drop 160).take 32).length = 32)
    (hlen192 : ((bytes.drop 192).take 32).length = 32)
    (hlen224 : ((bytes.drop 224).take 32).length = 32) :
    decodeABIValues?
        [abiAddress, abiAddress, abiUInt256, abiUInt256, abiBool,
          ABIType.elem (ElemType.int uint8Int), ABIType.elem (ElemType.bytes bytes32Width),
          ABIType.elem (ElemType.bytes bytes32Width)]
        bytes 0 0 256 256 DecodeMode.legacySolc05 =
      some
        ([.address (AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
          .address (AccountAddress.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
          .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
          .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
          if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat = 0 then .bool false
          else .bool true,
          .int (Int.ofNat ((ABI.bytesToWord ((bytes.drop 160).take 32)).toNat %
            EVM.twoPow 8)),
          .fixedBytes bytes32Width ((bytes.drop 192).take 32),
          .fixedBytes bytes32Width ((bytes.drop 224).take 32)], 256) := by
  have haddr0s := decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 0)
    (by simpa using hlen0)
  have haddr32s := decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 32)
    hlen32
  have huint64s := decodeScalarWordWithMode_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := bytes) (start := 64) hlen64
  have huint96s := decodeScalarWordWithMode_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := bytes) (start := 96) hlen96
  have huint8s := decodeScalarWordWithMode_legacy_uint8_ok (bytes := bytes) (start := 160)
    hlen160
  have haddr0 : decodeABIValue? abiAddress bytes 0 DecodeMode.legacySolc05 =
      some (.address (AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat), 32) := by
    rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
      (ty := abiAddress) (bytes := bytes) (start := 0) (by decide)]
    simpa using haddr0s
  have haddr32 : decodeABIValue? abiAddress bytes 32 DecodeMode.legacySolc05 =
      some (.address (AccountAddress.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        64) := by
    rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
      (ty := abiAddress) (bytes := bytes) (start := 32) (by decide)]
    simpa using haddr32s
  have huint64 : decodeABIValue? abiUInt256 bytes 64 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat), 96) := by
    rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
      (ty := abiUInt256) (bytes := bytes) (start := 64) (by decide)]
    simpa using huint64s
  have huint96 : decodeABIValue? abiUInt256 bytes 96 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat), 128) := by
    rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
      (ty := abiUInt256) (bytes := bytes) (start := 96) (by decide)]
    simpa using huint96s
  have huint8 :
      decodeABIValue? (ABIType.elem (ElemType.int uint8Int)) bytes 160
          DecodeMode.legacySolc05 =
        some (.int (Int.ofNat ((ABI.bytesToWord ((bytes.drop 160).take 32)).toNat %
          EVM.twoPow 8)), 192) := by
    rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
      (ty := ABIType.elem (ElemType.int uint8Int)) (bytes := bytes) (start := 160)
      (by decide)]
    simpa using huint8s
  have hbytes192 := decodeABIValue_legacy_bytes32_ok (bytes := bytes) (start := 192)
    hlen192
  have hbytes224 := decodeABIValue_legacy_bytes32_ok (bytes := bytes) (start := 224)
    hlen224
  by_cases hzero : (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat = 0
  · have hbools := decodeScalarWordWithMode_legacy_bool_false (bytes := bytes) (start := 128)
      hlen128 (uint256_toNat_eq_zero hzero)
    have hbool :
        decodeABIValue? abiBool bytes 128 DecodeMode.legacySolc05 =
          some (.bool false, 160) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := abiBool) (bytes := bytes) (start := 128) (by decide)]
      simpa using hbools
    simp only [decodeABIValues?, isDynamicABIType, Bool.false_eq_true, if_false,
      staticABIEncodedSize?, Option.bind, bind]
    simp only [Nat.zero_add, Nat.add_assoc]
    rw [haddr0, haddr32, huint64, huint96, hbool, huint8, hbytes192, hbytes224]
    simp [hzero, bytes32Width]
  · have hbools := decodeScalarWordWithMode_legacy_bool_true (bytes := bytes) (start := 128)
      hlen128 (fun h => hzero (congrArg UInt256.toNat h))
    have hbool :
        decodeABIValue? abiBool bytes 128 DecodeMode.legacySolc05 =
          some (.bool true, 160) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := abiBool) (bytes := bytes) (start := 128) (by decide)]
      simpa using hbools
    simp only [decodeABIValues?, isDynamicABIType, Bool.false_eq_true, if_false,
      staticABIEncodedSize?, Option.bind, bind]
    simp only [Nat.zero_add, Nat.add_assoc]
    rw [haddr0, haddr32, huint64, huint96, hbool, huint8, hbytes192, hbytes224]
    simp [hzero, bytes32Width]

theorem daiDecode_permit_ok {I : ExecutionEnv}
    (hsz260 : 260 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (permitTransition.params.map Param.name)
      (transitionSignature permitTransition).paramTypes I.calldata = some (permitStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode
    ["holder", "spender", "nonce", "expiry", "allowed", "v", "r", "s"]
    [addr, addr, uint256, uint256, boolTy, uint8, bytes32, bytes32] I.calldata = _
  change decodeCalldataWithMode DecodeMode.legacySolc05
    ["holder", "spender", "nonce", "expiry", "allowed", "v", "r", "s"]
    [abiAddress, abiAddress, abiUInt256, abiUInt256, abiBool,
      ABIType.elem (ElemType.int uint8Int), ABIType.elem (ElemType.bytes bytes32Width),
      ABIType.elem (ElemType.bytes bytes32Width)] I.calldata = _
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by rw [htlen]; omega
  have hhead :
      abiTupleHeadSize?
          [abiAddress, abiAddress, abiUInt256, abiUInt256, abiBool,
            ABIType.elem (ElemType.int uint8Int), ABIType.elem (ElemType.bytes bytes32Width),
            ABIType.elem (ElemType.bytes bytes32Width)] =
        some 256 := by
    native_decide
  have hnotShort : ¬ (I.calldata.toList.drop 4).length < 256 := by
    rw [List.length_drop, htlen]; omega
  have htake0 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake32 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake64 : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake96 : (((I.calldata.toList.drop 4).drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake128 : (((I.calldata.toList.drop 4).drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake160 : (((I.calldata.toList.drop 4).drop 160).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake192 : (((I.calldata.toList.drop 4).drop 192).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake224 : (((I.calldata.toList.drop 4).drop 224).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword4 :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
        calldataWord I.calldata 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hword68 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32) =
        calldataWord I.calldata 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 68 (by omega) (by norm_num)
  have hword100 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32) =
        calldataWord I.calldata 100 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 100 (by omega) (by norm_num)
  have hword132 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32) =
        calldataWord I.calldata 132 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 132 (by omega) (by norm_num)
  have hword164 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 160).take 32) =
        calldataWord I.calldata 164 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 164 (by omega) (by norm_num)
  have hvalues := decodeABIValues_permit_ok
    (bytes := I.calldata.toList.drop 4) htake0 htake32 htake64 htake96 htake128 htake160
      htake192 htake224
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg hnot4]
  rw [if_neg (by simp [isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [hhead]
  simp only [Option.bind, bind]
  rw [if_neg hnotShort]
  rw [hvalues]
  rw [hword4, hword36, hword68, hword100, hword132, hword164]
  by_cases hzero : (calldataWord I.calldata 132).toNat = 0
  · simp [hzero, permitStore, permitHolderValue, permitSpenderValue, permitNonceValue,
      permitExpiryValue, permitAllowedValue, permitVValue, permitRValue, permitSValue,
      permitHolderWord, permitSpenderWord, permitNonceWord, permitExpiryWord, permitAllowedWord,
      permitVWord, permitRBytes, permitSBytes, decodeCalldata.insertValues, List.drop_drop]
  · simp [hzero, permitStore, permitHolderValue, permitSpenderValue, permitNonceValue,
      permitExpiryValue, permitAllowedValue, permitVValue, permitRValue, permitSValue,
      permitHolderWord, permitSpenderWord, permitNonceWord, permitExpiryWord, permitAllowedWord,
      permitVWord, permitRBytes, permitSBytes, decodeCalldata.insertValues, List.drop_drop]

theorem daiDecode_permit_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 260) :
    decodeCalldataWithMode config.abiDecodeMode (permitTransition.params.map Param.name)
      (transitionSignature permitTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode
    ["holder", "spender", "nonce", "expiry", "allowed", "v", "r", "s"]
    [addr, addr, uint256, uint256, boolTy, uint8, bytes32, bytes32] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05
    ["holder", "spender", "nonce", "expiry", "allowed", "v", "r", "s"]
    [abiAddress, abiAddress, abiUInt256, abiUInt256, abiBool,
      ABIType.elem (ElemType.int uint8Int), ABIType.elem (ElemType.bytes bytes32Width),
      ABIType.elem (ElemType.bytes bytes32Width)] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by rw [htlen]; omega
  have hhead :
      abiTupleHeadSize?
          [abiAddress, abiAddress, abiUInt256, abiUInt256, abiBool,
            ABIType.elem (ElemType.int uint8Int), ABIType.elem (ElemType.bytes bytes32Width),
            ABIType.elem (ElemType.bytes bytes32Width)] =
        some 256 := by
    native_decide
  have hshortArgs : (I.calldata.toList.drop 4).length < 256 := by
    rw [List.length_drop, htlen]; omega
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg hnot4]
  rw [if_neg (by simp [isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [hhead]
  simp only [Option.bind, bind]
  rw [if_pos hshortArgs]

/-! ## EVM external wrapper -/

theorem daiPermitX_lenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz260 : 260 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨810⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨833⟩
      [UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩, ⟨4⟩, ⟨686⟩, daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd810⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨256⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (head := (⟨4⟩ : UInt256)) (need := (⟨256⟩ : UInt256))
      hsz260 hsize
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨256⟩) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rd811 := rd810.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have rd814 := rd811.push2 ⟨686⟩ (by native_decide) (by evm_ov)
  have rd816 := rd814.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd817 := rd816.dup1 (by native_decide) (by evm_ov)
  have rd818 := rd817.calldatasize (by native_decide) (by evm_ov)
  have rd819 := rd818.sub (by native_decide) (by evm_ov)
  have rd822 := rd819.push2 ⟨256⟩ (by native_decide) (by evm_ov)
  have rd823 := rd822.dup2 (by native_decide) (by evm_ov)
  have rd824 := rd823.lt (by native_decide) (by evm_ov)
  have rd825 := rd824.iszero (by native_decide) (by evm_ov)
  have rd828 := rd825.push2 ⟨833⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd828.jumpiT (by native_decide) hjumpCond (by jump_dest) (by evm_ov)⟩

theorem daiPermitX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 260)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨810⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd810⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨256⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 256
    omega
  have rd811 := rd810.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have rd814 := rd811.push2 ⟨686⟩ (by native_decide) (by evm_ov)
  have rd816 := rd814.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd817 := rd816.dup1 (by native_decide) (by evm_ov)
  have rd818 := rd817.calldatasize (by native_decide) (by evm_ov)
  have rd819 := rd818.sub (by native_decide) (by evm_ov)
  have rd822 := rd819.push2 ⟨256⟩ (by native_decide) (by evm_ov)
  have rd823 := rd822.dup2 (by native_decide) (by evm_ov)
  have rd824₀ := rd823.lt (by native_decide) (by evm_ov)
  have rd824 := rd824₀
  rw [hlt] at rd824
  have rd825₀ := rd824.iszero (by native_decide) (by evm_ov)
  have rd825 := rd825₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd825
  have rd828 := rd825.push2 ⟨833⟩ (by native_decide) (by evm_ov)
  have rd829 := rd828.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd831 := rd829.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd832 := rd831.dup1 (by native_decide) (by evm_ov)
  exact rd832.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem daiPermitX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz260 : 260 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨810⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
      [permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd833⟩ := daiPermitX_lenOk hsz260 hsize hreach
  have rd899raw := evm_run rd833 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨2428⟩ (by native_decide) (by evm_ov)]
  have rd2428 := rd899raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [permitHolderMaskedWord, permitSpenderMaskedWord, permitAllowedCleanWord,
      permitVMaskedWord, permitHolderWord, permitSpenderWord, permitNonceWord,
      permitExpiryWord, permitAllowedWord, permitVWord, permitRWord, permitSWord,
      calldataWord, solcAddrMask] using rd2428⟩

noncomputable abbrev permitWordMem (mem : ByteArray) (off : Nat) (word : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord mem off word

theorem permitWordMem_size (mem : ByteArray) (off : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size) :
    (permitWordMem mem off word).size = max mem.size (off + 32) := by
  simpa [permitWordMem] using Reasoning.Theory.writeWord_size mem off word hgap

theorem permitWordMem_read64_preserve {mem : ByteArray} {off : Nat} {word : UInt256}
    (hsize : 96 ≤ mem.size) (hoff : 96 ≤ off) (hgap : off - mem.size < USize.size) :
    (permitWordMem mem off word).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  simpa [permitWordMem] using
    Reasoning.Theory.writeWord_read_preserved mem off 64 word hgap
      (Or.inl ⟨by omega, by omega⟩)

theorem permitWordMem_read_preserve {mem : ByteArray} {off read : Nat} {word : UInt256}
    (hgap : off - mem.size < USize.size)
    (hdisj :
      (read + 32 ≤ off ∧ read + 32 ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + 32 ≤ mem.size)) :
    (permitWordMem mem off word).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  simpa [permitWordMem] using
    Reasoning.Theory.writeWord_read_preserved mem off read word hgap hdisj

theorem permitWordMem_read_preserve_len {mem : ByteArray} {off read len : Nat}
    {word : UInt256}
    (hgap : off - mem.size < USize.size)
    (hdisj :
      (read + len ≤ off ∧ read + len ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + len ≤ mem.size))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (permitWordMem mem off word).readWithPadding read len =
      mem.readWithPadding read len := by
  simpa [permitWordMem] using
    Reasoning.Theory.writeWord_read_preserved_len mem off read len word hgap hdisj hpos hlen64

theorem permitWordMem_read_back (mem : ByteArray) (off : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size) :
    (permitWordMem mem off word).readWithPadding off 32 = UInt256.toByteArray word := by
  simpa [permitWordMem, Reasoning.Theory.writeWord] using
    Reasoning.Theory.writeWord_read_back mem off word hgap

noncomputable abbrev permitTwoWordHashMem
    (mem : ByteArray) (key slot : UInt256) : ByteArray :=
  permitWordMem (permitWordMem mem 0 key) 32 slot

noncomputable abbrev permitNonceHashMem (mem : ByteArray) (I : ExecutionEnv) : ByteArray :=
  permitTwoWordHashMem mem (permitHolderMaskedWord I) (⟨4⟩ : UInt256)

noncomputable abbrev permitAllowanceOwnerHashMem (mem : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  permitTwoWordHashMem mem (permitHolderMaskedWord I) (⟨3⟩ : UInt256)

noncomputable abbrev permitAllowanceHashMem (mem : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  permitTwoWordHashMem (permitAllowanceOwnerHashMem mem I) (permitSpenderMaskedWord I)
    (mapSlot (permitHolderMaskedWord I) ⟨3⟩)

noncomputable abbrev permitApprovalLogMem (mem : ByteArray) (I : ExecutionEnv) : ByteArray :=
  permitWordMem mem 482 (permitWadWord I)

abbrev permitApprovalTopic : UInt256 :=
  ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩

theorem permitTwoWordHashMem_size {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (permitTwoWordHashMem mem key slot).size = mem.size := by
  have hzero : 0 < USize.size := lt_usize 0 (by norm_num)
  have hkey : (permitWordMem mem 0 key).size = mem.size := by
    rw [permitWordMem_size]
    · omega
    · omega
  unfold permitTwoWordHashMem
  rw [permitWordMem_size]
  · rw [hkey]
    omega
  · rw [hkey]
    omega

theorem permitTwoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    (permitTwoWordHashMem mem key slot).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  have hzero : 0 < USize.size := lt_usize 0 (by norm_num)
  have hkeySize : (permitWordMem mem 0 key).size = mem.size := by
    rw [permitWordMem_size]
    · omega
    · omega
  calc
    (permitTwoWordHashMem mem key slot).readWithPadding 64 32 =
        (permitWordMem mem 0 key).readWithPadding 64 32 := by
      simpa [permitTwoWordHashMem] using
        permitWordMem_read_preserve
          (mem := permitWordMem mem 0 key) (off := 32) (read := 64) (word := slot)
          (hgap := by rw [hkeySize]; omega)
          (hdisj := Or.inr ⟨by norm_num, by rw [hkeySize]; omega⟩)
    _ = mem.readWithPadding 64 32 := by
      simpa using
        permitWordMem_read_preserve
          (mem := mem) (off := 0) (read := 64) (word := key)
          (hgap := by omega)
          (hdisj := Or.inr ⟨by norm_num, by omega⟩)

set_option maxHeartbeats 800000 in
theorem permitTwoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (permitTwoWordHashMem mem key slot).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hzero : 0 < USize.size := lt_usize 0 (by norm_num)
  have hkeySize : (permitWordMem mem 0 key).size = mem.size := by
    rw [permitWordMem_size]
    · omega
    · omega
  have hhashSize : (permitTwoWordHashMem mem key slot).size = mem.size :=
    permitTwoWordHashMem_size key slot hmem
  have hread0 :
      (permitTwoWordHashMem mem key slot).readWithPadding 0 32 =
        UInt256.toByteArray key := by
    calc
      (permitTwoWordHashMem mem key slot).readWithPadding 0 32 =
          (permitWordMem mem 0 key).readWithPadding 0 32 := by
        simpa [permitTwoWordHashMem] using
          permitWordMem_read_preserve
            (mem := permitWordMem mem 0 key) (off := 32) (read := 0) (word := slot)
            (hgap := by rw [hkeySize]; omega)
            (hdisj := Or.inl ⟨by norm_num, by rw [hkeySize]; omega⟩)
      _ = UInt256.toByteArray key := by
        simpa using permitWordMem_read_back mem 0 key (by omega)
  have hread32 :
      (permitTwoWordHashMem mem key slot).readWithPadding 32 32 =
        UInt256.toByteArray slot := by
    simpa [permitTwoWordHashMem] using
      permitWordMem_read_back (permitWordMem mem 0 key) 32 slot
        (by rw [hkeySize]; omega)
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hhashSize]; omega)]
  have hleft :
      (permitTwoWordHashMem mem key slot).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hhashSize]; omega), hread0]
  have hright :
      (permitTwoWordHashMem mem key slot).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hhashSize]; omega), hread32]
  rw [show (permitTwoWordHashMem mem key slot).extract 0 64 =
      (permitTwoWordHashMem mem key slot).extract 0 32 ++
        (permitTwoWordHashMem mem key slot).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem permitTwoWordHashMem_slot {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((permitTwoWordHashMem mem key slot).readWithPadding 0 64))) =
      mapSlot key slot := by
  rw [permitTwoWordHashMem_read0_64 key slot hmem]
  unfold mapSlot
  rw [uInt256OfByteArray_eq]

theorem permitApprovalLogMem_size {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 610) :
    (permitApprovalLogMem mem I).size = 610 := by
  unfold permitApprovalLogMem
  rw [permitWordMem_size]
  · rw [hmem]
    norm_num
  · rw [hmem]
    norm_num

abbrev permitTypehashWordLit : UInt256 :=
  ⟨105916522785188513640362517802612480037966763957092682311465172263008277174987⟩

abbrev permitInvalidAddress0RawWord : UInt256 :=
  ⟨0x04461692f696e76616c69642d616464726573732d3⟩

abbrev permitInvalidAddress0Word : UInt256 :=
  ⟨0x4461692f696e76616c69642d616464726573732d300000000000000000000000⟩

theorem permitInvalidAddress0Word_shift :
    UInt256.shiftLeft permitInvalidAddress0RawWord ⟨92⟩ = permitInvalidAddress0Word := by
  native_decide

theorem permitTypehashBytes_eq_wordLit :
    permitTypehashBytes = EVM.Word.toBytesBE permitTypehashWordLit := by
  native_decide

noncomputable abbrev permitStructMem1 (I : ExecutionEnv) : ByteArray :=
  permitWordMem solcFreePtrMem 160 permitTypehashWordLit

noncomputable abbrev permitStructMem2 (I : ExecutionEnv) : ByteArray :=
  permitWordMem (permitStructMem1 I) 192 (permitHolderMaskedWord I)

noncomputable abbrev permitStructMem3 (I : ExecutionEnv) : ByteArray :=
  permitWordMem (permitStructMem2 I) 224 (permitSpenderMaskedWord I)

noncomputable abbrev permitStructMem4 (I : ExecutionEnv) : ByteArray :=
  permitWordMem (permitStructMem3 I) 256 (permitNonceWord I)

noncomputable abbrev permitStructMem5 (I : ExecutionEnv) : ByteArray :=
  permitWordMem (permitStructMem4 I) 288 (permitExpiryWord I)

noncomputable abbrev permitStructMem6 (I : ExecutionEnv) : ByteArray :=
  permitWordMem (permitStructMem5 I) 320
    (UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))

noncomputable abbrev permitDigestMem7 (I : ExecutionEnv) : ByteArray :=
  permitWordMem (permitStructMem6 I) 128 (⟨192⟩ : UInt256)

noncomputable abbrev permitDigestMem8 (I : ExecutionEnv) : ByteArray :=
  permitWordMem (permitDigestMem7 I) 64 (⟨352⟩ : UInt256)

noncomputable abbrev permitStructHashMemWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC ((permitDigestMem8 I).readWithPadding 160 192)))

abbrev permitEip191Word : UInt256 :=
  UInt256.shiftLeft (⟨6401⟩ : UInt256) ⟨240⟩

theorem permitEip191Word_prefix :
    (UInt256.toByteArray permitEip191Word).extract 0 2 = [25, 1].toByteArray := by
  rw [toByteArray_eq_toBytesBE]
  native_decide

noncomputable abbrev permitDigestMem9 (I : ExecutionEnv) (domainWord : UInt256) :
    ByteArray :=
  permitWordMem (permitDigestMem8 I) 384 permitEip191Word

noncomputable abbrev permitDigestMem10 (I : ExecutionEnv) (domainWord : UInt256) :
    ByteArray :=
  permitWordMem (permitDigestMem9 I domainWord) 386 domainWord

noncomputable abbrev permitDigestMem11 (I : ExecutionEnv) (domainWord : UInt256) :
    ByteArray :=
  permitWordMem (permitDigestMem10 I domainWord) 418 (permitStructHashMemWord I)

noncomputable abbrev permitDigestMem12 (I : ExecutionEnv) (domainWord : UInt256) :
    ByteArray :=
  permitWordMem (permitDigestMem11 I domainWord) 352 (⟨66⟩ : UInt256)

noncomputable abbrev permitDigestMem13 (I : ExecutionEnv) (domainWord : UInt256) :
    ByteArray :=
  permitWordMem (permitDigestMem12 I domainWord) 64 (⟨450⟩ : UInt256)

theorem permitStructMem1_size (I : ExecutionEnv) : (permitStructMem1 I).size = 192 := by
  unfold permitStructMem1
  rw [permitWordMem_size]
  · rw [solcFreePtrMem_size]; native_decide
  · rw [solcFreePtrMem_size]; native_decide

theorem permitStructMem2_size (I : ExecutionEnv) : (permitStructMem2 I).size = 224 := by
  unfold permitStructMem2
  rw [permitWordMem_size]
  · rw [permitStructMem1_size]; native_decide
  · rw [permitStructMem1_size]; native_decide

theorem permitStructMem3_size (I : ExecutionEnv) : (permitStructMem3 I).size = 256 := by
  unfold permitStructMem3
  rw [permitWordMem_size]
  · rw [permitStructMem2_size]; native_decide
  · rw [permitStructMem2_size]; native_decide

theorem permitStructMem4_size (I : ExecutionEnv) : (permitStructMem4 I).size = 288 := by
  unfold permitStructMem4
  rw [permitWordMem_size]
  · rw [permitStructMem3_size]; native_decide
  · rw [permitStructMem3_size]; native_decide

theorem permitStructMem5_size (I : ExecutionEnv) : (permitStructMem5 I).size = 320 := by
  unfold permitStructMem5
  rw [permitWordMem_size]
  · rw [permitStructMem4_size]; native_decide
  · rw [permitStructMem4_size]; native_decide

theorem permitStructMem6_size (I : ExecutionEnv) : (permitStructMem6 I).size = 352 := by
  unfold permitStructMem6
  rw [permitWordMem_size]
  · rw [permitStructMem5_size]; native_decide
  · rw [permitStructMem5_size]; native_decide

theorem permitDigestMem7_size (I : ExecutionEnv) : (permitDigestMem7 I).size = 352 := by
  unfold permitDigestMem7
  rw [permitWordMem_size]
  · rw [permitStructMem6_size]; native_decide
  · rw [permitStructMem6_size]; native_decide

theorem permitDigestMem8_size (I : ExecutionEnv) : (permitDigestMem8 I).size = 352 := by
  unfold permitDigestMem8
  rw [permitWordMem_size]
  · rw [permitDigestMem7_size]; native_decide
  · rw [permitDigestMem7_size]; native_decide

theorem permitDigestMem9_size (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem9 I domainWord).size = 416 := by
  unfold permitDigestMem9
  rw [permitWordMem_size]
  · rw [permitDigestMem8_size]; native_decide
  · rw [permitDigestMem8_size]; native_decide

theorem permitDigestMem10_size (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem10 I domainWord).size = 418 := by
  unfold permitDigestMem10
  rw [permitWordMem_size]
  · rw [permitDigestMem9_size]; native_decide
  · rw [permitDigestMem9_size]; native_decide

theorem permitDigestMem11_size (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem11 I domainWord).size = 450 := by
  unfold permitDigestMem11
  rw [permitWordMem_size]
  · rw [permitDigestMem10_size]; native_decide
  · rw [permitDigestMem10_size]; native_decide

theorem permitDigestMem12_size (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem12 I domainWord).size = 450 := by
  unfold permitDigestMem12
  rw [permitWordMem_size]
  · rw [permitDigestMem11_size]; native_decide
  · rw [permitDigestMem11_size]; native_decide

theorem permitDigestMem13_size (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem13 I domainWord).size = 450 := by
  unfold permitDigestMem13
  rw [permitWordMem_size]
  · rw [permitDigestMem12_size]; native_decide
  · rw [permitDigestMem12_size]; native_decide

theorem permitStructMem1_read64 (I : ExecutionEnv) :
    (permitStructMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [permitStructMem1] using
    permitWordMem_read64_preserve (mem := solcFreePtrMem) (off := 160)
      (word := permitTypehashWordLit)
      (hsize := by rw [solcFreePtrMem_size])
      (hoff := by norm_num)
      (hgap := by rw [solcFreePtrMem_size]; native_decide) |>.trans solcFreePtrMem_read64

theorem permitStructMem2_read64 (I : ExecutionEnv) :
    (permitStructMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [permitStructMem2] using
    permitWordMem_read64_preserve (mem := permitStructMem1 I) (off := 192)
      (word := permitHolderMaskedWord I)
      (hsize := by rw [permitStructMem1_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitStructMem1_size]; native_decide) |>.trans
        (permitStructMem1_read64 I)

theorem permitStructMem3_read64 (I : ExecutionEnv) :
    (permitStructMem3 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [permitStructMem3] using
    permitWordMem_read64_preserve (mem := permitStructMem2 I) (off := 224)
      (word := permitSpenderMaskedWord I)
      (hsize := by rw [permitStructMem2_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitStructMem2_size]; native_decide) |>.trans
        (permitStructMem2_read64 I)

theorem permitStructMem4_read64 (I : ExecutionEnv) :
    (permitStructMem4 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [permitStructMem4] using
    permitWordMem_read64_preserve (mem := permitStructMem3 I) (off := 256)
      (word := permitNonceWord I)
      (hsize := by rw [permitStructMem3_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitStructMem3_size]; native_decide) |>.trans
        (permitStructMem3_read64 I)

theorem permitStructMem5_read64 (I : ExecutionEnv) :
    (permitStructMem5 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [permitStructMem5] using
    permitWordMem_read64_preserve (mem := permitStructMem4 I) (off := 288)
      (word := permitExpiryWord I)
      (hsize := by rw [permitStructMem4_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitStructMem4_size]; native_decide) |>.trans
        (permitStructMem4_read64 I)

theorem permitStructMem6_read64 (I : ExecutionEnv) :
    (permitStructMem6 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [permitStructMem6] using
    permitWordMem_read64_preserve (mem := permitStructMem5 I) (off := 320)
      (word := UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))
      (hsize := by rw [permitStructMem5_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitStructMem5_size]; native_decide) |>.trans
        (permitStructMem5_read64 I)

theorem permitStructMem6_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (permitStructMem6 I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitStructMem6 I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [permitStructMem6_size]; decide) (by decide)
    (permitStructMem6_read64 I)

theorem permitDigestMem7_read128 (I : ExecutionEnv) :
    (permitDigestMem7 I).readWithPadding 128 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  simpa [permitDigestMem7] using
    permitWordMem_read_back (permitStructMem6 I) 128 (⟨192⟩ : UInt256)
      (by rw [permitStructMem6_size]; native_decide)

theorem permitDigestMem8_read128 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 128 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  simpa [permitDigestMem8] using
    permitWordMem_read_preserve (mem := permitDigestMem7 I) (off := 64) (read := 128)
      (word := (⟨352⟩ : UInt256))
      (hgap := by rw [permitDigestMem7_size]; native_decide)
      (hdisj := Or.inr ⟨by norm_num, by rw [permitDigestMem7_size]; norm_num⟩) |>.trans
        (permitDigestMem7_read128 I)

theorem permitDigestMem8_mload128 (I : ExecutionEnv) :
    (if (⟨128⟩ : UInt256).toNat ≥ (permitDigestMem8 I).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitDigestMem8 I).readWithPadding (⟨128⟩ : UInt256).toNat 32)))
      = ⟨192⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 11) (v := (⟨192⟩ : UInt256))
    (by rw [permitDigestMem8_size]; decide)
    (by decide)
    (by simpa using permitDigestMem8_read128 I)

theorem permitDigestMem8_read_structMem6 (I : ExecutionEnv) {read : Nat}
    (hlo : 160 ≤ read) (hhi : read + 32 ≤ 352) :
    (permitDigestMem8 I).readWithPadding read 32 =
      (permitStructMem6 I).readWithPadding read 32 := by
  calc
    (permitDigestMem8 I).readWithPadding read 32 =
        (permitDigestMem7 I).readWithPadding read 32 := by
      simpa [permitDigestMem8] using
        permitWordMem_read_preserve (mem := permitDigestMem7 I) (off := 64)
          (read := read) (word := (⟨352⟩ : UInt256))
          (hgap := by rw [permitDigestMem7_size]; native_decide)
          (hdisj := Or.inr ⟨by omega, by rw [permitDigestMem7_size]; omega⟩)
    _ = (permitStructMem6 I).readWithPadding read 32 := by
      simpa [permitDigestMem7] using
        permitWordMem_read_preserve (mem := permitStructMem6 I) (off := 128)
          (read := read) (word := (⟨192⟩ : UInt256))
          (hgap := by rw [permitStructMem6_size]; native_decide)
          (hdisj := Or.inr ⟨by omega, by rw [permitStructMem6_size]; omega⟩)

theorem permitDigestMem8_read160 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 160 32 =
      UInt256.toByteArray permitTypehashWordLit := by
  calc
    (permitDigestMem8 I).readWithPadding 160 32 =
        (permitStructMem6 I).readWithPadding 160 32 :=
      permitDigestMem8_read_structMem6 I (by norm_num) (by norm_num)
    _ = (permitStructMem5 I).readWithPadding 160 32 := by
      simpa [permitStructMem6] using
        permitWordMem_read_preserve (mem := permitStructMem5 I) (off := 320)
          (read := 160) (word := UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))
          (hgap := by rw [permitStructMem5_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem5_size]⟩)
    _ = (permitStructMem4 I).readWithPadding 160 32 := by
      simpa [permitStructMem5] using
        permitWordMem_read_preserve (mem := permitStructMem4 I) (off := 288)
          (read := 160) (word := permitExpiryWord I)
          (hgap := by rw [permitStructMem4_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem4_size]⟩)
    _ = (permitStructMem3 I).readWithPadding 160 32 := by
      simpa [permitStructMem4] using
        permitWordMem_read_preserve (mem := permitStructMem3 I) (off := 256)
          (read := 160) (word := permitNonceWord I)
          (hgap := by rw [permitStructMem3_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem3_size]⟩)
    _ = (permitStructMem2 I).readWithPadding 160 32 := by
      simpa [permitStructMem3] using
        permitWordMem_read_preserve (mem := permitStructMem2 I) (off := 224)
          (read := 160) (word := permitSpenderMaskedWord I)
          (hgap := by rw [permitStructMem2_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem2_size]⟩)
    _ = (permitStructMem1 I).readWithPadding 160 32 := by
      simpa [permitStructMem2] using
        permitWordMem_read_preserve (mem := permitStructMem1 I) (off := 192)
          (read := 160) (word := permitHolderMaskedWord I)
          (hgap := by rw [permitStructMem1_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem1_size]⟩)
    _ = UInt256.toByteArray permitTypehashWordLit := by
      simpa [permitStructMem1] using
        permitWordMem_read_back solcFreePtrMem 160 permitTypehashWordLit
          (by rw [solcFreePtrMem_size]; native_decide)

theorem permitDigestMem8_read192 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 192 32 =
      UInt256.toByteArray (permitHolderMaskedWord I) := by
  calc
    (permitDigestMem8 I).readWithPadding 192 32 =
        (permitStructMem6 I).readWithPadding 192 32 :=
      permitDigestMem8_read_structMem6 I (by norm_num) (by norm_num)
    _ = (permitStructMem5 I).readWithPadding 192 32 := by
      simpa [permitStructMem6] using
        permitWordMem_read_preserve (mem := permitStructMem5 I) (off := 320)
          (read := 192) (word := UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))
          (hgap := by rw [permitStructMem5_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem5_size]⟩)
    _ = (permitStructMem4 I).readWithPadding 192 32 := by
      simpa [permitStructMem5] using
        permitWordMem_read_preserve (mem := permitStructMem4 I) (off := 288)
          (read := 192) (word := permitExpiryWord I)
          (hgap := by rw [permitStructMem4_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem4_size]⟩)
    _ = (permitStructMem3 I).readWithPadding 192 32 := by
      simpa [permitStructMem4] using
        permitWordMem_read_preserve (mem := permitStructMem3 I) (off := 256)
          (read := 192) (word := permitNonceWord I)
          (hgap := by rw [permitStructMem3_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem3_size]⟩)
    _ = (permitStructMem2 I).readWithPadding 192 32 := by
      simpa [permitStructMem3] using
        permitWordMem_read_preserve (mem := permitStructMem2 I) (off := 224)
          (read := 192) (word := permitSpenderMaskedWord I)
          (hgap := by rw [permitStructMem2_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem2_size]⟩)
    _ = UInt256.toByteArray (permitHolderMaskedWord I) := by
      simpa [permitStructMem2] using
        permitWordMem_read_back (permitStructMem1 I) 192 (permitHolderMaskedWord I)
          (by rw [permitStructMem1_size]; native_decide)

theorem permitDigestMem8_read224 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 224 32 =
      UInt256.toByteArray (permitSpenderMaskedWord I) := by
  calc
    (permitDigestMem8 I).readWithPadding 224 32 =
        (permitStructMem6 I).readWithPadding 224 32 :=
      permitDigestMem8_read_structMem6 I (by norm_num) (by norm_num)
    _ = (permitStructMem5 I).readWithPadding 224 32 := by
      simpa [permitStructMem6] using
        permitWordMem_read_preserve (mem := permitStructMem5 I) (off := 320)
          (read := 224) (word := UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))
          (hgap := by rw [permitStructMem5_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem5_size]⟩)
    _ = (permitStructMem4 I).readWithPadding 224 32 := by
      simpa [permitStructMem5] using
        permitWordMem_read_preserve (mem := permitStructMem4 I) (off := 288)
          (read := 224) (word := permitExpiryWord I)
          (hgap := by rw [permitStructMem4_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem4_size]⟩)
    _ = (permitStructMem3 I).readWithPadding 224 32 := by
      simpa [permitStructMem4] using
        permitWordMem_read_preserve (mem := permitStructMem3 I) (off := 256)
          (read := 224) (word := permitNonceWord I)
          (hgap := by rw [permitStructMem3_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem3_size]⟩)
    _ = UInt256.toByteArray (permitSpenderMaskedWord I) := by
      simpa [permitStructMem3] using
        permitWordMem_read_back (permitStructMem2 I) 224 (permitSpenderMaskedWord I)
          (by rw [permitStructMem2_size]; native_decide)

theorem permitDigestMem8_read256 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 256 32 =
      UInt256.toByteArray (permitNonceWord I) := by
  calc
    (permitDigestMem8 I).readWithPadding 256 32 =
        (permitStructMem6 I).readWithPadding 256 32 :=
      permitDigestMem8_read_structMem6 I (by norm_num) (by norm_num)
    _ = (permitStructMem5 I).readWithPadding 256 32 := by
      simpa [permitStructMem6] using
        permitWordMem_read_preserve (mem := permitStructMem5 I) (off := 320)
          (read := 256) (word := UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))
          (hgap := by rw [permitStructMem5_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem5_size]⟩)
    _ = (permitStructMem4 I).readWithPadding 256 32 := by
      simpa [permitStructMem5] using
        permitWordMem_read_preserve (mem := permitStructMem4 I) (off := 288)
          (read := 256) (word := permitExpiryWord I)
          (hgap := by rw [permitStructMem4_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem4_size]⟩)
    _ = UInt256.toByteArray (permitNonceWord I) := by
      simpa [permitStructMem4] using
        permitWordMem_read_back (permitStructMem3 I) 256 (permitNonceWord I)
          (by rw [permitStructMem3_size]; native_decide)

theorem permitDigestMem8_read288 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 288 32 =
      UInt256.toByteArray (permitExpiryWord I) := by
  calc
    (permitDigestMem8 I).readWithPadding 288 32 =
        (permitStructMem6 I).readWithPadding 288 32 :=
      permitDigestMem8_read_structMem6 I (by norm_num) (by norm_num)
    _ = (permitStructMem5 I).readWithPadding 288 32 := by
      simpa [permitStructMem6] using
        permitWordMem_read_preserve (mem := permitStructMem5 I) (off := 320)
          (read := 288) (word := UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))
          (hgap := by rw [permitStructMem5_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitStructMem5_size]⟩)
    _ = UInt256.toByteArray (permitExpiryWord I) := by
      simpa [permitStructMem5] using
        permitWordMem_read_back (permitStructMem4 I) 288 (permitExpiryWord I)
          (by rw [permitStructMem4_size]; native_decide)

theorem permitDigestMem8_read320 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 320 32 =
      UInt256.toByteArray (permitAllowedCleanWord I) := by
  calc
    (permitDigestMem8 I).readWithPadding 320 32 =
        (permitStructMem6 I).readWithPadding 320 32 :=
      permitDigestMem8_read_structMem6 I (by norm_num) (by norm_num)
    _ = UInt256.toByteArray (UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I))) := by
      simpa [permitStructMem6] using
        permitWordMem_read_back (permitStructMem5 I) 320
          (UInt256.isZero (UInt256.isZero (permitAllowedCleanWord I)))
          (by rw [permitStructMem5_size]; native_decide)
    _ = UInt256.toByteArray (permitAllowedCleanWord I) := by
      rw [permitAllowedCleanWord_stable]

theorem permitDigestMem8_read160_192_eq (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 160 192 = permitStructPackedByteArray I := by
  have h0 :
      (permitDigestMem8 I).readWithPadding 160 (32 + 160) =
        (permitDigestMem8 I).readWithPadding 160 32 ++
          (permitDigestMem8 I).readWithPadding (160 + 32) 160 :=
    byteArray_readWithPadding_split (permitDigestMem8 I) 160 32 160
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [permitDigestMem8_size])
  have h1 :
      (permitDigestMem8 I).readWithPadding 192 (32 + 128) =
        (permitDigestMem8 I).readWithPadding 192 32 ++
          (permitDigestMem8 I).readWithPadding (192 + 32) 128 :=
    byteArray_readWithPadding_split (permitDigestMem8 I) 192 32 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [permitDigestMem8_size])
  have h2 :
      (permitDigestMem8 I).readWithPadding 224 (32 + 96) =
        (permitDigestMem8 I).readWithPadding 224 32 ++
          (permitDigestMem8 I).readWithPadding (224 + 32) 96 :=
    byteArray_readWithPadding_split (permitDigestMem8 I) 224 32 96
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [permitDigestMem8_size])
  have h3 :
      (permitDigestMem8 I).readWithPadding 256 (32 + 64) =
        (permitDigestMem8 I).readWithPadding 256 32 ++
          (permitDigestMem8 I).readWithPadding (256 + 32) 64 :=
    byteArray_readWithPadding_split (permitDigestMem8 I) 256 32 64
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [permitDigestMem8_size])
  have h4 :
      (permitDigestMem8 I).readWithPadding 288 (32 + 32) =
        (permitDigestMem8 I).readWithPadding 288 32 ++
          (permitDigestMem8 I).readWithPadding (288 + 32) 32 :=
    byteArray_readWithPadding_split (permitDigestMem8 I) 288 32 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [permitDigestMem8_size])
  rw [show 192 = 32 + 160 by norm_num, h0]
  rw [show 160 = 32 + 128 by norm_num, h1]
  rw [show 128 = 32 + 96 by norm_num, h2]
  rw [show 96 = 32 + 64 by norm_num, h3]
  rw [show 64 = 32 + 32 by norm_num, h4]
  rw [permitDigestMem8_read160, permitDigestMem8_read192, permitDigestMem8_read224,
    permitDigestMem8_read256, permitDigestMem8_read288, permitDigestMem8_read320]
  simp [permitStructPackedByteArray, permitTypehashBytes_eq_wordLit,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem permitDigestMem8_read64 (I : ExecutionEnv) :
    (permitDigestMem8 I).readWithPadding 64 32 =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  simpa [permitDigestMem8] using
    permitWordMem_read_back (permitDigestMem7 I) 64 (⟨352⟩ : UInt256)
      (by rw [permitDigestMem7_size]; native_decide)

theorem permitDigestMem9_read64 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem9 I domainWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  simpa [permitDigestMem9] using
    permitWordMem_read64_preserve (mem := permitDigestMem8 I) (off := 384)
      (word := permitEip191Word)
      (hsize := by rw [permitDigestMem8_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitDigestMem8_size]; native_decide) |>.trans
        (permitDigestMem8_read64 I)

theorem permitDigestMem10_read64 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem10 I domainWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  simpa [permitDigestMem10] using
    permitWordMem_read64_preserve (mem := permitDigestMem9 I domainWord) (off := 386)
      (word := domainWord)
      (hsize := by rw [permitDigestMem9_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitDigestMem9_size]; native_decide) |>.trans
        (permitDigestMem9_read64 I domainWord)

theorem permitDigestMem11_read64 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem11 I domainWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  simpa [permitDigestMem11] using
    permitWordMem_read64_preserve (mem := permitDigestMem10 I domainWord) (off := 418)
      (word := permitStructHashMemWord I)
      (hsize := by rw [permitDigestMem10_size]; norm_num)
      (hoff := by norm_num)
      (hgap := by rw [permitDigestMem10_size]; native_decide) |>.trans
        (permitDigestMem10_read64 I domainWord)

theorem permitDigestMem11_mload64 (I : ExecutionEnv) (domainWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (permitDigestMem11 I domainWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitDigestMem11 I domainWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨352⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 15) (v := (⟨352⟩ : UInt256))
    (by rw [permitDigestMem11_size]; decide)
    (by decide)
    (by simpa using permitDigestMem11_read64 I domainWord)

theorem permitDigestMem12_read352 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem12 I domainWord).readWithPadding 352 32 =
      UInt256.toByteArray (⟨66⟩ : UInt256) := by
  simpa [permitDigestMem12] using
    permitWordMem_read_back (permitDigestMem11 I domainWord) 352 (⟨66⟩ : UInt256)
      (by rw [permitDigestMem11_size]; native_decide)

theorem permitDigestMem13_read352 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem13 I domainWord).readWithPadding 352 32 =
      UInt256.toByteArray (⟨66⟩ : UInt256) := by
  simpa [permitDigestMem13] using
    permitWordMem_read_preserve (mem := permitDigestMem12 I domainWord) (off := 64)
      (read := 352) (word := (⟨450⟩ : UInt256))
      (hgap := by rw [permitDigestMem12_size]; native_decide)
      (hdisj := Or.inr ⟨by norm_num, by rw [permitDigestMem12_size]; norm_num⟩) |>.trans
        (permitDigestMem12_read352 I domainWord)

theorem permitDigestMem13_mload352 (I : ExecutionEnv) (domainWord : UInt256) :
    (if (⟨352⟩ : UInt256).toNat ≥ (permitDigestMem13 I domainWord).size
        ∨ (⟨352⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitDigestMem13 I domainWord).readWithPadding (⟨352⟩ : UInt256).toNat 32)))
      = ⟨66⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨352⟩ : UInt256)) (aw := UInt256.ofNat 15) (v := (⟨66⟩ : UInt256))
    (by rw [permitDigestMem13_size]; decide)
    (by decide)
    (by simpa using permitDigestMem13_read352 I domainWord)

theorem permitDigestMem13_read64 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem13 I domainWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨450⟩ : UInt256) := by
  simpa [permitDigestMem13] using
    permitWordMem_read_back (permitDigestMem12 I domainWord) 64 (⟨450⟩ : UInt256)
      (by rw [permitDigestMem12_size]; native_decide)

theorem permitDigestMem13_mload64 (I : ExecutionEnv) (domainWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (permitDigestMem13 I domainWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitDigestMem13 I domainWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨450⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 15) (v := (⟨450⟩ : UInt256))
    (by rw [permitDigestMem13_size]; decide)
    (by decide)
    (by simpa using permitDigestMem13_read64 I domainWord)

theorem permitDigestMem12_read384_66 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem12 I domainWord).readWithPadding 384 66 =
      (permitDigestMem11 I domainWord).readWithPadding 384 66 := by
  simpa [permitDigestMem12] using
    permitWordMem_read_preserve_len (mem := permitDigestMem11 I domainWord) (off := 352)
      (read := 384) (len := 66) (word := (⟨66⟩ : UInt256))
      (hgap := by rw [permitDigestMem11_size]; native_decide)
      (hdisj := Or.inr ⟨by norm_num, by rw [permitDigestMem11_size]⟩)
      (hpos := by norm_num) (hlen64 := by norm_num)

theorem permitDigestMem13_read384_66 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem13 I domainWord).readWithPadding 384 66 =
      (permitDigestMem11 I domainWord).readWithPadding 384 66 := by
  simpa [permitDigestMem13] using
    permitWordMem_read_preserve_len (mem := permitDigestMem12 I domainWord) (off := 64)
      (read := 384) (len := 66) (word := (⟨450⟩ : UInt256))
      (hgap := by rw [permitDigestMem12_size]; native_decide)
      (hdisj := Or.inr ⟨by norm_num, by rw [permitDigestMem12_size]⟩)
      (hpos := by norm_num) (hlen64 := by norm_num) |>.trans
        (permitDigestMem12_read384_66 I domainWord)

theorem permitDigestMem11_read384_2 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem11 I domainWord).readWithPadding 384 2 = [25, 1].toByteArray := by
  calc
    (permitDigestMem11 I domainWord).readWithPadding 384 2 =
        (permitDigestMem10 I domainWord).readWithPadding 384 2 := by
      simpa [permitDigestMem11] using
        permitWordMem_read_preserve_len (mem := permitDigestMem10 I domainWord) (off := 418)
          (read := 384) (len := 2) (word := permitStructHashMemWord I)
          (hgap := by rw [permitDigestMem10_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitDigestMem10_size]⟩)
          (hpos := by norm_num) (hlen64 := by norm_num)
    _ = (permitDigestMem9 I domainWord).readWithPadding 384 2 := by
      simpa [permitDigestMem10] using
        permitWordMem_read_preserve_len (mem := permitDigestMem9 I domainWord) (off := 386)
          (read := 384) (len := 2) (word := domainWord)
          (hgap := by rw [permitDigestMem9_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitDigestMem9_size]⟩)
          (hpos := by norm_num) (hlen64 := by norm_num)
    _ = (UInt256.toByteArray permitEip191Word).extract 0 2 := by
      simpa [permitDigestMem9, permitWordMem] using
        Reasoning.Theory.writeWord_read_window (permitDigestMem8 I) 384 0 2
          permitEip191Word (by norm_num) (by norm_num) (by norm_num)
          (by rw [permitDigestMem8_size]; native_decide)
    _ = [25, 1].toByteArray := permitEip191Word_prefix

theorem permitDigestMem11_read386 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem11 I domainWord).readWithPadding 386 32 =
      UInt256.toByteArray domainWord := by
  calc
    (permitDigestMem11 I domainWord).readWithPadding 386 32 =
        (permitDigestMem10 I domainWord).readWithPadding 386 32 := by
      simpa [permitDigestMem11] using
        permitWordMem_read_preserve (mem := permitDigestMem10 I domainWord) (off := 418)
          (read := 386) (word := permitStructHashMemWord I)
          (hgap := by rw [permitDigestMem10_size]; native_decide)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitDigestMem10_size]⟩)
    _ = UInt256.toByteArray domainWord := by
      simpa [permitDigestMem10] using
        permitWordMem_read_back (permitDigestMem9 I domainWord) 386 domainWord
          (by rw [permitDigestMem9_size]; native_decide)

theorem permitDigestMem11_read418 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitDigestMem11 I domainWord).readWithPadding 418 32 =
      UInt256.toByteArray (permitStructHashMemWord I) := by
  simpa [permitDigestMem11] using
    permitWordMem_read_back (permitDigestMem10 I domainWord) 418 (permitStructHashMemWord I)
      (by rw [permitDigestMem10_size]; native_decide)

theorem permitDigestMem11_read384_66_eq (cA gh bl σ σ₀ A I) (g : Sat256) :
    ((permitDigestMem11 I
      (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner domainSeparatorStorageSlot))
        |>.readWithPadding 384 66) =
      permitDigestPackedByteArray (initState cA gh bl σ σ₀ g A I) I := by
  let domainWord :=
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner domainSeparatorStorageSlot
  change (permitDigestMem11 I domainWord).readWithPadding 384 66 =
    permitDigestPackedByteArray (initState cA gh bl σ σ₀ g A I) I
  have hstructBytes :
      UInt256.toByteArray (permitStructHashMemWord I) =
        (permitStructHashBytes I).toByteArray := by
    have hstruct : permitStructHashMemWord I = permitStructHashWord I := by
      unfold permitStructHashMemWord permitStructHashWord
      rw [permitDigestMem8_read160_192_eq]
      rw [uInt256OfByteArray_eq]
    rw [hstruct]
    rw [← word_toBytesBE_toByteArray_eq_toByteArray (permitStructHashWord I)]
    rw [permitStructHashWord_toBytesBE]
  have h0 :
      (permitDigestMem11 I domainWord).readWithPadding 384 (2 + 64) =
        (permitDigestMem11 I domainWord).readWithPadding 384 2 ++
          (permitDigestMem11 I domainWord).readWithPadding (384 + 2) 64 :=
    byteArray_readWithPadding_split (permitDigestMem11 I domainWord) 384 2 64
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [permitDigestMem11_size])
  have h1 :
      (permitDigestMem11 I domainWord).readWithPadding 386 (32 + 32) =
        (permitDigestMem11 I domainWord).readWithPadding 386 32 ++
          (permitDigestMem11 I domainWord).readWithPadding (386 + 32) 32 :=
    byteArray_readWithPadding_split (permitDigestMem11 I domainWord) 386 32 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [permitDigestMem11_size])
  rw [show 66 = 2 + 64 by norm_num, h0]
  rw [show 64 = 32 + 32 by norm_num, h1]
  rw [permitDigestMem11_read384_2, permitDigestMem11_read386, permitDigestMem11_read418]
  rw [hstructBytes]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray domainWord]
  dsimp [domainWord]
  unfold permitDigestPackedByteArray
  rw [← ByteArray.append_assoc]
  rw [← List.toByteArray_append]

theorem permitDigestMem13_read384_66_eq (cA gh bl σ σ₀ A I) (g : Sat256) :
    ((permitDigestMem13 I
      (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner domainSeparatorStorageSlot))
        |>.readWithPadding 384 66) =
      permitDigestPackedByteArray (initState cA gh bl σ σ₀ g A I) I := by
  rw [permitDigestMem13_read384_66]
  exact permitDigestMem11_read384_66_eq cA gh bl σ σ₀ A I g

theorem permitDigestWord_from_mem13 (cA gh bl σ σ₀ A I) (g : Sat256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((permitDigestMem13 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)).readWithPadding 384 66))) =
      permitDigestWord (initState cA gh bl σ σ₀ g A I) I := by
  rw [permitDigestMem13_read384_66_eq]
  unfold permitDigestWord
  rw [uInt256OfByteArray_eq]

theorem permitRWord_toByteArray {I : ExecutionEnv} (hsz260 : 260 ≤ I.calldata.size) :
    UInt256.toByteArray (permitRWord I) = (permitRBytes I).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq (UInt256.toByteArray (permitRWord I)),
    ← byteArray_toList_eq ((permitRBytes I).toByteArray)]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (permitRWord I)]
  rw [byteArray_toList_eq ((EVM.Word.toBytesBE (permitRWord I)).toByteArray),
    byteArray_toList_eq ((permitRBytes I).toByteArray)]
  rw [List.toList_data_toByteArray, List.toList_data_toByteArray]
  rw [toBytesBE_uInt256OfByteArray_of_size]
  · unfold permitRBytes
    rw [byteArray_toList_eq, readBytes_at_toList_any]
    · simp [byteArray_toList_eq]
    · omega
  · have hlist := readBytes_at_toList_any I.calldata 196
      (by omega : 196 + 32 ≤ I.calldata.size)
    have hcalldataLen : I.calldata.data.toList.length = I.calldata.size := by
      rw [Array.length_toList]
      rfl
    have hlen : (I.calldata.readBytes 196 32).toList.length = 32 := by
      rw [byteArray_toList_eq, hlist, List.length_take, List.length_drop]
      rw [hcalldataLen]
      omega
    simpa [byteArray_toList_eq] using hlen

theorem permitSWord_toByteArray {I : ExecutionEnv} (hsz260 : 260 ≤ I.calldata.size) :
    UInt256.toByteArray (permitSWord I) = (permitSBytes I).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq (UInt256.toByteArray (permitSWord I)),
    ← byteArray_toList_eq ((permitSBytes I).toByteArray)]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (permitSWord I)]
  rw [byteArray_toList_eq ((EVM.Word.toBytesBE (permitSWord I)).toByteArray),
    byteArray_toList_eq ((permitSBytes I).toByteArray)]
  rw [List.toList_data_toByteArray, List.toList_data_toByteArray]
  rw [toBytesBE_uInt256OfByteArray_of_size]
  · unfold permitSBytes
    rw [byteArray_toList_eq, readBytes_at_toList_any]
    · simp [byteArray_toList_eq]
    · omega
  · have hlist := readBytes_at_toList_any I.calldata 228
      (by omega : 228 + 32 ≤ I.calldata.size)
    have hcalldataLen : I.calldata.data.toList.length = I.calldata.size := by
      rw [Array.length_toList]
      rfl
    have hlen : (I.calldata.readBytes 228 32).toList.length = 32 := by
      rw [byteArray_toList_eq, hlist, List.length_take, List.length_drop]
      rw [hcalldataLen]
      omega
    simpa [byteArray_toList_eq] using hlen

theorem permitVMaskedWord_mask (I : ExecutionEnv) :
    UInt256.land (⟨255⟩ : UInt256) (permitVMaskedWord I) = permitVMaskedWord I := by
  unfold permitVMaskedWord
  apply u256_inj
  repeat rw [uland_toNat]
  change 255 &&& ((permitVWord I).toNat &&& 255) = (permitVWord I).toNat &&& 255
  rw [← Nat.and_assoc]
  rw [show 255 &&& (permitVWord I).toNat = (permitVWord I).toNat &&& 255 by
    rw [Nat.and_comm]]
  rw [Nat.and_assoc]
  rw [show 255 &&& 255 = 255 by native_decide]

noncomputable abbrev permitEcrecoverMem0 (I : ExecutionEnv) (domainWord : UInt256) :
    ByteArray :=
  permitWordMem (permitDigestMem13 I domainWord) 450 (⟨0⟩ : UInt256)

noncomputable abbrev permitEcrecoverMem1 (I : ExecutionEnv) (domainWord : UInt256) :
    ByteArray :=
  permitWordMem (permitEcrecoverMem0 I domainWord) 64 (⟨482⟩ : UInt256)

noncomputable abbrev permitEcrecoverMem2
    (I : ExecutionEnv) (domainWord digestWord : UInt256) : ByteArray :=
  permitWordMem (permitEcrecoverMem1 I domainWord) 482 digestWord

noncomputable abbrev permitEcrecoverMem3
    (I : ExecutionEnv) (domainWord digestWord : UInt256) : ByteArray :=
  permitWordMem (permitEcrecoverMem2 I domainWord digestWord) 514 (permitVMaskedWord I)

noncomputable abbrev permitEcrecoverMem4
    (I : ExecutionEnv) (domainWord digestWord : UInt256) : ByteArray :=
  permitWordMem (permitEcrecoverMem3 I domainWord digestWord) 546 (permitRWord I)

noncomputable abbrev permitEcrecoverMem5
    (I : ExecutionEnv) (domainWord digestWord : UInt256) : ByteArray :=
  permitWordMem (permitEcrecoverMem4 I domainWord digestWord) 578 (permitSWord I)

theorem permitEcrecoverMem0_size (I : ExecutionEnv) (domainWord : UInt256) :
    (permitEcrecoverMem0 I domainWord).size = 482 := by
  unfold permitEcrecoverMem0
  rw [permitWordMem_size]
  · rw [permitDigestMem13_size]; norm_num
  · rw [permitDigestMem13_size]; norm_num

theorem permitEcrecoverMem1_size (I : ExecutionEnv) (domainWord : UInt256) :
    (permitEcrecoverMem1 I domainWord).size = 482 := by
  unfold permitEcrecoverMem1
  rw [permitWordMem_size]
  · rw [permitEcrecoverMem0_size]; norm_num
  · rw [permitEcrecoverMem0_size]; norm_num

theorem permitEcrecoverMem1_read64 (I : ExecutionEnv) (domainWord : UInt256) :
    (permitEcrecoverMem1 I domainWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨482⟩ : UInt256) := by
  simpa [permitEcrecoverMem1] using
    permitWordMem_read_back (permitEcrecoverMem0 I domainWord) 64 (⟨482⟩ : UInt256)
      (by rw [permitEcrecoverMem0_size]; norm_num)

theorem permitEcrecoverMem1_mload64 (I : ExecutionEnv) (domainWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (permitEcrecoverMem1 I domainWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 16 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitEcrecoverMem1 I domainWord).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨482⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 16) (v := (⟨482⟩ : UInt256))
    (by rw [permitEcrecoverMem1_size]; decide)
    (by decide)
    (by simpa using permitEcrecoverMem1_read64 I domainWord)

theorem permitEcrecoverMem2_size
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem2 I domainWord digestWord).size = 514 := by
  unfold permitEcrecoverMem2
  rw [permitWordMem_size]
  · rw [permitEcrecoverMem1_size]; norm_num
  · rw [permitEcrecoverMem1_size]; norm_num

theorem permitEcrecoverMem3_size
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem3 I domainWord digestWord).size = 546 := by
  unfold permitEcrecoverMem3
  rw [permitWordMem_size]
  · rw [permitEcrecoverMem2_size]; norm_num
  · rw [permitEcrecoverMem2_size]; norm_num

theorem permitEcrecoverMem4_size
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem4 I domainWord digestWord).size = 578 := by
  unfold permitEcrecoverMem4
  rw [permitWordMem_size]
  · rw [permitEcrecoverMem3_size]; norm_num
  · rw [permitEcrecoverMem3_size]; norm_num

theorem permitEcrecoverMem5_size
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem5 I domainWord digestWord).size = 610 := by
  unfold permitEcrecoverMem5
  rw [permitWordMem_size]
  · rw [permitEcrecoverMem4_size]; norm_num
  · rw [permitEcrecoverMem4_size]; norm_num

theorem permitEcrecoverMem5_read64
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨482⟩ : UInt256) := by
  calc
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 64 32 =
        (permitEcrecoverMem4 I domainWord digestWord).readWithPadding 64 32 := by
      simpa [permitEcrecoverMem5] using
        permitWordMem_read64_preserve
          (mem := permitEcrecoverMem4 I domainWord digestWord) (off := 578)
          (word := permitSWord I)
          (hsize := by rw [permitEcrecoverMem4_size]; norm_num)
          (hoff := by norm_num)
          (hgap := by rw [permitEcrecoverMem4_size]; norm_num)
    _ = (permitEcrecoverMem3 I domainWord digestWord).readWithPadding 64 32 := by
      simpa [permitEcrecoverMem4] using
        permitWordMem_read64_preserve
          (mem := permitEcrecoverMem3 I domainWord digestWord) (off := 546)
          (word := permitRWord I)
          (hsize := by rw [permitEcrecoverMem3_size]; norm_num)
          (hoff := by norm_num)
          (hgap := by rw [permitEcrecoverMem3_size]; norm_num)
    _ = (permitEcrecoverMem2 I domainWord digestWord).readWithPadding 64 32 := by
      simpa [permitEcrecoverMem3] using
        permitWordMem_read64_preserve
          (mem := permitEcrecoverMem2 I domainWord digestWord) (off := 514)
          (word := permitVMaskedWord I)
          (hsize := by rw [permitEcrecoverMem2_size]; norm_num)
          (hoff := by norm_num)
          (hgap := by rw [permitEcrecoverMem2_size]; norm_num)
    _ = (permitEcrecoverMem1 I domainWord).readWithPadding 64 32 := by
      simpa [permitEcrecoverMem2] using
        permitWordMem_read64_preserve
          (mem := permitEcrecoverMem1 I domainWord) (off := 482)
          (word := digestWord)
          (hsize := by rw [permitEcrecoverMem1_size]; norm_num)
          (hoff := by norm_num)
          (hgap := by rw [permitEcrecoverMem1_size]; norm_num)
    _ = UInt256.toByteArray (⟨482⟩ : UInt256) := by
      simpa [permitEcrecoverMem1] using
        permitWordMem_read_back (permitEcrecoverMem0 I domainWord) 64 (⟨482⟩ : UInt256)
          (by rw [permitEcrecoverMem0_size]; norm_num)

theorem permitEcrecoverMem5_mload64
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (permitEcrecoverMem5 I domainWord digestWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitEcrecoverMem5 I domainWord digestWord).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨482⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 20) (v := (⟨482⟩ : UInt256))
    (by rw [permitEcrecoverMem5_size]; decide)
    (by decide)
    (by simpa using permitEcrecoverMem5_read64 I domainWord digestWord)

theorem permitEcrecoverMem5_read482
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 482 32 =
      UInt256.toByteArray digestWord := by
  calc
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 482 32 =
        (permitEcrecoverMem4 I domainWord digestWord).readWithPadding 482 32 := by
      simpa [permitEcrecoverMem5] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem4 I domainWord digestWord) (off := 578)
          (read := 482) (word := permitSWord I)
          (hgap := by rw [permitEcrecoverMem4_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitEcrecoverMem4_size]⟩)
    _ = (permitEcrecoverMem3 I domainWord digestWord).readWithPadding 482 32 := by
      simpa [permitEcrecoverMem4] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem3 I domainWord digestWord) (off := 546)
          (read := 482) (word := permitRWord I)
          (hgap := by rw [permitEcrecoverMem3_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitEcrecoverMem3_size]⟩)
    _ = (permitEcrecoverMem2 I domainWord digestWord).readWithPadding 482 32 := by
      simpa [permitEcrecoverMem3] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem2 I domainWord digestWord) (off := 514)
          (read := 482) (word := permitVMaskedWord I)
          (hgap := by rw [permitEcrecoverMem2_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitEcrecoverMem2_size]⟩)
    _ = UInt256.toByteArray digestWord := by
      simpa [permitEcrecoverMem2] using
        permitWordMem_read_back (permitEcrecoverMem1 I domainWord) 482 digestWord
          (by rw [permitEcrecoverMem1_size]; norm_num)

theorem permitEcrecoverMem5_read514
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 514 32 =
      UInt256.toByteArray (permitVMaskedWord I) := by
  calc
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 514 32 =
        (permitEcrecoverMem4 I domainWord digestWord).readWithPadding 514 32 := by
      simpa [permitEcrecoverMem5] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem4 I domainWord digestWord) (off := 578)
          (read := 514) (word := permitSWord I)
          (hgap := by rw [permitEcrecoverMem4_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitEcrecoverMem4_size]⟩)
    _ = (permitEcrecoverMem3 I domainWord digestWord).readWithPadding 514 32 := by
      simpa [permitEcrecoverMem4] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem3 I domainWord digestWord) (off := 546)
          (read := 514) (word := permitRWord I)
          (hgap := by rw [permitEcrecoverMem3_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitEcrecoverMem3_size]⟩)
    _ = UInt256.toByteArray (permitVMaskedWord I) := by
      simpa [permitEcrecoverMem3] using
        permitWordMem_read_back (permitEcrecoverMem2 I domainWord digestWord) 514
          (permitVMaskedWord I) (by rw [permitEcrecoverMem2_size]; norm_num)

theorem permitEcrecoverMem5_read546
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 546 32 =
      UInt256.toByteArray (permitRWord I) := by
  calc
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 546 32 =
        (permitEcrecoverMem4 I domainWord digestWord).readWithPadding 546 32 := by
      simpa [permitEcrecoverMem5] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem4 I domainWord digestWord) (off := 578)
          (read := 546) (word := permitSWord I)
          (hgap := by rw [permitEcrecoverMem4_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by simpa [permitEcrecoverMem4_size]⟩)
    _ = UInt256.toByteArray (permitRWord I) := by
      simpa [permitEcrecoverMem4] using
        permitWordMem_read_back (permitEcrecoverMem3 I domainWord digestWord) 546
          (permitRWord I) (by rw [permitEcrecoverMem3_size]; norm_num)

theorem permitEcrecoverMem5_read578
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 578 32 =
      UInt256.toByteArray (permitSWord I) := by
  simpa [permitEcrecoverMem5] using
    permitWordMem_read_back (permitEcrecoverMem4 I domainWord digestWord) 578
      (permitSWord I) (by rw [permitEcrecoverMem4_size]; norm_num)

theorem permitEcrecoverMem5_read482_128 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz260 : 260 ≤ I.calldata.size) :
    (permitEcrecoverMem5 I
      (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner domainSeparatorStorageSlot)
      (permitDigestWord (initState cA gh bl σ σ₀ g A I) I)).readWithPadding 482 128 =
      permitEcrecoverCalldata (initState cA gh bl σ σ₀ g A I) I := by
  let evm := initState cA gh bl σ σ₀ g A I
  let domainWord :=
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner domainSeparatorStorageSlot
  let digestWord := permitDigestWord evm I
  let mem := permitEcrecoverMem5 I domainWord digestWord
  change mem.readWithPadding 482 128 = permitEcrecoverCalldata evm I
  have hsplit0 :
      mem.readWithPadding 482 (32 + 96) =
        mem.readWithPadding 482 32 ++ mem.readWithPadding (482 + 32) 96 :=
    byteArray_readWithPadding_split mem 482 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by
        change 482 + 32 + 96 ≤ (permitEcrecoverMem5 I domainWord digestWord).size
        simpa [permitEcrecoverMem5_size])
  have hsplit1 :
      mem.readWithPadding 514 (32 + 64) =
        mem.readWithPadding 514 32 ++ mem.readWithPadding (514 + 32) 64 :=
    byteArray_readWithPadding_split mem 514 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by
        change 514 + 32 + 64 ≤ (permitEcrecoverMem5 I domainWord digestWord).size
        simpa [permitEcrecoverMem5_size])
  have hsplit2 :
      mem.readWithPadding 546 (32 + 32) =
        mem.readWithPadding 546 32 ++ mem.readWithPadding (546 + 32) 32 :=
    byteArray_readWithPadding_split mem 546 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by
        change 546 + 32 + 32 ≤ (permitEcrecoverMem5 I domainWord digestWord).size
        simpa [permitEcrecoverMem5_size])
  rw [show 128 = 32 + 96 by norm_num]
  rw [hsplit0]
  rw [show 96 = 32 + 64 by norm_num]
  rw [hsplit1]
  rw [show 64 = 32 + 32 by norm_num]
  rw [hsplit2]
  rw [permitEcrecoverMem5_read482, permitEcrecoverMem5_read514,
    permitEcrecoverMem5_read546, permitEcrecoverMem5_read578]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray digestWord]
  rw [permitDigestWord_toBytesBE]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (permitVMaskedWord I)]
  rw [permitRWord_toByteArray hsz260, permitSWord_toByteArray hsz260]

end Benchmarks.Dss.Dai

namespace Reasoning.Theory

theorem dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length -
          12 + 13 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk ::
              ll :: mm :: nn :: oo :: pp :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
            mm :: nn :: oo :: pp :: t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.dup12_xstep hc hp hdec hs hov)

theorem RD.dup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk ::
        ll :: mm :: nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.dup16_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.Dss.Dai

theorem permitHolderMaskedWord_canonical (I : ExecutionEnv) :
    (permitHolderMaskedWord I).toNat < EVM.addressModulus := by
  unfold permitHolderMaskedWord
  rw [u256_land_comm solcAddrMask (permitHolderWord I)]
  exact solcAddrMask_result_canonical (permitHolderWord I)

theorem permitSpenderMaskedWord_canonical (I : ExecutionEnv) :
    (permitSpenderMaskedWord I).toNat < EVM.addressModulus := by
  unfold permitSpenderMaskedWord
  rw [u256_land_comm solcAddrMask (permitSpenderWord I)]
  exact solcAddrMask_result_canonical (permitSpenderWord I)

set_option maxHeartbeats 1000000 in
theorem daiPermitX_holderZeroRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz260 : 260 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hz : permitHolderMaskedWord I = ⟨0⟩)
    (hreach : ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨810⟩
      [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2428⟩ := daiPermitX_decoded hsz260 hsize hreach
  obtain ⟨_, _, rd2432raw⟩ := (evm_run rd2428 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov)]).sload (by native_decide) (by evm_ov)
  have rd2432 := by
    simpa [domainSeparatorStorageSlot, initState, Solm.EVM.storageLoad] using rd2432raw
  let domainWord :=
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner domainSeparatorStorageSlot
  let mem1 := permitStructMem1 I
  let mem2 := permitStructMem2 I
  let mem3 := permitStructMem3 I
  let mem4 := permitStructMem4 I
  let mem5 := permitStructMem5 I
  let mem6 := permitStructMem6 I
  have rd2436pre := evm_run rd2432 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
        solcFreePtrMem_read64) (by decide) (by evm_ov)]
  have rd2469 := rd2436pre.pushConst permitTypehashWordLit (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd2477pre := evm_run rd2469 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2478 := evm_run rd2477pre with [
    raw mstore 9 mem1 (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hholderMask :
      UInt256.land (permitHolderMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        permitHolderMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (permitHolderMaskedWord_canonical I)
  have rd2489pre := evm_run rd2478 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup14 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hholderMask] at rd2489pre
  have rd2495 := evm_run rd2489pre with [
    raw dup4 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hspenderMask :
      UInt256.land (permitSpenderMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        permitSpenderMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (permitSpenderMaskedWord_canonical I)
  have rd2498pre := evm_run rd2495 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup13 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hspenderMask] at rd2498pre
  have rd2503 := evm_run rd2498pre with [
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2507 := evm_run rd2503 with [
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd2508 := Reasoning.Reach.RD.dup12 rd2507 (by native_decide) (by evm_ov)
  have rd2510 := evm_run rd2508 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 mem4 (UInt256.ofNat 9) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2517 := evm_run rd2510 with [
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 mem5 (UInt256.ofNat 10) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2529 := evm_run rd2517 with [
    raw dup9 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 3 mem6 (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  let mem7 := permitDigestMem7 I
  let mem8 := permitDigestMem8 I
  let structHash := permitStructHashMemWord I
  let eip191Word := permitEip191Word
  let mem9 := permitDigestMem9 I domainWord
  let mem10 := permitDigestMem10 I domainWord
  let mem11 := permitDigestMem11 I domainWord
  let mem12 := permitDigestMem12 I domainWord
  let mem13 := permitDigestMem13 I domainWord
  let digestWord :=
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem11.readWithPadding 384 66)))
  have rd2539 := evm_run rd2529 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost (by simpa [mem6] using permitStructMem6_mload64 I) (by native_decide)
        (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 mem7 (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2545 := evm_run rd2539 with [
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw mstore 0 mem8 (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2550pre := evm_run rd2545 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨192⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost (by simpa [mem8] using permitDigestMem8_mload128 I) (by native_decide)
        (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd2551 := rd2550pre.keccak256 0 structHash (UInt256.ofNat 11) (by native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2563 := evm_run rd2551 with [
    raw push2 ⟨6401⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨240⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 6 mem9 (UInt256.ofNat 13) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2572 := evm_run rd2563 with [
    raw push2 ⟨258⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw mstore 3 mem10 (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2582 := evm_run rd2572 with [
    raw push2 ⟨290⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw mstore 3 mem11 (UInt256.ofNat 15) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2601 := evm_run rd2582 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨352⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (by simpa [mem11] using permitDigestMem11_mload64 I domainWord)
        (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw mstore 0 mem12 (UInt256.ofNat 15) (by native_decide)
      mem_cost (by
        have hword :
            ((⟨290⟩ : UInt256) + (⟨128⟩ : UInt256).sub (⟨352⟩ : UInt256)) =
              (⟨66⟩ : UInt256) := by native_decide
        rw [hword]
        rw [show (⟨352⟩ : UInt256).toNat = 352 from by native_decide]
        change (UInt256.toByteArray (⟨66⟩ : UInt256)).write 0 mem11 352 32 = mem12
        rfl)
        (by native_decide) (by evm_ov),
    raw push2 ⟨322⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mstore 0 mem13 (UInt256.ofNat 15) (by native_decide)
      mem_cost (by
        have hword : ((⟨128⟩ : UInt256) + (⟨322⟩ : UInt256)) =
            (⟨450⟩ : UInt256) := by native_decide
        rw [hword]
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
        change (UInt256.toByteArray (⟨450⟩ : UInt256)).write 0 mem12 64 32 = mem13
        rfl)
        (by native_decide) (by evm_ov)]
  have rd2611 := evm_run rd2601 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨66⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (by simpa [mem13] using permitDigestMem13_mload352 I domainWord)
        (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2611hash := rd2611.keccak256 0 digestWord (UInt256.ofNat 15) (by native_decide)
    mem_cost (by
      unfold digestWord
      rw [show ((⟨32⟩ : UInt256) + (⟨352⟩ : UInt256)).toNat = 384 from by
          native_decide,
        show (⟨66⟩ : UInt256).toNat = 66 from by native_decide,
        show mem13.readWithPadding 384 66 = mem11.readWithPadding 384 66 from by
        simpa [mem13, mem11] using permitDigestMem13_read384_66 I domainWord])
    (by native_decide) (by evm_ov)
  rw [hz] at rd2611hash
  have rd2615 := evm_run rd2611hash with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2684⟩ (by native_decide) (by evm_ov)]
  have rd2616 := rd2615.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  let err0 := permitWordMem mem13 450 solcErrorStringSelector
  let err1 := permitWordMem err0 454 (⟨32⟩ : UInt256)
  let err2 := permitWordMem err1 486 (⟨21⟩ : UInt256)
  let err3 := permitWordMem err2 518 permitInvalidAddress0Word
  have hmem13_size : mem13.size = 450 := by
    simpa [mem13] using permitDigestMem13_size I domainWord
  have hmem13_read64 :
      mem13.readWithPadding 64 32 = UInt256.toByteArray (⟨450⟩ : UInt256) := by
    simpa [mem13] using permitDigestMem13_read64 I domainWord
  have herr0_size : err0.size = 482 := by
    unfold err0
    rw [permitWordMem_size]
    · rw [hmem13_size]; native_decide
    · rw [hmem13_size]; native_decide
  have herr1_size : err1.size = 486 := by
    unfold err1
    rw [permitWordMem_size]
    · rw [herr0_size]; native_decide
    · rw [herr0_size]; native_decide
  have herr2_size : err2.size = 518 := by
    unfold err2
    rw [permitWordMem_size]
    · rw [herr1_size]; native_decide
    · rw [herr1_size]; native_decide
  have herr3_size : err3.size = 550 := by
    unfold err3
    rw [permitWordMem_size]
    · rw [herr2_size]; native_decide
    · rw [herr2_size]; native_decide
  have herr0_read64 :
      err0.readWithPadding 64 32 = UInt256.toByteArray (⟨450⟩ : UInt256) := by
    simpa [err0] using
      permitWordMem_read64_preserve (mem := mem13) (off := 450)
        (word := solcErrorStringSelector)
        (hsize := by rw [hmem13_size]; norm_num)
        (hoff := by norm_num)
        (hgap := by rw [hmem13_size]; native_decide) |>.trans hmem13_read64
  have herr1_read64 :
      err1.readWithPadding 64 32 = UInt256.toByteArray (⟨450⟩ : UInt256) := by
    simpa [err1] using
      permitWordMem_read64_preserve (mem := err0) (off := 454)
        (word := (⟨32⟩ : UInt256))
        (hsize := by rw [herr0_size]; norm_num)
        (hoff := by norm_num)
        (hgap := by rw [herr0_size]; native_decide) |>.trans herr0_read64
  have herr2_read64 :
      err2.readWithPadding 64 32 = UInt256.toByteArray (⟨450⟩ : UInt256) := by
    simpa [err2] using
      permitWordMem_read64_preserve (mem := err1) (off := 486)
        (word := (⟨21⟩ : UInt256))
        (hsize := by rw [herr1_size]; norm_num)
        (hoff := by norm_num)
        (hgap := by rw [herr1_size]; native_decide) |>.trans herr1_read64
  have herr3_read64 :
      err3.readWithPadding 64 32 = UInt256.toByteArray (⟨450⟩ : UInt256) := by
    simpa [err3] using
      permitWordMem_read64_preserve (mem := err2) (off := 518)
        (word := permitInvalidAddress0Word)
        (hsize := by rw [herr2_size]; norm_num)
        (hoff := by norm_num)
        (hgap := by rw [herr2_size]; native_decide) |>.trans herr2_read64
  have herr3_mload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ err3.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (err3.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨450⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 18) (v := (⟨450⟩ : UInt256))
      (by rw [herr3_size]; decide)
      (by decide)
      (by simpa using herr3_read64)
  have rdErrMload := evm_run rd2616 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨450⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (by simpa [mem13] using permitDigestMem13_mload64 I domainWord)
      (by native_decide) (by evm_ov)]
  have rdErrSelectorRaw := rdErrMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rdErrSelector := evm_run rdErrSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [show UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩ =
      solcErrorStringSelector from rfl] at rdErrSelector
  have rdErrPrefix := evm_run rdErrSelector with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 err0 (UInt256.ofNat 16) (by native_decide)
      mem_cost (by
        rw [show (⟨450⟩ : UInt256).toNat = 450 from by native_decide]
        simp [err0, permitWordMem, Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 err1 (UInt256.ofNat 16) (by native_decide)
      mem_cost (by
        rw [show ((⟨450⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 454 from by
          native_decide]
        simp [err1, permitWordMem, Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨21⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 err2 (UInt256.ofNat 17) (by native_decide)
      mem_cost (by
        rw [show ((⟨450⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 486 from by
          native_decide]
        simp [err2, permitWordMem, Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov)]
  have rdErrRaw := rdErrPrefix.pushConst permitInvalidAddress0RawWord
    (width := 21) (op := .PUSH21) (by decide) (by native_decide) (by evm_ov)
  have rdErrWord := evm_run rdErrRaw with [
    raw push1 ⟨92⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [permitInvalidAddress0Word_shift] at rdErrWord
  exact evm_run rdErrWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 err3 (UInt256.ofNat 18) (by native_decide)
      mem_cost (by
        rw [show ((⟨450⟩ : UInt256) + (⟨68⟩ : UInt256)).toNat = 518 from by
          native_decide]
        simp [err3, permitWordMem, Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨450⟩ (UInt256.ofNat 18) (by native_decide)
      mem_cost herr3_mload64 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem daiPermitX_nonzeroHolderReach2684 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz260 : 260 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnz : permitHolderMaskedWord I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨810⟩
      [daiSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2684⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitDigestMem13 I
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          domainSeparatorStorageSlot))
      (UInt256.ofNat 15) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2428⟩ := daiPermitX_decoded hsz260 hsize hreach
  obtain ⟨_, _, rd2432raw⟩ := (evm_run rd2428 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov)]).sload (by native_decide) (by evm_ov)
  have rd2432 := by
    simpa [domainSeparatorStorageSlot, initState, Solm.EVM.storageLoad] using rd2432raw
  let domainWord :=
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner domainSeparatorStorageSlot
  let mem1 := permitStructMem1 I
  let mem2 := permitStructMem2 I
  let mem3 := permitStructMem3 I
  let mem4 := permitStructMem4 I
  let mem5 := permitStructMem5 I
  let mem6 := permitStructMem6 I
  have rd2436pre := evm_run rd2432 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
        solcFreePtrMem_read64) (by decide) (by evm_ov)]
  have rd2469 := rd2436pre.pushConst permitTypehashWordLit (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd2477pre := evm_run rd2469 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2478 := evm_run rd2477pre with [
    raw mstore 9 mem1 (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hholderMask :
      UInt256.land (permitHolderMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        permitHolderMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (permitHolderMaskedWord_canonical I)
  have rd2489pre := evm_run rd2478 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup14 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hholderMask] at rd2489pre
  have rd2495 := evm_run rd2489pre with [
    raw dup4 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hspenderMask :
      UInt256.land (permitSpenderMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        permitSpenderMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (permitSpenderMaskedWord_canonical I)
  have rd2498pre := evm_run rd2495 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup13 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hspenderMask] at rd2498pre
  have rd2503 := evm_run rd2498pre with [
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2507 := evm_run rd2503 with [
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd2508 := Reasoning.Reach.RD.dup12 rd2507 (by native_decide) (by evm_ov)
  have rd2510 := evm_run rd2508 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 mem4 (UInt256.ofNat 9) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2517 := evm_run rd2510 with [
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 mem5 (UInt256.ofNat 10) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2529 := evm_run rd2517 with [
    raw dup9 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 3 mem6 (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  let mem7 := permitDigestMem7 I
  let mem8 := permitDigestMem8 I
  let structHash := permitStructHashMemWord I
  let mem9 := permitDigestMem9 I domainWord
  let mem10 := permitDigestMem10 I domainWord
  let mem11 := permitDigestMem11 I domainWord
  let mem12 := permitDigestMem12 I domainWord
  let mem13 := permitDigestMem13 I domainWord
  let digestWord :=
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem11.readWithPadding 384 66)))
  have rd2539 := evm_run rd2529 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost (by simpa [mem6] using permitStructMem6_mload64 I) (by native_decide)
        (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 mem7 (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2545 := evm_run rd2539 with [
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw mstore 0 mem8 (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2550pre := evm_run rd2545 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨192⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost (by simpa [mem8] using permitDigestMem8_mload128 I) (by native_decide)
        (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd2551 := rd2550pre.keccak256 0 structHash (UInt256.ofNat 11) (by native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2563 := evm_run rd2551 with [
    raw push2 ⟨6401⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨240⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 6 mem9 (UInt256.ofNat 13) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2572 := evm_run rd2563 with [
    raw push2 ⟨258⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw mstore 3 mem10 (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2582 := evm_run rd2572 with [
    raw push2 ⟨290⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw mstore 3 mem11 (UInt256.ofNat 15) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2601 := evm_run rd2582 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨352⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (by simpa [mem11] using permitDigestMem11_mload64 I domainWord)
        (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw mstore 0 mem12 (UInt256.ofNat 15) (by native_decide)
      mem_cost (by
        have hword :
            ((⟨290⟩ : UInt256) + (⟨128⟩ : UInt256).sub (⟨352⟩ : UInt256)) =
              (⟨66⟩ : UInt256) := by native_decide
        rw [hword]
        rw [show (⟨352⟩ : UInt256).toNat = 352 from by native_decide]
        change (UInt256.toByteArray (⟨66⟩ : UInt256)).write 0 mem11 352 32 = mem12
        rfl)
        (by native_decide) (by evm_ov),
    raw push2 ⟨322⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mstore 0 mem13 (UInt256.ofNat 15) (by native_decide)
      mem_cost (by
        have hword : ((⟨128⟩ : UInt256) + (⟨322⟩ : UInt256)) =
            (⟨450⟩ : UInt256) := by native_decide
        rw [hword]
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
        change (UInt256.toByteArray (⟨450⟩ : UInt256)).write 0 mem12 64 32 = mem13
        rfl)
        (by native_decide) (by evm_ov)]
  have rd2611 := evm_run rd2601 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨66⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (by simpa [mem13] using permitDigestMem13_mload352 I domainWord)
        (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2611hash := rd2611.keccak256 0 digestWord (UInt256.ofNat 15) (by native_decide)
    mem_cost (by
      unfold digestWord
      rw [show ((⟨32⟩ : UInt256) + (⟨352⟩ : UInt256)).toNat = 384 from by
          native_decide,
        show (⟨66⟩ : UInt256).toNat = 66 from by native_decide,
        show mem13.readWithPadding 384 66 = mem11.readWithPadding 384 66 from by
        simpa [mem13, mem11] using permitDigestMem13_read384_66 I domainWord])
    (by native_decide) (by evm_ov)
  have hdigest :
      digestWord = permitDigestWord (initState cA gh bl σ σ₀ g A I) I := by
    unfold digestWord
    rw [← permitDigestMem13_read384_66 I domainWord]
    simpa [domainWord] using permitDigestWord_from_mem13 cA gh bl σ σ₀ A I g
  rw [hdigest] at rd2611hash
  have rd2615 := evm_run rd2611hash with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2684⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd2615.jumpiT (by native_decide) hnz (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiPermitX_nonzeroHolderToStaticcallFrom2684 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ}
    (rd2684 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2684⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitDigestMem13 I
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          domainSeparatorStorageSlot))
      (UInt256.ofNat 15) ByteArray.empty (cA, σ) k C) :
    ∃ gasArg k' C', RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2757⟩
      [gasArg, ⟨1⟩, ⟨482⟩, ⟨128⟩, ⟨450⟩, ⟨32⟩, ⟨610⟩, ⟨1⟩,
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverMem5 I
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          domainSeparatorStorageSlot)
        (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.ofNat 20) ByteArray.empty (cA, σ) k' C' := by
  let evm := initState cA gh bl σ σ₀ g A I
  let domainWord :=
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner domainSeparatorStorageSlot
  let digestWord := permitDigestWord evm I
  let mem0 := permitEcrecoverMem0 I domainWord
  let mem1 := permitEcrecoverMem1 I domainWord
  let mem2 := permitEcrecoverMem2 I domainWord digestWord
  let mem3 := permitEcrecoverMem3 I domainWord digestWord
  let mem4 := permitEcrecoverMem4 I domainWord digestWord
  let mem5 := permitEcrecoverMem5 I domainWord digestWord
  have rd2731 := evm_run rd2684 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨450⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (by simpa [evm, domainWord] using permitDigestMem13_mload64 I domainWord)
      (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem0 (UInt256.ofNat 16) (by native_decide)
      mem_cost (by
        rw [show (⟨450⟩ : UInt256).toNat = 450 by native_decide]
        simp [mem0, evm, domainWord, permitEcrecoverMem0, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 16) (by native_decide)
      mem_cost (by
        rw [show ((⟨32⟩ : UInt256) + ⟨450⟩) = ⟨482⟩ by native_decide]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        simp [mem0, mem1, permitEcrecoverMem1, permitWordMem, Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 16) (by native_decide)
      mem_cost (by simpa [mem1, domainWord] using permitEcrecoverMem1_mload64 I domainWord)
      (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 17) (by native_decide)
      mem_cost (by
        rw [show (⟨482⟩ : UInt256).toNat = 482 by native_decide]
        simp [evm, digestWord, mem1, mem2, permitEcrecoverMem2, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 18) (by native_decide)
      mem_cost (by
        rw [permitVMaskedWord_mask I]
        rw [show ((⟨32⟩ : UInt256) + ⟨482⟩) = ⟨514⟩ by native_decide]
        rw [show (⟨514⟩ : UInt256).toNat = 514 by native_decide]
        simp [mem2, mem3, permitEcrecoverMem2, permitEcrecoverMem3, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem4 (UInt256.ofNat 19) (by native_decide)
      mem_cost (by
        rw [show ((⟨32⟩ : UInt256) + (⟨32⟩ + ⟨482⟩)) = ⟨546⟩ by native_decide]
        rw [show (⟨546⟩ : UInt256).toNat = 546 by native_decide]
        simp [mem3, mem4, permitEcrecoverMem3, permitEcrecoverMem4, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem5 (UInt256.ofNat 20) (by native_decide)
      mem_cost (by
        rw [show ((⟨32⟩ : UInt256) + (⟨32⟩ + (⟨32⟩ + ⟨482⟩))) = ⟨578⟩ by
          native_decide]
        rw [show (⟨578⟩ : UInt256).toNat = 578 by native_decide]
        simp [mem4, mem5, permitEcrecoverMem4, permitEcrecoverMem5, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov)]
  have rd2756 := evm_run rd2731 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost (by simpa [mem5, domainWord, digestWord] using
        permitEcrecoverMem5_mload64 I domainWord digestWord)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  obtain ⟨gasArg, rd2757⟩ := RD.gas rd2756 (by native_decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [evm, domainWord, digestWord] using rd2757⟩

set_option maxHeartbeats 1000000 in
theorem daiPermitX_nonzeroHolderStaticcallFrom2684 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ}
    (hsz260 : 260 ≤ I.calldata.size) (hdepth : I.depth.val < 1024)
    (rd2684 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2684⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitDigestMem13 I
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          domainSeparatorStorageSlot))
      (UInt256.ofNat 15) ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          (permitEcrecoverCalldata (initState cA gh bl σ σ₀ g A I) I)
          (I.depth + 1) I.header false)
      ∧ RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2758⟩
          ((if z then (⟨1⟩ : UInt256) else ⟨0⟩) ::
            [⟨610⟩, ⟨1⟩, permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
              permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
              permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
              permitHolderMaskedWord I, ⟨686⟩, daiSelWord I])
          (o.write 0
            (permitEcrecoverMem5 I
              (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
                (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
                domainSeparatorStorageSlot)
              (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
            (⟨450⟩ : UInt256).toNat
            (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat
            (MachineState.M
              (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
                (⟨128⟩ : UInt256).toNat)
              (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  let evm := initState cA gh bl σ σ₀ g A I
  let domainWord :=
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner domainSeparatorStorageSlot
  let digestWord := permitDigestWord evm I
  let mem0 := permitEcrecoverMem0 I domainWord
  let mem1 := permitEcrecoverMem1 I domainWord
  let mem2 := permitEcrecoverMem2 I domainWord digestWord
  let mem3 := permitEcrecoverMem3 I domainWord digestWord
  let mem4 := permitEcrecoverMem4 I domainWord digestWord
  let mem5 := permitEcrecoverMem5 I domainWord digestWord
  have rd2731 := evm_run rd2684 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨450⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (by simpa [evm, domainWord] using permitDigestMem13_mload64 I domainWord)
      (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem0 (UInt256.ofNat 16) (by native_decide)
      mem_cost (by
        rw [show (⟨450⟩ : UInt256).toNat = 450 by native_decide]
        simp [mem0, evm, domainWord, permitEcrecoverMem0, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 16) (by native_decide)
      mem_cost (by
        rw [show ((⟨32⟩ : UInt256) + ⟨450⟩) = ⟨482⟩ by native_decide]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        simp [mem0, mem1, permitEcrecoverMem1, permitWordMem, Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 16) (by native_decide)
      mem_cost (by simpa [mem1, domainWord] using permitEcrecoverMem1_mload64 I domainWord)
      (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 17) (by native_decide)
      mem_cost (by
        rw [show (⟨482⟩ : UInt256).toNat = 482 by native_decide]
        simp [evm, digestWord, mem1, mem2, permitEcrecoverMem2, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 18) (by native_decide)
      mem_cost (by
        rw [permitVMaskedWord_mask I]
        rw [show ((⟨32⟩ : UInt256) + ⟨482⟩) = ⟨514⟩ by native_decide]
        rw [show (⟨514⟩ : UInt256).toNat = 514 by native_decide]
        simp [mem2, mem3, permitEcrecoverMem2, permitEcrecoverMem3, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem4 (UInt256.ofNat 19) (by native_decide)
      mem_cost (by
        rw [show ((⟨32⟩ : UInt256) + (⟨32⟩ + ⟨482⟩)) = ⟨546⟩ by native_decide]
        rw [show (⟨546⟩ : UInt256).toNat = 546 by native_decide]
        simp [mem3, mem4, permitEcrecoverMem3, permitEcrecoverMem4, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 mem5 (UInt256.ofNat 20) (by native_decide)
      mem_cost (by
        rw [show ((⟨32⟩ : UInt256) + (⟨32⟩ + (⟨32⟩ + ⟨482⟩))) = ⟨578⟩ by
          native_decide]
        rw [show (⟨578⟩ : UInt256).toNat = 578 by native_decide]
        simp [mem4, mem5, permitEcrecoverMem4, permitEcrecoverMem5, permitWordMem,
          Reasoning.Theory.writeWord])
      (by native_decide) (by evm_ov)]
  have rd2756 := evm_run rd2731 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost (by simpa [mem5, domainWord, digestWord] using
        permitEcrecoverMem5_mload64 I domainWord digestWord)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  obtain ⟨_gasArg, rd2757⟩ := RD.gas rd2756 (by native_decide) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd2758, hoSize⟩ :=
    RD.uniswapStaticcall rd2757 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, o, A_in, callGas, k', C', ?_, ?_, hoSize⟩
  · rcases hΘ with ⟨g'', A', hΘ⟩
    refine ⟨g'', A', ?_⟩
    have hcalldata :
        mem5.readWithPadding (⟨482⟩ : UInt256).toNat
          (((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
            ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + (⟨482⟩ : UInt256))))).sub
            (⟨482⟩ : UInt256)).toNat =
          permitEcrecoverCalldata (initState cA gh bl σ σ₀ g A I) I := by
      rw [show (⟨482⟩ : UInt256).toNat = 482 by native_decide]
      change mem5.readWithPadding 482 128 =
        permitEcrecoverCalldata (initState cA gh bl σ σ₀ g A I) I
      simpa [mem5, evm, domainWord, digestWord] using
        permitEcrecoverMem5_read482_128 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz260
    rw [hcalldata] at hΘ
    simpa [evm, initState, domainWord, digestWord] using hΘ
  · rw [show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
        ((⟨32⟩ : UInt256) + (⟨482⟩ : UInt256))))) = ⟨610⟩ by native_decide] at rd2758
    rw [show UInt256.sub (⟨482⟩ : UInt256) (⟨32⟩ : UInt256) = ⟨450⟩ by
      native_decide] at rd2758
    rw [show UInt256.sub (⟨610⟩ : UInt256) (⟨482⟩ : UInt256) = ⟨128⟩ by
      native_decide] at rd2758
    simpa [evm, domainWord, digestWord] using rd2758

theorem ecrecover_output_size (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    let r := Ξ_ECREC σ g A I
    r.2.2.2.size = 0 ∨ r.2.2.2.size = 32 := by
  unfold Ξ_ECREC
  dsimp
  split
  · left
    rfl
  · split
    · left
      rfl
    · split
      · right
        rw [ByteArray.size_append]
        rw [ByteArray_zeroes_size]
        rw [ByteArray.size_extract]
        rw [keccak_size]
        native_decide
      · left
        rfl

theorem toExecute_ecrecover_precompile (σ : AccountMap) :
    toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) =
      ToExecute.Precompiled (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) := by
  unfold toExecute
  have hmem : AccountAddress.ofUInt256 (⟨1⟩ : UInt256) ∈ π := by
    unfold π
    native_decide
  rw [if_pos hmem]

theorem permitStaticcallTheta_ecrecover_output_size
    {blobVersionedHashes cA gh bl σ σ₀ A_in r s g p v v' d e H w cA' σ' g' A' z o}
    (hΘ : (cA', σ', g', A', z, o) =
      Θ blobVersionedHashes cA gh bl σ σ₀ A_in r s
        (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
        (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
        g p v v' d e H w) :
    o.size = 0 ∨ o.size = 32 := by
  have hpre : toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) =
      ToExecute.Precompiled (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) := by
    exact toExecute_ecrecover_precompile σ
  have hone : (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) = 1 := by
    native_decide
  have hout := congrArg (fun x => x.2.2.2.2.2.size) hΘ
  have hout' :
      o.size =
        (Θ blobVersionedHashes cA gh bl σ σ₀ A_in r s
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          g p v v' d e H w).2.2.2.2.2.size := by
    simpa using hout
  rw [hout']
  unfold Θ
  rw [hpre, hone]
  dsimp
  exact ecrecover_output_size _ g A_in _

theorem daiPermitX_nonzeroHolderEcrecoverFailureAfter2758
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o mem : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (rd2758 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2758⟩
      (⟨0⟩ ::
        [⟨610⟩, ⟨1⟩, permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
          permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
          permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
          permitHolderMaskedWord I, ⟨686⟩, daiSelWord I])
      mem aw o (cA', σ') k C)
    (hoSize : o.size < UInt256.size) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (okPc := ⟨2774⟩) rd2758 rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hoSize (by simp)

abbrev permitEcrecoverReturnCopyLen (o : ByteArray) : Nat :=
  (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

noncomputable abbrev permitEcrecoverReturnMem (mem o : ByteArray) : ByteArray :=
  o.write 0 mem 450 (permitEcrecoverReturnCopyLen o)

noncomputable abbrev permitMloadWord (mem : ByteArray) (aw off : UInt256) : UInt256 :=
  if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))

abbrev permitEcrecoverStaticcallAw : UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
        (⟨128⟩ : UInt256).toNat)
      (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

theorem permitEcrecoverReturnCopyLen_empty :
    permitEcrecoverReturnCopyLen ByteArray.empty = 0 := by
  native_decide

theorem permitEcrecoverReturnMem_empty (mem : ByteArray) :
    permitEcrecoverReturnMem mem ByteArray.empty = mem := by
  simp [permitEcrecoverReturnMem, permitEcrecoverReturnCopyLen_empty, byteArray_write_len_zero]

theorem permitEcrecoverMem5_read450_zero
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 450 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  calc
    (permitEcrecoverMem5 I domainWord digestWord).readWithPadding 450 32 =
        (permitEcrecoverMem4 I domainWord digestWord).readWithPadding 450 32 := by
      simpa [permitEcrecoverMem5] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem4 I domainWord digestWord) (off := 578) (read := 450)
          (word := permitSWord I)
          (hgap := by rw [permitEcrecoverMem4_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by rw [permitEcrecoverMem4_size]; norm_num⟩)
    _ = (permitEcrecoverMem3 I domainWord digestWord).readWithPadding 450 32 := by
      simpa [permitEcrecoverMem4] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem3 I domainWord digestWord) (off := 546) (read := 450)
          (word := permitRWord I)
          (hgap := by rw [permitEcrecoverMem3_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by rw [permitEcrecoverMem3_size]; norm_num⟩)
    _ = (permitEcrecoverMem2 I domainWord digestWord).readWithPadding 450 32 := by
      simpa [permitEcrecoverMem3] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem2 I domainWord digestWord) (off := 514) (read := 450)
          (word := permitVMaskedWord I)
          (hgap := by rw [permitEcrecoverMem2_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by rw [permitEcrecoverMem2_size]; norm_num⟩)
    _ = (permitEcrecoverMem1 I domainWord).readWithPadding 450 32 := by
      simpa [permitEcrecoverMem2] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem1 I domainWord) (off := 482) (read := 450)
          (word := digestWord)
          (hgap := by rw [permitEcrecoverMem1_size]; norm_num)
          (hdisj := Or.inl ⟨by norm_num, by rw [permitEcrecoverMem1_size]⟩)
    _ = (permitEcrecoverMem0 I domainWord).readWithPadding 450 32 := by
      simpa [permitEcrecoverMem1] using
        permitWordMem_read_preserve
          (mem := permitEcrecoverMem0 I domainWord) (off := 64) (read := 450)
          (word := (⟨482⟩ : UInt256))
          (hgap := by rw [permitEcrecoverMem0_size]; norm_num)
          (hdisj := Or.inr ⟨by norm_num, by rw [permitEcrecoverMem0_size]⟩)
    _ = UInt256.toByteArray (⟨0⟩ : UInt256) := by
      simpa [permitEcrecoverMem0] using
        permitWordMem_read_back (permitDigestMem13 I domainWord) 450 (⟨0⟩ : UInt256)
          (by rw [permitDigestMem13_size]; norm_num)

theorem permitEcrecoverMem5_mload450_zero
    (I : ExecutionEnv) (domainWord digestWord : UInt256) :
    permitMloadWord (permitEcrecoverMem5 I domainWord digestWord)
      permitEcrecoverStaticcallAw ⟨450⟩ = ⟨0⟩ := by
  unfold permitMloadWord
  exact mloadWordValue_of_readWithPadding
    (off := (⟨450⟩ : UInt256)) (aw := permitEcrecoverStaticcallAw)
    (v := (⟨0⟩ : UInt256))
    (by rw [permitEcrecoverMem5_size]; native_decide)
    (by native_decide)
    (by simpa using permitEcrecoverMem5_read450_zero I domainWord digestWord)

theorem permitEcrecoverReturnCopyLen_le_size (o : ByteArray)
    (hoSize : o.size < UInt256.size) :
    permitEcrecoverReturnCopyLen o ≤ o.size := by
  unfold permitEcrecoverReturnCopyLen
  by_cases h : o.size < 32
  · have hword :
        min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) = UInt256.ofNat o.size := by
      rw [show min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) =
          if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
          else UInt256.ofNat o.size from rfl]
      rw [if_neg]
      change ¬ (32 : Nat) ≤ (UInt256.ofNat o.size).toNat
      rw [ulit_toNat' o.size hoSize]
      omega
    rw [hword, ulit_toNat' o.size hoSize]
  · have hword :
        min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) = (⟨32⟩ : UInt256) := by
      rw [show min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) =
          if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
          else UInt256.ofNat o.size from rfl]
      rw [if_pos]
      change (32 : Nat) ≤ (UInt256.ofNat o.size).toNat
      rw [ulit_toNat' o.size hoSize]
      omega
    rw [hword]
    change (32 : Nat) ≤ o.size
    omega

theorem permitEcrecoverReturnCopyLen_le_32 (o : ByteArray)
    (hoSize : o.size < UInt256.size) :
    permitEcrecoverReturnCopyLen o ≤ 32 := by
  unfold permitEcrecoverReturnCopyLen
  by_cases h : o.size < 32
  · have hword :
        min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) = UInt256.ofNat o.size := by
      rw [show min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) =
          if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
          else UInt256.ofNat o.size from rfl]
      rw [if_neg]
      change ¬ (32 : Nat) ≤ (UInt256.ofNat o.size).toNat
      rw [ulit_toNat' o.size hoSize]
      omega
    rw [hword, ulit_toNat' o.size hoSize]
    omega
  · have hword :
        min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) = (⟨32⟩ : UInt256) := by
      rw [show min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) =
          if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
          else UInt256.ofNat o.size from rfl]
      rw [if_pos]
      change (32 : Nat) ≤ (UInt256.ofNat o.size).toNat
      rw [ulit_toNat' o.size hoSize]
      omega
    rw [hword]
    change (32 : Nat) ≤ 32
    omega

theorem permitEcrecoverReturnCopyLen_eq_32 (o : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    permitEcrecoverReturnCopyLen o = 32 := by
  unfold permitEcrecoverReturnCopyLen
  have hword :
      min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) = (⟨32⟩ : UInt256) := by
    rw [show min (⟨32⟩ : UInt256) (UInt256.ofNat o.size) =
        if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
        else UInt256.ofNat o.size from rfl]
    rw [if_pos]
    change (32 : Nat) ≤ (UInt256.ofNat o.size).toNat
    rw [ulit_toNat' o.size hoSize]
    exact ho32
  rw [hword]
  native_decide

theorem permitEcrecoverReturnMem_size {mem o : ByteArray}
    (hmem : mem.size = 610) (hoSize : o.size < UInt256.size) :
    (permitEcrecoverReturnMem mem o).size = mem.size := by
  by_cases hlen : permitEcrecoverReturnCopyLen o = 0
  · simp [permitEcrecoverReturnMem, hlen, byteArray_write_len_zero]
  · unfold permitEcrecoverReturnMem
    have hleSize := permitEcrecoverReturnCopyLen_le_size o hoSize
    have hle32 := permitEcrecoverReturnCopyLen_le_32 o hoSize
    have hin : 450 + permitEcrecoverReturnCopyLen o ≤ mem.size := by
      rw [hmem]
      omega
    rw [write_eq_gen o mem 450 (permitEcrecoverReturnCopyLen o) hlen
      hleSize hin]
    rw [ByteArray.size_append, ByteArray.size_append]
    have hprefix : (mem.extract 0 450).size = 450 := by
      rw [ByteArray.size_extract]
      rw [hmem]
      omega
    have hsrc : (o.extract 0 (permitEcrecoverReturnCopyLen o)).size =
        permitEcrecoverReturnCopyLen o := by
      rw [ByteArray.size_extract]
      omega
    have htail : (mem.extract (450 + permitEcrecoverReturnCopyLen o) mem.size).size =
        mem.size - (450 + permitEcrecoverReturnCopyLen o) := by
      rw [ByteArray.size_extract]
      omega
    rw [hprefix, hsrc, htail, hmem]
    omega

theorem permitEcrecoverReturnMem_read64 {mem o : ByteArray}
    (hmem : 450 ≤ mem.size) (hoSize : o.size < UInt256.size) :
    (permitEcrecoverReturnMem mem o).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  by_cases hlen : permitEcrecoverReturnCopyLen o = 0
  · simp [permitEcrecoverReturnMem, hlen, byteArray_write_len_zero]
  · exact write_read_below_gen_extend o mem 450 (permitEcrecoverReturnCopyLen o) 64 hlen
      (permitEcrecoverReturnCopyLen_le_size o hoSize) hmem (by norm_num)

theorem permitEcrecoverReturnMem_mload64 {mem o : ByteArray}
    (hmem : mem.size = 610)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hoSize : o.size < UInt256.size) :
    permitMloadWord (permitEcrecoverReturnMem mem o) permitEcrecoverStaticcallAw ⟨64⟩ =
      (⟨482⟩ : UInt256) := by
  unfold permitMloadWord
  exact mloadWordValue_of_readWithPadding
    (by rw [permitEcrecoverReturnMem_size hmem hoSize, hmem]; native_decide)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
      rw [permitEcrecoverReturnMem_read64 (by rw [hmem]; norm_num) hoSize]
      exact hread)

theorem permitEcrecoverReturnMem_mload450 {mem o : ByteArray}
    (hmem : mem.size = 610) (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    permitMloadWord (permitEcrecoverReturnMem mem o) permitEcrecoverStaticcallAw ⟨450⟩ =
      UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  unfold permitMloadWord
  rw [mloadValue_eq_readWithPadding_of_lt_size
    (permitEcrecoverReturnMem mem o) permitEcrecoverStaticcallAw (⟨450⟩ : UInt256) mem.size
    (permitEcrecoverReturnMem_size hmem hoSize)
    (by rw [show (⟨450⟩ : UInt256).toNat = 450 by native_decide, hmem]; norm_num)
    (by native_decide)]
  rw [show (⟨450⟩ : UInt256).toNat = 450 by native_decide]
  rw [permitEcrecoverReturnMem,
    permitEcrecoverReturnCopyLen_eq_32 o ho32 hoSize]
  rw [write32_read_back o mem 450 ho32 (by rw [hmem]; norm_num)]

theorem permitTwoWordHashMem_mload64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 610)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256)) :
    permitMloadWord (permitTwoWordHashMem mem key slot) permitEcrecoverStaticcallAw ⟨64⟩ =
      (⟨482⟩ : UInt256) := by
  unfold permitMloadWord
  have hsize : (permitTwoWordHashMem mem key slot).size = 610 := by
    rw [permitTwoWordHashMem_size key slot (by rw [hmem]; norm_num), hmem]
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := permitEcrecoverStaticcallAw)
    (v := (⟨482⟩ : UInt256))
    (by rw [hsize]; native_decide)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
      rw [permitTwoWordHashMem_read64 key slot (by rw [hmem]; norm_num)]
      exact hread64)

theorem permitApprovalLogMem_mload64 {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 610)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256)) :
    permitMloadWord (permitApprovalLogMem mem I) permitEcrecoverStaticcallAw ⟨64⟩ =
      (⟨482⟩ : UInt256) := by
  unfold permitMloadWord
  have hsize : (permitApprovalLogMem mem I).size = 610 :=
    permitApprovalLogMem_size I hmem
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := permitEcrecoverStaticcallAw)
    (v := (⟨482⟩ : UInt256))
    (by rw [hsize]; native_decide)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
      unfold permitApprovalLogMem
      rw [permitWordMem_read_preserve
        (mem := mem) (off := 482) (read := 64) (word := permitWadWord I)
        (hgap := by rw [hmem]; norm_num)
        (hdisj := Or.inl ⟨by norm_num, by rw [hmem]; norm_num⟩)]
      exact hread64)

theorem daiPermitX_nonzeroHolderEcrecoverSuccessToRecoveredBranchAfter2758
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    {k C : ℕ}
    (rd2758 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2758⟩
      (⟨1⟩ ::
        [⟨610⟩, ⟨1⟩, permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
          permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
          permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
          permitHolderMaskedWord I, ⟨686⟩, daiSelWord I])
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k C)
    (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2808⟩
      [⟨2874⟩,
        UInt256.eq (permitHolderMaskedWord I)
          (UInt256.land solcAddrMask
            (permitMloadWord
              (permitEcrecoverReturnMem
                (permitEcrecoverMem5 I
                  (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
                    (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
                    domainSeparatorStorageSlot)
                  (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
                o)
              permitEcrecoverStaticcallAw ⟨450⟩)),
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k' C' := by
  let evm := initState cA gh bl σ σ₀ g A I
  let domainWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner domainSeparatorStorageSlot
  let digestWord := permitDigestWord evm I
  let baseMem := permitEcrecoverMem5 I domainWord digestWord
  let memRet := permitEcrecoverReturnMem baseMem o
  let recoveredWord := permitMloadWord memRet permitEcrecoverStaticcallAw ⟨450⟩
  have hbaseSize : baseMem.size = 610 := by
    simpa [baseMem] using permitEcrecoverMem5_size I domainWord digestWord
  have hmload64 : permitMloadWord memRet permitEcrecoverStaticcallAw ⟨64⟩ = ⟨482⟩ := by
    simpa [memRet, baseMem] using
      permitEcrecoverReturnMem_mload64
        (hmem := hbaseSize)
        (hread := by
          simpa [baseMem] using permitEcrecoverMem5_read64 I domainWord digestWord)
        (hoSize := hoSize)
  obtain ⟨_, _, rd2776⟩ :=
    RD.uniswapCallSuccessGuardOk (okPc := ⟨2774⟩) rd2758
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by simp)
  have rd2778 := evm_run rd2776 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd2784pre := evm_run rd2778 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨482⟩ permitEcrecoverStaticcallAw (by native_decide)
      mem_cost (by simpa [memRet] using hmload64) (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov)]
  rw [show UInt256.sub (⟨482⟩ : UInt256) ⟨32⟩ = ⟨450⟩ by native_decide] at rd2784pre
  have rd2785 := evm_run rd2784pre with [
    raw mload 0 recoveredWord permitEcrecoverStaticcallAw (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2793 := evm_run rd2785 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide] at rd2793
  have rd2804 := evm_run rd2793 with [
    raw and (by native_decide) (by evm_ov),
    raw dup10 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide] at rd2804
  have hholderMask :
      UInt256.land solcAddrMask (permitHolderMaskedWord I) = permitHolderMaskedWord I := by
    rw [u256_land_comm]
    exact solcAddrMask_clean (permitHolderMaskedWord_canonical I)
  have rd2808 := evm_run rd2804 with [
    raw and (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨2874⟩ (by native_decide) (by evm_ov)]
  rw [hholderMask] at rd2808
  exact ⟨_, _, by simpa [evm, domainWord, digestWord, baseMem, memRet, recoveredWord] using rd2808⟩

theorem daiPermitX_nonzeroHolderRecoveredOkAfter2808
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    {k C : ℕ}
    (rd2808 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2808⟩
      [⟨2874⟩,
        UInt256.eq (permitHolderMaskedWord I)
          (UInt256.land solcAddrMask
            (permitMloadWord
              (permitEcrecoverReturnMem
                (permitEcrecoverMem5 I
                  (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
                    (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
                    domainSeparatorStorageSlot)
                  (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
                o)
              permitEcrecoverStaticcallAw ⟨450⟩)),
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k C)
    (hcond :
      UInt256.eq (permitHolderMaskedWord I)
        (UInt256.land solcAddrMask
          (permitMloadWord
            (permitEcrecoverReturnMem
              (permitEcrecoverMem5 I
                (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
                  (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
                  domainSeparatorStorageSlot)
                (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
              o)
            permitEcrecoverStaticcallAw ⟨450⟩)) ≠ ⟨0⟩) :
    ∃ k' C', RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2874⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k' C' := by
  exact ⟨_, _, rd2808.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)⟩

theorem daiPermitX_nonzeroHolderExpiryOkAfter2874
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    {k C : ℕ}
    (rd2874 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2874⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k C)
    (hexpiryOk :
      permitExpiryWord I = ⟨0⟩ ∨
        (UInt256.ofNat I.header.timestamp).toNat ≤ (permitExpiryWord I).toNat) :
    ∃ k' C', RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k' C' := by
  have rd2881 := evm_run rd2874 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2887⟩ (by native_decide) (by evm_ov)]
  rcases hexpiryOk with hexpiryZero | htimeLe
  · have hizero : UInt256.isZero (permitExpiryWord I) = ⟨1⟩ := by
      rw [hexpiryZero]
      native_decide
    rw [hizero] at rd2881
    have rd2887 := rd2881.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)
    have rd2891 := evm_run rd2887 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2957⟩ (by native_decide) (by evm_ov)]
    exact ⟨_, _, rd2891.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)⟩
  · by_cases hexpiryZero : permitExpiryWord I = ⟨0⟩
    · have hizero : UInt256.isZero (permitExpiryWord I) = ⟨1⟩ := by
        rw [hexpiryZero]
        native_decide
      rw [hizero] at rd2881
      have rd2887 := rd2881.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)
      have rd2891 := evm_run rd2887 with [
        raw jumpdest (by native_decide) (by evm_ov),
        raw push2 ⟨2957⟩ (by native_decide) (by evm_ov)]
      exact ⟨_, _, rd2891.jumpiT (by native_decide) one_ne_zero_uint
        (by jump_dest) (by evm_ov)⟩
    have hnonzero : UInt256.isZero (permitExpiryWord I) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hexpiryZero
    rw [hnonzero] at rd2881
    have rd2882 := rd2881.jumpiNT (by native_decide) rfl (by evm_ov)
    have hgt : UInt256.gt (UInt256.ofNat I.header.timestamp) (permitExpiryWord I) = ⟨0⟩ :=
      ugt_zero htimeLe
    have hiszero : UInt256.isZero (UInt256.gt (UInt256.ofNat I.header.timestamp)
        (permitExpiryWord I)) = ⟨1⟩ := by
      rw [hgt]
      native_decide
    have rd2887pre := evm_run rd2882 with [
      raw pop (by native_decide) (by evm_ov),
      raw dup6 (by native_decide) (by evm_ov),
      raw timestamp (by native_decide) (by evm_ov),
      raw gt (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov)]
    rw [hiszero] at rd2887pre
    have rd2891 := evm_run rd2887pre with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2957⟩ (by native_decide) (by evm_ov)]
    exact ⟨_, _, rd2891.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiPermitX_nonzeroHolderExpiredAfter2874
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    {k C : ℕ}
    (rd2874 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2874⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k C)
    (hoSize : o.size < UInt256.size)
    (hexpiryNonzero : permitExpiryWord I ≠ ⟨0⟩)
    (hexpired :
      (permitExpiryWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let evm := initState cA gh bl σ σ₀ g A I
  let domainWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner domainSeparatorStorageSlot
  let digestWord := permitDigestWord evm I
  let baseMem := permitEcrecoverMem5 I domainWord digestWord
  let memRet := permitEcrecoverReturnMem baseMem o
  let err0 := (UInt256.toByteArray solcErrorStringSelector).write 0 memRet 482 32
  let err1 := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 err0 486 32
  let err2 := (UInt256.toByteArray (⟨18⟩ : UInt256)).write 0 err1 518 32
  let expiredPermitWord :=
    UInt256.shiftLeft (⟨0x11185a4bdc195c9b5a5d0b595e1c1a5c9959⟩ : UInt256) ⟨114⟩
  let err3 := (UInt256.toByteArray expiredPermitWord).write 0 err2 550 32
  let free2 := permitMloadWord err3 permitEcrecoverStaticcallAw ⟨64⟩
  have hbaseSize : baseMem.size = 610 := by
    simpa [evm, domainWord, digestWord, baseMem] using
      permitEcrecoverMem5_size I domainWord digestWord
  have hmload64 : permitMloadWord memRet permitEcrecoverStaticcallAw ⟨64⟩ = ⟨482⟩ := by
    simpa [memRet, baseMem] using
      permitEcrecoverReturnMem_mload64
        (hmem := hbaseSize)
        (hread := by
          simpa [baseMem] using permitEcrecoverMem5_read64 I domainWord digestWord)
        (hoSize := hoSize)
  have rd2881 := evm_run rd2874 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2887⟩ (by native_decide) (by evm_ov)]
  have hnonzero : UInt256.isZero (permitExpiryWord I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hexpiryNonzero
  rw [hnonzero] at rd2881
  have rd2882 := rd2881.jumpiNT (by native_decide) rfl (by evm_ov)
  have hgt :
      UInt256.gt (UInt256.ofNat I.header.timestamp) (permitExpiryWord I) = ⟨1⟩ :=
    ugt_one hexpired
  have hiszero : UInt256.isZero (UInt256.gt (UInt256.ofNat I.header.timestamp)
      (permitExpiryWord I)) = ⟨0⟩ := by
    rw [hgt]
    native_decide
  have rd2887pre := evm_run rd2882 with [
    raw pop (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hiszero] at rd2887pre
  have rd2891 := evm_run rd2887pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2957⟩ (by native_decide) (by evm_ov)]
  have rd2892 := rd2891.jumpiNT (by native_decide) rfl (by evm_ov)
  have rd2895 := evm_run rd2892 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd2896 := RD.mload 0 (⟨482⟩ : UInt256) permitEcrecoverStaticcallAw rd2895
    (by native_decide) mem_cost (by simpa [memRet] using hmload64)
    (by native_decide) (by evm_ov)
  have rd2900 :=
    RD.pushConst rd2896 (⟨4594637⟩ : UInt256)
      (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2902 := RD.push1 rd2900 (⟨229⟩ : UInt256) (by native_decide) (by evm_ov)
  have rd2903 := RD.shl rd2902 (by native_decide) (by evm_ov)
  rw [show UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩ =
      solcErrorStringSelector by native_decide] at rd2903
  have rd2904pre := RD.dup2 rd2903 (by native_decide) (by evm_ov)
  have rd2905 := rd2904pre.mstore 0 err0 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2911pre := evm_run rd2905 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨4⟩ : UInt256)) = ⟨486⟩ by native_decide]
    at rd2911pre
  have rd2912 := rd2911pre.mstore 0 err1 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2918pre := evm_run rd2912 with [
    raw push1 ⟨18⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨36⟩ : UInt256)) = ⟨518⟩ by native_decide]
    at rd2918pre
  have rd2919 := rd2918pre.mstore 0 err2 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdErrRaw := rd2919.pushConst
    (⟨0x11185a4bdc195c9b5a5d0b595e1c1a5c9959⟩ : UInt256)
    (width := 18) (op := .PUSH18) (by decide) (by native_decide) (by evm_ov)
  have rdErrWord := evm_run rdErrRaw with [
    raw push1 ⟨114⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [show UInt256.shiftLeft
      (⟨0x11185a4bdc195c9b5a5d0b595e1c1a5c9959⟩ : UInt256) ⟨114⟩ =
      expiredPermitWord by rfl] at rdErrWord
  have rd2945pre := evm_run rdErrWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨68⟩ : UInt256)) = ⟨550⟩ by native_decide]
    at rd2945pre
  have rd2946 := rd2945pre.mstore 0 err3 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2956 := evm_run rd2946 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 free2 permitEcrecoverStaticcallAw (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  exact rd2956.rev
    (Cₘ (UInt256.ofNat (MachineState.M permitEcrecoverStaticcallAw.toNat free2.toNat
      (((⟨100⟩ : UInt256) + UInt256.sub (⟨482⟩ : UInt256) free2).toNat))) -
      Cₘ permitEcrecoverStaticcallAw)
    (by native_decide)
    (fun s haws hstks => by
      set_option linter.unusedSimpArgs false in
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ])
    (by simp only [List.length_cons, List.length_nil]; norm_num)

set_option maxHeartbeats 1000000 in
theorem daiPermitX_nonzeroHolderBadRecoveredAfter2808
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    {k C : ℕ}
    (rd2808 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2808⟩
      [⟨2874⟩,
        UInt256.eq (permitHolderMaskedWord I)
          (UInt256.land solcAddrMask
            (permitMloadWord
              (permitEcrecoverReturnMem
                (permitEcrecoverMem5 I
                  (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
                    (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
                    domainSeparatorStorageSlot)
                  (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
                o)
              permitEcrecoverStaticcallAw ⟨450⟩)),
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitEcrecoverReturnMem
        (permitEcrecoverMem5 I
          (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
            (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
            domainSeparatorStorageSlot)
          (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
        o)
      permitEcrecoverStaticcallAw o (cA', σ') k C)
    (hoSize : o.size < UInt256.size)
    (hcond :
      UInt256.eq (permitHolderMaskedWord I)
        (UInt256.land solcAddrMask
          (permitMloadWord
            (permitEcrecoverReturnMem
              (permitEcrecoverMem5 I
                (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
                  (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
                  domainSeparatorStorageSlot)
                (permitDigestWord (initState cA gh bl σ σ₀ g A I) I))
              o)
            permitEcrecoverStaticcallAw ⟨450⟩)) = ⟨0⟩) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let evm := initState cA gh bl σ σ₀ g A I
  let domainWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner domainSeparatorStorageSlot
  let digestWord := permitDigestWord evm I
  let baseMem := permitEcrecoverMem5 I domainWord digestWord
  let memRet := permitEcrecoverReturnMem baseMem o
  let err0 := (UInt256.toByteArray solcErrorStringSelector).write 0 memRet 482 32
  let err1 := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 err0 486 32
  let err2 := (UInt256.toByteArray (⟨18⟩ : UInt256)).write 0 err1 518 32
  let invalidPermitWord :=
    UInt256.shiftLeft (⟨0x11185a4bda5b9d985b1a590b5c195c9b5a5d⟩ : UInt256) ⟨114⟩
  let err3 := (UInt256.toByteArray invalidPermitWord).write 0 err2 550 32
  let free2 := permitMloadWord err3 permitEcrecoverStaticcallAw ⟨64⟩
  have hbaseSize : baseMem.size = 610 := by
    simpa [evm, domainWord, digestWord, baseMem] using
      permitEcrecoverMem5_size I domainWord digestWord
  have hmload64 : permitMloadWord memRet permitEcrecoverStaticcallAw ⟨64⟩ = ⟨482⟩ := by
    simpa [memRet, baseMem] using
      permitEcrecoverReturnMem_mload64
        (hmem := hbaseSize)
        (hread := by
          simpa [baseMem] using permitEcrecoverMem5_read64 I domainWord digestWord)
        (hoSize := hoSize)
  have rd2809 := rd2808.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd2812 := evm_run rd2809 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd2813 :
      RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2813⟩
        [⟨482⟩, ⟨64⟩, permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
          permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
          permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
          permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
        memRet permitEcrecoverStaticcallAw o (cA', σ')
        (k + 1 + 1 + 1 + 1) (C + 10 + 3 + 3 + (0 + 3)) := by
    simpa [evm, domainWord, digestWord, baseMem, memRet] using
      RD.mload 0 (⟨482⟩ : UInt256) permitEcrecoverStaticcallAw rd2812
        (by native_decide) mem_cost (by simpa [memRet] using hmload64)
        (by native_decide) (by evm_ov)
  have rd2817 :=
    RD.pushConst rd2813 (⟨4594637⟩ : UInt256)
      (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2819 := RD.push1 rd2817 (⟨229⟩ : UInt256) (by native_decide) (by evm_ov)
  have rd2820 := RD.shl rd2819 (by native_decide) (by evm_ov)
  rw [show UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩ =
      solcErrorStringSelector by native_decide] at rd2820
  have rd2821pre := RD.dup2 rd2820 (by native_decide) (by evm_ov)
  have rd2822 := rd2821pre.mstore 0 err0 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2828pre := evm_run rd2822 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨4⟩ : UInt256)) = ⟨486⟩ by native_decide]
    at rd2828pre
  have rd2829 := rd2828pre.mstore 0 err1 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2835pre := evm_run rd2829 with [
    raw push1 ⟨18⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨36⟩ : UInt256)) = ⟨518⟩ by native_decide]
    at rd2835pre
  have rd2836 := rd2835pre.mstore 0 err2 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdErrRaw := rd2836.pushConst
    (⟨0x11185a4bda5b9d985b1a590b5c195c9b5a5d⟩ : UInt256)
    (width := 18) (op := .PUSH18) (by decide) (by native_decide) (by evm_ov)
  have rdErrWord := evm_run rdErrRaw with [
    raw push1 ⟨114⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [show UInt256.shiftLeft
      (⟨0x11185a4bda5b9d985b1a590b5c195c9b5a5d⟩ : UInt256) ⟨114⟩ =
      invalidPermitWord by rfl] at rdErrWord
  have rd2862pre := evm_run rdErrWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨68⟩ : UInt256)) = ⟨550⟩ by native_decide]
    at rd2862pre
  have rd2863 := rd2862pre.mstore 0 err3 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2873 := evm_run rd2863 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 free2 permitEcrecoverStaticcallAw (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  exact rd2873.rev
    (Cₘ (UInt256.ofNat (MachineState.M permitEcrecoverStaticcallAw.toNat free2.toNat
      (((⟨100⟩ : UInt256) + UInt256.sub (⟨482⟩ : UInt256) free2).toNat))) -
      Cₘ permitEcrecoverStaticcallAw)
    (by native_decide)
    (fun s haws hstks => by
      set_option linter.unusedSimpArgs false in
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ])
    (by simp only [List.length_cons, List.length_nil]; norm_num)

theorem daiPermitX_nonceBranchAfter2957
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memRet.size = 610)
    (hread64 : memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (rd2957 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      memRet permitEcrecoverStaticcallAw o (cA', σ') k C) :
    ∃ k' C', RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2996⟩
      [⟨3061⟩, UInt256.eq (permitNonceWord I) (permitEvmNonceWord σ' I),
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
      (cA', permitEvmAfterNonceAccountMap σ' I) k' C' := by
  have hmask :
      UInt256.land (permitHolderMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        permitHolderMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
    exact solcAddrMask_clean (permitHolderMaskedWord_canonical I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((permitNonceHashMem memRet I).readWithPadding 0 64))) =
        permitNonceStorageSlot I := by
    simpa [permitNonceHashMem, permitNonceStorageSlot_eq_mapSlot_masked I] using
      permitTwoWordHashMem_slot (mem := memRet) (permitHolderMaskedWord I)
        (⟨4⟩ : UInt256) (by rw [hmem]; norm_num)
  have rd2968 := evm_run rd2957 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup10 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmask] at rd2968
  have rd2971 := evm_run rd2968 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2972 := rd2971.mstore 0
    (permitWordMem memRet 0 (permitHolderMaskedWord I)) permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2977 := evm_run rd2972 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2978 := rd2977.mstore 0 (permitNonceHashMem memRet I)
    permitEcrecoverStaticcallAw (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd2981 := evm_run rd2978 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2982 := rd2981.keccak256 0 (permitNonceStorageSlot I)
    permitEcrecoverStaticcallAw (by native_decide) mem_cost hslot
    (by native_decide) (by evm_ov)
  have rd2983pre := evm_run rd2982 with [
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2983raw⟩ := rd2983pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; norm_num)
  have rd2984 := by
    simpa [permitEvmNonceWord, permitNonceStoredWord] using rd2983raw
  have rd2990 := evm_run rd2984 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2991raw⟩ := rd2990.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; norm_num)
  have rd2991 := by
    simpa [permitEvmAfterNonceAccountMap] using rd2991raw
  have rd2996 := evm_run rd2991 with [
    raw dup8 (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨3061⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd2996⟩

set_option maxHeartbeats 1000000 in
theorem daiPermitX_nonceMismatchAfter2957
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memRet.size = 610)
    (hread64 : memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hnonce : permitNonceWord I ≠ permitEvmNonceWord σ' I)
    (rd2957 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      memRet permitEcrecoverStaticcallAw o (cA', σ') k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let memHash := permitNonceHashMem memRet I
  let err0 := (UInt256.toByteArray solcErrorStringSelector).write 0 memHash 482 32
  let err1 := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 err0 486 32
  let err2 := (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 err1 518 32
  let invalidNonceWord :=
    UInt256.shiftLeft (⟨0x4461692f696e76616c69642d6e6f6e6365⟩ : UInt256) ⟨120⟩
  let err3 := (UInt256.toByteArray invalidNonceWord).write 0 err2 550 32
  let free2 := permitMloadWord err3 permitEcrecoverStaticcallAw ⟨64⟩
  have hmload64 : permitMloadWord memHash permitEcrecoverStaticcallAw ⟨64⟩ =
      (⟨482⟩ : UInt256) := by
    simpa [memHash, permitNonceHashMem] using
      permitTwoWordHashMem_mload64 (mem := memRet) (permitHolderMaskedWord I)
        (⟨4⟩ : UInt256) hmem hread64
  obtain ⟨_, _, rd2996⟩ :=
    daiPermitX_nonceBranchAfter2957 (g := g) hperm hmem hread64 rd2957
  have hcond : UInt256.eq (permitNonceWord I) (permitEvmNonceWord σ' I) = ⟨0⟩ :=
    u256_eq_of_ne hnonce
  have rd2997 := rd2996.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd3000 := evm_run rd2997 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd3001 := RD.mload 0 (⟨482⟩ : UInt256) permitEcrecoverStaticcallAw rd3000
    (by native_decide) mem_cost (by simpa [memHash] using hmload64)
    (by native_decide) (by evm_ov)
  have rd3005 :=
    RD.pushConst rd3001 (⟨4594637⟩ : UInt256)
      (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd3007 := RD.push1 rd3005 (⟨229⟩ : UInt256) (by native_decide) (by evm_ov)
  have rd3008 := RD.shl rd3007 (by native_decide) (by evm_ov)
  rw [show UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩ =
      solcErrorStringSelector by native_decide] at rd3008
  have rd3009pre := RD.dup2 rd3008 (by native_decide) (by evm_ov)
  have rd3010 := rd3009pre.mstore 0 err0 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3016pre := evm_run rd3010 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨4⟩ : UInt256)) = ⟨486⟩ by native_decide]
    at rd3016pre
  have rd3017 := rd3016pre.mstore 0 err1 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3023pre := evm_run rd3017 with [
    raw push1 ⟨17⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨36⟩ : UInt256)) = ⟨518⟩ by native_decide]
    at rd3023pre
  have rd3024 := rd3023pre.mstore 0 err2 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdErrRaw := rd3024.pushConst
    (⟨0x4461692f696e76616c69642d6e6f6e6365⟩ : UInt256)
    (width := 17) (op := .PUSH17) (by decide) (by native_decide) (by evm_ov)
  have rdErrWord := evm_run rdErrRaw with [
    raw push1 ⟨120⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [show UInt256.shiftLeft
      (⟨0x4461692f696e76616c69642d6e6f6e6365⟩ : UInt256) ⟨120⟩ =
      invalidNonceWord by rfl] at rdErrWord
  have rd3049pre := evm_run rdErrWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [show ((⟨482⟩ : UInt256) + (⟨68⟩ : UInt256)) = ⟨550⟩ by native_decide]
    at rd3049pre
  have rd3050 := rd3049pre.mstore 0 err3 permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3060 := evm_run rd3050 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 free2 permitEcrecoverStaticcallAw (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  exact rd3060.rev
    (Cₘ (UInt256.ofNat (MachineState.M permitEcrecoverStaticcallAw.toNat free2.toNat
      (((⟨100⟩ : UInt256) + UInt256.sub (⟨482⟩ : UInt256) free2).toNat))) -
      Cₘ permitEcrecoverStaticcallAw)
    (by native_decide)
    (fun s haws hstks => by
      set_option linter.unusedSimpArgs false in
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ])
    (by simp only [List.length_cons, List.length_nil]; norm_num)

set_option maxHeartbeats 1000000 in
theorem daiPermitX_successLogStopAfter3124
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {acct : AccountMap}
    {o memAllowance : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memAllowance.size = 610)
    (hread64 : memAllowance.readWithPadding 64 32 =
      UInt256.toByteArray (⟨482⟩ : UInt256))
    (rd3124 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3124⟩
      [⟨32⟩, ⟨64⟩, permitHolderMaskedWord I, permitSpenderMaskedWord I,
        permitWadWord I, ⟨0⟩,
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      memAllowance permitEcrecoverStaticcallAw o
      (cA', acct) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', acct) ByteArray.empty := by
  let memLog := permitApprovalLogMem memAllowance I
  have hmloadAllow64 :
      permitMloadWord memAllowance permitEcrecoverStaticcallAw ⟨64⟩ =
        (⟨482⟩ : UInt256) := by
    unfold permitMloadWord
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := permitEcrecoverStaticcallAw)
      (v := (⟨482⟩ : UInt256))
      (by rw [hmem]; native_decide)
      (by native_decide)
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        exact hread64)
  have hmloadLog64 :
      permitMloadWord memLog permitEcrecoverStaticcallAw ⟨64⟩ =
        (⟨482⟩ : UInt256) := by
    simpa [memLog] using permitApprovalLogMem_mload64 (I := I) hmem hread64
  have rd3125pre := RD.dup2 rd3124 (by native_decide) (by evm_ov)
  have rd3126 := RD.mload 0 (⟨482⟩ : UInt256) permitEcrecoverStaticcallAw rd3125pre
    (by native_decide) mem_cost (by simpa using hmloadAllow64)
    (by native_decide) (by evm_ov)
  have rd3128pre := evm_run rd3126 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3129 := rd3128pre.mstore 0 memLog permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3130pre := RD.swap2 rd3129 (by native_decide) (by evm_ov)
  have rd3131 := RD.mload 0 (⟨482⟩ : UInt256) permitEcrecoverStaticcallAw rd3130pre
    (by native_decide) mem_cost (by simpa [memLog] using hmloadLog64)
    (by native_decide) (by evm_ov)
  have rd3138 := evm_run rd3131 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd3171 := rd3138.pushConst permitApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd3178 := evm_run rd3171 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3179 := rd3178.log3 0 permitEcrecoverStaticcallAw (by native_decide) hperm
    mem_cost (by native_decide) (by simp only [List.length_cons, List.length_nil]; norm_num)
  have rd3189 := evm_run rd3179 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd686 := rd3189.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd687 := rd686.jumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; norm_num)
  exact rd687.stop (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; norm_num)

set_option maxHeartbeats 1000000 in
theorem daiPermitX_successStorageAfter3079
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memRet.size = 610)
    (hread64 : memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (rd3079 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3079⟩
      [permitWadWord I, ⟨0⟩,
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
      (cA', permitEvmAfterNonceAccountMap σ' I) k C) :
    ∃ k' C',
      RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3124⟩
        [⟨32⟩, ⟨64⟩, permitHolderMaskedWord I, permitSpenderMaskedWord I,
          permitWadWord I, ⟨0⟩,
          permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
          permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
          permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
          permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
        (permitAllowanceHashMem (permitNonceHashMem memRet I) I)
        permitEcrecoverStaticcallAw o (cA', permitEvmPostAccountMap σ' I) k' C' := by
  let memNonce := permitNonceHashMem memRet I
  let memOwner := permitAllowanceOwnerHashMem memNonce I
  let memAllowance := permitAllowanceHashMem memNonce I
  have hnonceSize : memNonce.size = 610 := by
    simpa [memNonce, permitNonceHashMem] using
      (permitTwoWordHashMem_size (mem := memRet) (permitHolderMaskedWord I)
        (⟨4⟩ : UInt256) (by rw [hmem]; norm_num)).trans hmem
  have hnonceRead64 :
      memNonce.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [memNonce, permitNonceHashMem] using
      (permitTwoWordHashMem_read64 (mem := memRet) (permitHolderMaskedWord I)
        (⟨4⟩ : UInt256) (by rw [hmem]; norm_num)).trans hread64
  have hownerSize : memOwner.size = 610 := by
    simpa [memOwner, permitAllowanceOwnerHashMem] using
      (permitTwoWordHashMem_size (mem := memNonce) (permitHolderMaskedWord I)
        (⟨3⟩ : UInt256) (by rw [hnonceSize]; norm_num)).trans hnonceSize
  have hownerRead64 :
      memOwner.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [memOwner, permitAllowanceOwnerHashMem] using
      (permitTwoWordHashMem_read64 (mem := memNonce) (permitHolderMaskedWord I)
        (⟨3⟩ : UInt256) (by rw [hnonceSize]; norm_num)).trans hnonceRead64
  have hallowSize : memAllowance.size = 610 := by
    simpa [memAllowance, permitAllowanceHashMem, memOwner] using
      (permitTwoWordHashMem_size (mem := memOwner) (permitSpenderMaskedWord I)
        (mapSlot (permitHolderMaskedWord I) ⟨3⟩) (by rw [hownerSize]; norm_num)).trans hownerSize
  have hallowRead64 :
      memAllowance.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [memAllowance, permitAllowanceHashMem, memOwner] using
      (permitTwoWordHashMem_read64 (mem := memOwner) (permitSpenderMaskedWord I)
        (mapSlot (permitHolderMaskedWord I) ⟨3⟩)
        (by rw [hownerSize]; norm_num)).trans hownerRead64
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((memOwner).readWithPadding 0 64))) =
        mapSlot (permitHolderMaskedWord I) ⟨3⟩ := by
    simpa [memOwner, permitAllowanceOwnerHashMem] using
      permitTwoWordHashMem_slot (mem := memNonce) (permitHolderMaskedWord I)
        (⟨3⟩ : UInt256) (by rw [hnonceSize]; norm_num)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((memAllowance).readWithPadding 0 64))) =
        permitAllowanceStorageSlot I := by
    simpa [memAllowance, permitAllowanceHashMem, memOwner,
      permitAllowanceStorageSlot_eq_mapSlot_masked I] using
      permitTwoWordHashMem_slot (mem := memOwner) (permitSpenderMaskedWord I)
        (mapSlot (permitHolderMaskedWord I) ⟨3⟩) (by rw [hownerSize]; norm_num)
  have hmloadAllow64 :
      permitMloadWord memAllowance permitEcrecoverStaticcallAw ⟨64⟩ =
        (⟨482⟩ : UInt256) := by
    simpa [memAllowance, permitAllowanceHashMem, memOwner] using
      permitTwoWordHashMem_mload64 (mem := memOwner) (permitSpenderMaskedWord I)
        (mapSlot (permitHolderMaskedWord I) ⟨3⟩) hownerSize hownerRead64
  have hholderMask :
      UInt256.land (permitHolderMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        permitHolderMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
    exact solcAddrMask_clean (permitHolderMaskedWord_canonical I)
  have hspenderMask :
      UInt256.land (permitSpenderMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        permitSpenderMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
    exact solcAddrMask_clean (permitSpenderMaskedWord_canonical I)
  have rd3091 := evm_run rd3079 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup13 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hholderMask] at rd3091
  have rd3095 := evm_run rd3091 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3096 := rd3095.mstore 0 (permitWordMem memNonce 0 (permitHolderMaskedWord I))
    permitEcrecoverStaticcallAw (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd3102 := evm_run rd3096 with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3103 := rd3102.mstore 0 memOwner permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3107 := evm_run rd3103 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd3108 := rd3107.keccak256 0 (mapSlot (permitHolderMaskedWord I) ⟨3⟩)
    permitEcrecoverStaticcallAw (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rd3111 := evm_run rd3108 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw dup16 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hspenderMask] at rd3111
  have rd3113 := evm_run rd3111 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd3114 := rd3113.mstore 0 (permitWordMem memOwner 0 (permitSpenderMaskedWord I))
    permitEcrecoverStaticcallAw (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd3116 := evm_run rd3114 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd3117 := rd3116.mstore 0 memAllowance permitEcrecoverStaticcallAw
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3120 := evm_run rd3117 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3121 := rd3120.keccak256 0 (permitAllowanceStorageSlot I)
    permitEcrecoverStaticcallAw (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  have rd3123 := evm_run rd3121 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k3124, C3124, rd3124raw⟩ := rd3123.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; norm_num)
  refine ⟨k3124, C3124, ?_⟩
  convert rd3124raw using 1

set_option maxHeartbeats 1000000 in
theorem daiPermitX_successTailAfter3079
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memRet.size = 610)
    (hread64 : memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (rd3079 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3079⟩
      [permitWadWord I, ⟨0⟩,
        permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
      (cA', permitEvmAfterNonceAccountMap σ' I) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', permitEvmPostAccountMap σ' I) ByteArray.empty := by
  let memNonce := permitNonceHashMem memRet I
  let memOwner := permitAllowanceOwnerHashMem memNonce I
  let memAllowance := permitAllowanceHashMem memNonce I
  have hnonceSize : memNonce.size = 610 := by
    simpa [memNonce, permitNonceHashMem] using
      (permitTwoWordHashMem_size (mem := memRet) (permitHolderMaskedWord I)
        (⟨4⟩ : UInt256) (by rw [hmem]; norm_num)).trans hmem
  have hnonceRead64 :
      memNonce.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [memNonce, permitNonceHashMem] using
      (permitTwoWordHashMem_read64 (mem := memRet) (permitHolderMaskedWord I)
        (⟨4⟩ : UInt256) (by rw [hmem]; norm_num)).trans hread64
  have hownerSize : memOwner.size = 610 := by
    simpa [memOwner, permitAllowanceOwnerHashMem] using
      (permitTwoWordHashMem_size (mem := memNonce) (permitHolderMaskedWord I)
        (⟨3⟩ : UInt256) (by rw [hnonceSize]; norm_num)).trans hnonceSize
  have hownerRead64 :
      memOwner.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [memOwner, permitAllowanceOwnerHashMem] using
      (permitTwoWordHashMem_read64 (mem := memNonce) (permitHolderMaskedWord I)
        (⟨3⟩ : UInt256) (by rw [hnonceSize]; norm_num)).trans hnonceRead64
  have hallowSize : memAllowance.size = 610 := by
    simpa [memAllowance, permitAllowanceHashMem, memOwner] using
      (permitTwoWordHashMem_size (mem := memOwner) (permitSpenderMaskedWord I)
        (mapSlot (permitHolderMaskedWord I) ⟨3⟩) (by rw [hownerSize]; norm_num)).trans hownerSize
  have hallowRead64 :
      memAllowance.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [memAllowance, permitAllowanceHashMem, memOwner] using
      (permitTwoWordHashMem_read64 (mem := memOwner) (permitSpenderMaskedWord I)
        (mapSlot (permitHolderMaskedWord I) ⟨3⟩)
        (by rw [hownerSize]; norm_num)).trans hownerRead64
  obtain ⟨k', C', rd3124⟩ :=
    daiPermitX_successStorageAfter3079 (g := g) hperm hmem hread64 rd3079
  exact daiPermitX_successLogStopAfter3124 (g := g) hperm
    (by simpa [memAllowance, memNonce] using hallowSize)
    (by simpa [memAllowance, memNonce] using hallowRead64)
    rd3124

set_option maxHeartbeats 1000000 in
theorem daiPermitX_after3061_allowedZero_to3079
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hclean : permitAllowedCleanWord I = ⟨0⟩)
    (hwad : permitWadWord I = ⟨0⟩)
    (rd3061 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
      (cA', permitEvmAfterNonceAccountMap σ' I) k C) :
    ∃ k' C',
      RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3079⟩
        [permitWadWord I, ⟨0⟩,
          permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
          permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
          permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
          permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
        (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
        (cA', permitEvmAfterNonceAccountMap σ' I) k' C' := by
  have rd3068 := evm_run rd3061 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push2 ⟨3075⟩ (by native_decide) (by evm_ov)]
  have rd3069 := rd3068.jumpiNT (by native_decide) hclean (by evm_ov)
  have rd3074 := evm_run rd3069 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨3079⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa only [hwad] using rd3074.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiPermitX_after3061_allowedNonzero_to3079
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hclean : permitAllowedCleanWord I = ⟨1⟩)
    (hwad : permitWadWord I = UInt256.lnot ⟨0⟩)
    (rd3061 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
      (cA', permitEvmAfterNonceAccountMap σ' I) k C) :
    ∃ k' C',
      RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3079⟩
        [permitWadWord I, ⟨0⟩,
          permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
          permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
          permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
          permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
        (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
        (cA', permitEvmAfterNonceAccountMap σ' I) k' C' := by
  have rd3068 := evm_run rd3061 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push2 ⟨3075⟩ (by native_decide) (by evm_ov)]
  have rd3075 := rd3068.jumpiT (by native_decide)
    (by rw [hclean]; exact one_ne_zero_uint)
    (by jump_dest) (by evm_ov)
  have rd3079raw := evm_run rd3075 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa only [hwad] using rd3079raw⟩

set_option maxHeartbeats 1000000 in
theorem daiPermitX_successAfter3061_allowedZero
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memRet.size = 610)
    (hread64 : memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hallowedZero : (permitAllowedWord I).toNat = 0)
    (rd3061 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
      (cA', permitEvmAfterNonceAccountMap σ' I) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', permitEvmPostAccountMap σ' I) ByteArray.empty := by
  have hclean : permitAllowedCleanWord I = ⟨0⟩ := by
    unfold permitAllowedCleanWord
    have hzero : permitAllowedWord I = ⟨0⟩ := uint256_toNat_eq_zero hallowedZero
    rw [hzero]
    native_decide
  have hwad : permitWadWord I = ⟨0⟩ := by
    simp [permitWadWord, hallowedZero]
  obtain ⟨_, _, rd3079⟩ :=
    daiPermitX_after3061_allowedZero_to3079 (g := g) hclean hwad rd3061
  exact daiPermitX_successTailAfter3079 (g := g) hperm hmem hread64 rd3079

set_option maxHeartbeats 1000000 in
theorem daiPermitX_successAfter3061_allowedNonzero
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memRet.size = 610)
    (hread64 : memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hallowedNonzero : ¬ (permitAllowedWord I).toNat = 0)
    (rd3061 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      (permitNonceHashMem memRet I) permitEcrecoverStaticcallAw o
      (cA', permitEvmAfterNonceAccountMap σ' I) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', permitEvmPostAccountMap σ' I) ByteArray.empty := by
  have hclean : permitAllowedCleanWord I = ⟨1⟩ := by
    unfold permitAllowedCleanWord
    have hnz : permitAllowedWord I ≠ ⟨0⟩ := by
      intro hz
      exact hallowedNonzero (by rw [hz]; rfl)
    rw [isZero_eq_zero_of_ne hnz]
    native_decide
  have hwad : permitWadWord I = UInt256.lnot ⟨0⟩ := by
    simp [permitWadWord, hallowedNonzero]
  obtain ⟨_, _, rd3079⟩ :=
    daiPermitX_after3061_allowedNonzero_to3079 (g := g) hclean hwad rd3061
  exact daiPermitX_successTailAfter3079 (g := g) hperm hmem hread64 rd3079

set_option maxHeartbeats 2000000 in
theorem daiPermitX_successAfter2957
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o memRet : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : memRet.size = 610)
    (hread64 : memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hnonce : permitNonceWord I = permitEvmNonceWord σ' I)
    (rd2957 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [permitDigestWord (initState cA gh bl σ σ₀ g A I) I,
        permitSWord I, permitRWord I, permitVMaskedWord I, permitAllowedCleanWord I,
        permitExpiryWord I, permitNonceWord I, permitSpenderMaskedWord I,
        permitHolderMaskedWord I, ⟨686⟩, daiSelWord I]
      memRet permitEcrecoverStaticcallAw o (cA', σ') k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', permitEvmPostAccountMap σ' I) ByteArray.empty := by
  obtain ⟨_, _, rd2996⟩ :=
    daiPermitX_nonceBranchAfter2957 (g := g) hperm hmem hread64 rd2957
  have heqOne : UInt256.eq (permitNonceWord I) (permitEvmNonceWord σ' I) = ⟨1⟩ := by
    rw [hnonce]
    exact u256_eq_refl _
  have hcond : UInt256.eq (permitNonceWord I) (permitEvmNonceWord σ' I) ≠ ⟨0⟩ := by
    rw [heqOne]
    exact one_ne_zero_uint
  have rd3061 := rd2996.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  by_cases hallowedZero : (permitAllowedWord I).toNat = 0
  · exact daiPermitX_successAfter3061_allowedZero (g := g)
      hperm hmem hread64 hallowedZero rd3061
  · exact daiPermitX_successAfter3061_allowedNonzero (g := g)
      hperm hmem hread64 hallowedZero rd3061

theorem permitStaticcallTheta_callViaEVM {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas g'' : UInt256}
    {A' : Substate}
    (hdepth : I.depth.val < 1024)
    (hΘ :
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
        σ σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
        (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
        (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        (permitEcrecoverCalldata (initState cA gh bl σ σ₀ g A I) I)
        (I.depth + 1) I.header false) :
    callViaEVM (initState cA gh bl σ σ₀ g A I) (EVM.address (AccountAddress.ofNat 1)) 0
      (permitEcrecoverCalldata (initState cA gh bl σ σ₀ g A I) I)
      (z,
        { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' },
        o) false := by
  apply callViaEVM.callMade (perm := false) wordOfInt_zero.symm
  · refine ⟨callGas, A_in, ?_⟩
    simpa [initState, accountAddress_roundtrip] using hΘ
  · rfl
  · show (⟨0⟩ : UInt256) ≤ _
    exact Fin.zero_le _
  · intro hbad
    have hv : I.depth.val = 1024 := by
      simpa using congrArg Fin.val hbad
    omega

/-- `permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32)` body refines its Solm transition. -/
theorem daiPermitBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 11) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some permitTransition :=
    daiDispatchPermit hsel
  have hreach := daiReachPermitBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz260 : 260 ≤ I.calldata.size
  · have hdecode := daiDecode_permit_ok (I := I) hsz260
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    by_cases hz : permitHolderMaskedWord I = ⟨0⟩
    · have hbody :
          ExecTransitionBody config contract evmSolm (permitStore I)
            permitTransition.body .reverted := by
        exact daiPermitBodyReverts_holderZero evmSolm I
          (by simpa [evmSolm, initState] using hwv) hz
      exact
        (daiPermitX_holderZeroRevert
          (g := Sat256.ofUInt256 g) hsz260 hsize hz hreach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · obtain ⟨_, _, rd2684⟩ :=
        daiPermitX_nonzeroHolderReach2684
          (g := Sat256.ofUInt256 g) hsz260 hsize hz hreach
      have hstaticOnDepth := fun hdepth =>
        daiPermitX_nonzeroHolderStaticcallFrom2684
          (g := Sat256.ofUInt256 g) hsz260 hdepth rd2684
      by_cases hdepth : I.depth.val < 1024
      · obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘex, rd2758, hoSize⟩ :=
          hstaticOnDepth hdepth
        rcases hΘex with ⟨g'', A', hΘ⟩
        have hcallEvm :
            callViaEVM (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (EVM.address (AccountAddress.ofNat 1)) 0
              (permitEcrecoverCalldata
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
              (z,
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' },
                o) false := by
          exact permitStaticcallTheta_callViaEVM
            (g := Sat256.ofUInt256 g) hdepth hΘ
        obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccountsCallRaw⟩ :=
          callViaEVM_initState_accountMapEquiv_perm
            (storage := config.storage) hcallEvm hAccounts
        have hcalldata :
            permitEcrecoverCalldata
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I =
              permitEcrecoverCalldata evmSolm I := by
          simpa [evmSolm] using
            permitEcrecoverCalldata_initState_accountMapEquiv
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) hAccounts
        rw [hcalldata] at hcallSolm
        by_cases hzcall : z = true
        · let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let domainWord :=
            Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner domainSeparatorStorageSlot
          let digestWord := permitDigestWord evmE I
          let baseMem := permitEcrecoverMem5 I domainWord digestWord
          let memRet := permitEcrecoverReturnMem baseMem o
          let evmPostSolm :=
            { evmSolm with
              accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
          have hcallSucceeded :
              callViaEVM evmSolm (EVM.address (AccountAddress.ofNat 1)) 0
                (permitEcrecoverCalldata evmSolm I) (true, evmPostSolm, o) false := by
            simpa [evmPostSolm, evmSolm, hzcall] using hcallSolm
          have hAccountsCall : accountMapEquiv σ' σ'_solm := by
            simpa using hAccountsCallRaw
          have hnonceLoad :
              permitEvmNonceWord σ' I =
                Solm.EVM.storageLoad evmPostSolm evmPostSolm.executionEnv.codeOwner
                  (permitNonceStorageSlot I) := by
            have hread :=
              accountMapEquiv_storage_findD hAccountsCall I.codeOwner
                (permitNonceStorageSlot I) (⟨0⟩ : UInt256)
            simpa [permitEvmNonceWord, permitNonceStoredWord, evmPostSolm, evmSolm,
              initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
              using hread
          have hrd2758 :
              RD daiBytecode I (Sat256.ofUInt256 g) evmE ⟨2758⟩
                (⟨1⟩ ::
                  [⟨610⟩, ⟨1⟩, permitDigestWord evmE I,
                    permitSWord I, permitRWord I, permitVMaskedWord I,
                    permitAllowedCleanWord I, permitExpiryWord I, permitNonceWord I,
                    permitSpenderMaskedWord I, permitHolderMaskedWord I, ⟨686⟩,
                    daiSelWord I])
                memRet permitEcrecoverStaticcallAw o (cA', σ') k' C' := by
            simpa [hzcall, evmE, domainWord, digestWord, baseMem, memRet,
              permitEcrecoverReturnMem] using rd2758
          have hbaseSize : baseMem.size = 610 := by
            simpa [baseMem] using permitEcrecoverMem5_size I domainWord digestWord
          have hmemRet : memRet.size = 610 := by
            simpa [memRet, hbaseSize] using
              permitEcrecoverReturnMem_size (mem := baseMem) (o := o) hbaseSize hoSize
          have hread64 :
              memRet.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
            calc
              memRet.readWithPadding 64 32 = baseMem.readWithPadding 64 32 := by
                simpa [memRet] using
                  permitEcrecoverReturnMem_read64 (mem := baseMem) (o := o)
                    (by rw [hbaseSize]; norm_num) hoSize
              _ = UInt256.toByteArray (⟨482⟩ : UInt256) := by
                simpa [baseMem] using permitEcrecoverMem5_read64 I domainWord digestWord
          obtain ⟨k2808, C2808, rd2808⟩ :=
            daiPermitX_nonzeroHolderEcrecoverSuccessToRecoveredBranchAfter2758
              (g := Sat256.ofUInt256 g) hrd2758 hoSize
          have hoSzAlt : o.size = 0 ∨ o.size = 32 :=
            permitStaticcallTheta_ecrecover_output_size hΘ
          by_cases ho32 : 32 ≤ o.size
          · let recoveredWord := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
            let recovered := AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))
            have hdecRet :
                ABI.decodeReturnValueWithMode? config.abiDecodeMode addr o =
                  some (.address recovered) := by
              simpa [config, recovered] using
                decodeReturnValueWithMode_legacy_addr_ok (returndata := o) ho32
            have hmload450 :
                permitMloadWord memRet permitEcrecoverStaticcallAw ⟨450⟩ =
                  recoveredWord := by
              simpa [memRet, baseMem, recoveredWord] using
                permitEcrecoverReturnMem_mload450 (mem := baseMem) (o := o)
                  hbaseSize ho32 hoSize
            have hrecoveredWordToNat :
                recoveredWord.toNat = fromByteArrayBigEndian (o.extract 0 32) := by
              simpa [recoveredWord] using
                UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt ho32)
            by_cases heqRecovered :
                AccountAddress.ofNat (permitHolderWord I).toNat = recovered
            · have hmaskEq :
                permitHolderMaskedWord I = UInt256.land solcAddrMask recoveredWord := by
                have hmask :=
                  (addressOfNat_eq_iff_solcAddrMask_eq
                    (permitHolderWord I) recoveredWord).mp (by
                      simpa [recovered, hrecoveredWordToNat] using heqRecovered)
                simpa [permitHolderMaskedWord] using hmask
              have hcondLocal :
                  UInt256.eq (permitHolderMaskedWord I)
                    (UInt256.land solcAddrMask
                      (permitMloadWord memRet permitEcrecoverStaticcallAw ⟨450⟩)) ≠
                    ⟨0⟩ := by
                rw [hmload450, ← hmaskEq, u256_eq_refl]
                exact one_ne_zero_uint
              have hcond :
                  UInt256.eq (permitHolderMaskedWord I)
                    (UInt256.land solcAddrMask
                      (permitMloadWord
                        (permitEcrecoverReturnMem
                          (permitEcrecoverMem5 I
                            (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner
                              domainSeparatorStorageSlot)
                            (permitDigestWord evmE I))
                          o)
                        permitEcrecoverStaticcallAw ⟨450⟩)) ≠ ⟨0⟩ := by
                simpa [domainWord, digestWord, baseMem, memRet] using hcondLocal
              obtain ⟨k2874, C2874, rd2874⟩ :=
                daiPermitX_nonzeroHolderRecoveredOkAfter2808
                  (g := Sat256.ofUInt256 g) rd2808 hcond
              by_cases hexpiryOk :
                  permitExpiryWord I = ⟨0⟩ ∨
                    (UInt256.ofNat evmPostSolm.executionEnv.header.timestamp).toNat ≤
                      (permitExpiryWord I).toNat
              · have hexpiryOkEvm :
                  permitExpiryWord I = ⟨0⟩ ∨
                    (UInt256.ofNat I.header.timestamp).toNat ≤
                      (permitExpiryWord I).toNat := by
                  simpa [evmPostSolm, evmSolm, initState] using hexpiryOk
                obtain ⟨k2957, C2957, rd2957⟩ :=
                  daiPermitX_nonzeroHolderExpiryOkAfter2874
                    (g := Sat256.ofUInt256 g) rd2874 hexpiryOkEvm
                by_cases hnonce : permitNonceWord I = permitEvmNonceWord σ' I
                · have hnonceSolm :
                    permitNonceWord I =
                      Solm.EVM.storageLoad evmPostSolm
                        evmPostSolm.executionEnv.codeOwner (permitNonceStorageSlot I) :=
                    hnonce.trans hnonceLoad
                  have hbody :
                      ExecTransitionBody config contract evmSolm (permitStore I)
                        permitTransition.body
                        (.returned
                          { contract := contract,
                            locals := permitWadStore evmSolm I o recovered }
                          (permitPostState evmPostSolm I) none) := by
                    exact daiPermitBodyReturns_success evmSolm evmPostSolm I o recovered
                      hsz260 (by simpa [evmSolm, initState] using hwv) hz
                      hcallSucceeded hdecRet heqRecovered hexpiryOk hnonceSolm
                  have hAccountsAfterNonce :
                      accountMapEquiv (permitEvmAfterNonceAccountMap σ' I)
                        (permitPostNonceState evmPostSolm I).accountMap := by
                    simpa [permitEvmAfterNonceAccountMap, permitPostNonceState,
                      evmPostSolm, evmSolm, initState, storageStore_accountMap,
                      hnonceLoad] using
                      accountMapEquiv_sstoreAccountMap I.codeOwner
                        (permitNonceStorageSlot I)
                        (permitEvmNonceWord σ' I + ⟨1⟩) hAccountsCall
                  have hAccountsPost :
                      accountMapEquiv (permitEvmPostAccountMap σ' I)
                        (permitPostState evmPostSolm I).accountMap := by
                    simpa [permitEvmPostAccountMap, permitPostState, evmPostSolm,
                      evmSolm, initState, storageStore_accountMap] using
                      accountMapEquiv_sstoreAccountMap I.codeOwner
                        (permitAllowanceStorageSlot I) (permitWadWord I)
                        hAccountsAfterNonce
                  have hCreatedPost :
                      cA' = (permitPostState evmPostSolm I).createdAccounts := by
                    simp [permitPostState, permitPostNonceState, evmPostSolm,
                      storageStore_createdAccounts]
                  exact
                    (daiPermitX_successAfter2957
                      (g := Sat256.ofUInt256 g) hperm hmemRet hread64 hnonce rd2957)
                    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                      hCreatedPost hAccountsPost
                      (by
                        simpa [permitTransition] using
                          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                            (t := []) (dvs := []) rfl (by native_decide)
                            (by native_decide)))
                · have hnonceSolmNe :
                    permitNonceWord I ≠
                      Solm.EVM.storageLoad evmPostSolm
                        evmPostSolm.executionEnv.codeOwner (permitNonceStorageSlot I) := by
                    intro hbad
                    exact hnonce (hbad.trans hnonceLoad.symm)
                  have hbody :
                      ExecTransitionBody config contract evmSolm (permitStore I)
                        permitTransition.body .reverted := by
                    exact daiPermitBodyReverts_nonceMismatch evmSolm evmPostSolm I
                      o recovered hsz260 (by simpa [evmSolm, initState] using hwv)
                      hz hcallSucceeded hdecRet heqRecovered hexpiryOk hnonceSolmNe
                  exact
                    (daiPermitX_nonceMismatchAfter2957
                      (g := Sat256.ofUInt256 g) hperm hmemRet hread64 hnonce rd2957)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hexpiryNonzero : permitExpiryWord I ≠ ⟨0⟩ := by
                  intro hzero
                  exact hexpiryOk (Or.inl hzero)
                have hnotle :
                    ¬ (UInt256.ofNat evmPostSolm.executionEnv.header.timestamp).toNat ≤
                      (permitExpiryWord I).toNat := by
                  intro hle
                  exact hexpiryOk (Or.inr hle)
                have hexpiredSolm :
                    (permitExpiryWord I).toNat <
                      (UInt256.ofNat evmPostSolm.executionEnv.header.timestamp).toNat :=
                  Nat.lt_of_not_ge hnotle
                have hexpiredEvm :
                    (permitExpiryWord I).toNat <
                      (UInt256.ofNat I.header.timestamp).toNat := by
                  simpa [evmPostSolm, evmSolm, initState] using hexpiredSolm
                have hbody :
                    ExecTransitionBody config contract evmSolm (permitStore I)
                      permitTransition.body .reverted := by
                  exact daiPermitBodyReverts_expired evmSolm evmPostSolm I o recovered
                    hsz260 (by simpa [evmSolm, initState] using hwv) hz
                    hcallSucceeded hdecRet heqRecovered hexpiryNonzero hexpiredSolm
                exact
                  (daiPermitX_nonzeroHolderExpiredAfter2874
                    (g := Sat256.ofUInt256 g) rd2874 hoSize hexpiryNonzero
                    hexpiredEvm)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hmaskNe :
                permitHolderMaskedWord I ≠ UInt256.land solcAddrMask recoveredWord := by
                intro hmaskEq
                have haddrEq :
                    AccountAddress.ofNat (permitHolderWord I).toNat = recovered := by
                  have haddrWord :
                      AccountAddress.ofNat (permitHolderWord I).toNat =
                        AccountAddress.ofNat recoveredWord.toNat :=
                    (addressOfNat_eq_iff_solcAddrMask_eq
                      (permitHolderWord I) recoveredWord).mpr
                      (by simpa [permitHolderMaskedWord] using hmaskEq)
                  simpa [recovered, hrecoveredWordToNat] using haddrWord
                exact heqRecovered haddrEq
              have hcondLocal :
                  UInt256.eq (permitHolderMaskedWord I)
                    (UInt256.land solcAddrMask
                      (permitMloadWord memRet permitEcrecoverStaticcallAw ⟨450⟩)) =
                    ⟨0⟩ := by
                rw [hmload450]
                exact u256_eq_of_ne hmaskNe
              have hcond :
                  UInt256.eq (permitHolderMaskedWord I)
                    (UInt256.land solcAddrMask
                      (permitMloadWord
                        (permitEcrecoverReturnMem
                          (permitEcrecoverMem5 I
                            (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner
                              domainSeparatorStorageSlot)
                            (permitDigestWord evmE I))
                          o)
                        permitEcrecoverStaticcallAw ⟨450⟩)) = ⟨0⟩ := by
                simpa [domainWord, digestWord, baseMem, memRet] using hcondLocal
              have hbody :
                  ExecTransitionBody config contract evmSolm (permitStore I)
                    permitTransition.body .reverted := by
                exact daiPermitBodyReverts_badRecovered evmSolm evmPostSolm I
                  o recovered hsz260 (by simpa [evmSolm, initState] using hwv) hz
                  hcallSucceeded hdecRet heqRecovered
              exact
                (daiPermitX_nonzeroHolderBadRecoveredAfter2808
                  (g := Sat256.ofUInt256 g) rd2808 hoSize hcond)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hoShort : o.size < 32 := Nat.lt_of_not_ge ho32
            have hdecNone :
                ABI.decodeReturnValueWithMode? config.abiDecodeMode addr o = none := by
              simpa [config] using
                decodeReturnValueWithMode_legacy_addr_none_short (returndata := o) hoShort
            have ho0 : o.size = 0 := by
              rcases hoSzAlt with hzero | hthirtyTwo
              · exact hzero
              · omega
            have hoEmpty : o = ByteArray.empty :=
              byteArray_eq_empty_of_size_eq_zero o ho0
            have hmloadEmpty :
                permitMloadWord memRet permitEcrecoverStaticcallAw ⟨450⟩ = ⟨0⟩ := by
              simpa [memRet, baseMem, hoEmpty, permitEcrecoverReturnMem_empty] using
                permitEcrecoverMem5_mload450_zero I domainWord digestWord
            have hcondLocal :
                UInt256.eq (permitHolderMaskedWord I)
                  (UInt256.land solcAddrMask
                    (permitMloadWord memRet permitEcrecoverStaticcallAw ⟨450⟩)) =
                  ⟨0⟩ := by
              rw [hmloadEmpty]
              rw [show UInt256.land solcAddrMask (⟨0⟩ : UInt256) = ⟨0⟩ by native_decide]
              exact u256_eq_of_ne hz
            have hcond :
                UInt256.eq (permitHolderMaskedWord I)
                  (UInt256.land solcAddrMask
                    (permitMloadWord
                      (permitEcrecoverReturnMem
                        (permitEcrecoverMem5 I
                          (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner
                            domainSeparatorStorageSlot)
                          (permitDigestWord evmE I))
                        o)
                      permitEcrecoverStaticcallAw ⟨450⟩)) = ⟨0⟩ := by
              simpa [domainWord, digestWord, baseMem, memRet] using hcondLocal
            have hbody :
                ExecTransitionBody config contract evmSolm (permitStore I)
                  permitTransition.body .reverted := by
              exact daiPermitBodyReverts_recoveredDecode evmSolm evmPostSolm I o
                hsz260 (by simpa [evmSolm, initState] using hwv) hz
                hcallSucceeded hdecNone
            exact
              (daiPermitX_nonzeroHolderBadRecoveredAfter2808
                (g := Sat256.ofUInt256 g) rd2808 hoSize hcond)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hrd2758 :
              RD daiBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2758⟩
                (⟨0⟩ ::
                  [⟨610⟩, ⟨1⟩,
                    permitDigestWord
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I,
                    permitSWord I, permitRWord I, permitVMaskedWord I,
                    permitAllowedCleanWord I, permitExpiryWord I, permitNonceWord I,
                    permitSpenderMaskedWord I, permitHolderMaskedWord I, ⟨686⟩,
                    daiSelWord I])
                (o.write 0
                  (permitEcrecoverMem5 I
                    (Solm.EVM.storageLoad
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      domainSeparatorStorageSlot)
                    (permitDigestWord
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I))
                  (⟨450⟩ : UInt256).toNat
                  (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
                (UInt256.ofNat
                  (MachineState.M
                    (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
                      (⟨128⟩ : UInt256).toNat)
                    (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))
                o (cA', σ') k' C' := by
            simpa [hzcall] using rd2758
          let evmPostSolm :=
            { evmSolm with
              accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
          have hcallFailed :
              callViaEVM evmSolm (EVM.address (AccountAddress.ofNat 1)) 0
                (permitEcrecoverCalldata evmSolm I) (false, evmPostSolm, o) false := by
            simpa [evmPostSolm, evmSolm, hzcall] using hcallSolm
          have hbody :
              ExecTransitionBody config contract evmSolm (permitStore I)
                permitTransition.body .reverted := by
            exact daiPermitBodyReverts_ecrecoverFailed evmSolm evmPostSolm I o hsz260
              (by simpa [evmSolm, initState] using hwv) hz hcallFailed
          exact
            (daiPermitX_nonzeroHolderEcrecoverFailureAfter2758
              (g := Sat256.ofUInt256 g) hrd2758 hoSize)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · obtain ⟨_gasArg, _k', _C', rd2757⟩ :=
          daiPermitX_nonzeroHolderToStaticcallFrom2684
            (g := Sat256.ofUInt256 g) rd2684
        have hdepthEqVal : I.depth.val = 1024 := by
          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
          omega
        have hdepthEq : I.depth = (1024 : Fin 1025) := Fin.ext hdepthEqVal
        obtain ⟨_kStatic, _CStatic, rd2758⟩ :=
          RD.uniswapStaticcallDepthLimit rd2757 (by native_decide) hdepthEq (by simp)
        let evmPostSolm :=
          { evmSolm with
            substate := (evmSolm.addAccessedAccount
              (EVM.address (AccountAddress.ofNat 1))).substate }
        have hcallFailed :
            callViaEVM evmSolm (EVM.address (AccountAddress.ofNat 1)) 0
              (permitEcrecoverCalldata evmSolm I)
              (false, evmPostSolm, ByteArray.empty) false := by
          apply callViaEVM.callNotMade (perm := false) rfl rfl
          rintro ⟨_, hdepthNe⟩
          exact hdepthNe (by simpa [evmSolm, initState] using hdepthEq)
        have hbody :
            ExecTransitionBody config contract evmSolm (permitStore I)
              permitTransition.body .reverted := by
          exact daiPermitBodyReverts_ecrecoverFailed evmSolm evmPostSolm I ByteArray.empty hsz260
            (by simpa [evmSolm, initState] using hwv) hz hcallFailed
        exact
          (daiPermitX_nonzeroHolderEcrecoverFailureAfter2758
            (g := Sat256.ofUInt256 g) rd2758 (by native_decide))
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (daiPermitX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (daiDecode_permit_none_short (I := I) hsz4 (by omega))

end Benchmarks.Dss.Dai

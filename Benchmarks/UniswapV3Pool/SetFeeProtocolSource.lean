import Benchmarks.UniswapV3Pool.Slot0
import Benchmarks.UniswapV3Pool.SetFeeProtocolOwnerCall

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev setFeeProtocolUint8Mask : UInt256 :=
  UInt256.ofNat (2 ^ 8 - 1)

abbrev setFeeProtocolArg0Word (I : ExecutionEnv) : UInt256 :=
  UInt256.land (calldataWord I.calldata 4) setFeeProtocolUint8Mask

abbrev setFeeProtocolArg1Word (I : ExecutionEnv) : UInt256 :=
  UInt256.land (calldataWord I.calldata 36) setFeeProtocolUint8Mask

abbrev setFeeProtocolArg0Value (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (setFeeProtocolArg0Word I).toNat)

abbrev setFeeProtocolArg1Value (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (setFeeProtocolArg1Word I).toNat)

abbrev setFeeProtocolStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "feeProtocol0" (setFeeProtocolArg0Value I)).insert
    "feeProtocol1" (setFeeProtocolArg1Value I)

theorem setFeeProtocolStore_feeProtocol0 (I : ExecutionEnv) :
    (setFeeProtocolStore I).get? "feeProtocol0" = some (setFeeProtocolArg0Value I) := by
  rw [setFeeProtocolStore]
  rw [store_get_ne (L := (∅ : Store).insert "feeProtocol0" (setFeeProtocolArg0Value I))
    (k := "feeProtocol1") (a := "feeProtocol0") (setFeeProtocolArg1Value I)
    (by native_decide)]
  exact store_get_self (∅ : Store) "feeProtocol0" (setFeeProtocolArg0Value I)

theorem setFeeProtocolStore_feeProtocol1 (I : ExecutionEnv) :
    (setFeeProtocolStore I).get? "feeProtocol1" = some (setFeeProtocolArg1Value I) := by
  rw [setFeeProtocolStore]
  exact store_get_self ((∅ : Store).insert "feeProtocol0" (setFeeProtocolArg0Value I))
    "feeProtocol1" (setFeeProtocolArg1Value I)

theorem evalExpr_setFeeProtocol_feeProtocol0 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      (.var "feeProtocol0") = .ok (setFeeProtocolArg0Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setFeeProtocolStore_feeProtocol0]

theorem evalExpr_setFeeProtocol_feeProtocol1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      (.var "feeProtocol1") = .ok (setFeeProtocolArg1Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setFeeProtocolStore_feeProtocol1]

theorem evalExpr_setFeeProtocol_addrLit {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (a : EVM.Address) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      (addrLit a) = .ok (Value.address (AccountAddress.ofNat a.toNat)) := by
  dsimp [addrLit]
  have hint :
      evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        (.intLit (↑↑a)) = .ok (.int (↑↑a)) := by
    simp [evalExpr?, pure]
  unfold evalExpr?
  rw [hint]
  change (if (↑↑a : Int) < 0 then EvalResult.error EvalError.typeError
      else EvalResult.ok
        (Value.address (AccountAddress.ofNat (Int.toNat (↑↑a : Int))))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat ↑a))
  rw [if_neg (by omega)]
  simp

theorem evalExpr_setFeeProtocol_factoryExtCodeSizeGuard_true {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (hcode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (setFeeProtocolFactoryWord v) ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)) = .ok (.bool true) := by
  unfold Reasoning.Theory.extCodeSizeWord at hcode
  have haddr : AccountAddress.ofUInt256 (setFeeProtocolFactoryWord v) =
      AccountAddress.ofNat ↑v.factory := by
    simpa using setFeeProtocolFactoryAddress_eq v
  rw [haddr] at hcode
  have hword :
      EVM.Word.ofNat
        ((evm.accountMap.find? (AccountAddress.ofNat ↑v.factory)).option 0
          (fun acc => acc.code.size)) ≠ (⟨0⟩ : UInt256) := by
    cases hacc : evm.accountMap.find? (AccountAddress.ofNat ↑v.factory)
    · simp [Option.option, hacc] at hcode
    · simpa [EVM.Word.ofNat, Option.option, hacc] using hcode
  have hnat :
      (EVM.Word.ofNat
        ((evm.accountMap.find? (AccountAddress.ofNat ↑v.factory)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0 := by
    intro hz
    exact hword (uint256_toNat_eq_zero hz)
  have hpos :
      0 <
        (EVM.Word.ofNat
          ((evm.accountMap.find? (AccountAddress.ofNat ↑v.factory)).option 0
            (fun acc => acc.code.size))).toNat :=
    Nat.pos_of_ne_zero hnat
  simp [evalExpr?, evalExpr_setFeeProtocol_addrLit, EvalResult.bind, evalBinaryOp?,
    State.lookupAccount, pure, bind, hpos]

theorem evalExpr_setFeeProtocol_factoryExtCodeSizeGuard_false {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (hcode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (setFeeProtocolFactoryWord v) = ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)) = .ok (.bool false) := by
  unfold Reasoning.Theory.extCodeSizeWord at hcode
  have haddr : AccountAddress.ofUInt256 (setFeeProtocolFactoryWord v) =
      AccountAddress.ofNat ↑v.factory := by
    simpa using setFeeProtocolFactoryAddress_eq v
  rw [haddr] at hcode
  have hword :
      EVM.Word.ofNat
        ((evm.accountMap.find? (AccountAddress.ofNat ↑v.factory)).option 0
          (fun acc => acc.code.size)) = (⟨0⟩ : UInt256) := by
    cases hacc : evm.accountMap.find? (AccountAddress.ofNat ↑v.factory)
    · native_decide
    · simpa [EVM.Word.ofNat, Option.option, hacc] using hcode
  have hnat :
      (EVM.Word.ofNat
        ((evm.accountMap.find? (AccountAddress.ofNat ↑v.factory)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    congrArg UInt256.toNat hword
  simp [evalExpr?, evalExpr_setFeeProtocol_addrLit, EvalResult.bind, evalBinaryOp?,
    State.lookupAccount, pure, bind, hnat]

abbrev setFeeProtocolUnlockedShift : UInt256 :=
  UInt256.shiftLeft ⟨1⟩ ⟨240⟩

abbrev setFeeProtocolUnlockedByte (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land setFeeProtocolUint8Mask
    (UInt256.div (solcSlotWord σ I ⟨0⟩) setFeeProtocolUnlockedShift)

abbrev setFeeProtocolUnlockedClearMask : UInt256 :=
  UInt256.lnot (UInt256.shiftLeft setFeeProtocolUint8Mask ⟨240⟩)

abbrev setFeeProtocolLockedSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land setFeeProtocolUnlockedClearMask (solcSlotWord σ I ⟨0⟩)

abbrev setFeeProtocolUnlockedLoc : StorageLoc :=
  loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool

theorem setFeeProtocolUnlockedByte_eq_slot0UnlockedRawWord (σ : AccountMap)
    (I : ExecutionEnv) :
    setFeeProtocolUnlockedByte σ I = slot0UnlockedRawWord σ I := by
  have hshift : setFeeProtocolUnlockedShift = slot0ShiftBytes 30 := by native_decide
  simp [setFeeProtocolUnlockedByte, slot0UnlockedRawWord, setFeeProtocolUnlockedShift,
    slot0ShiftBytes, slot0SlotWord, setFeeProtocolUint8Mask, slot0Uint8Mask, hshift,
    u256_land_comm]

theorem uniswapV3PoolSetFeeProtocolEvalUnlocked {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "unlocked")) =
      .ok (wordToElem .bool (setFeeProtocolUnlockedByte σ I)) := by
  rw [evalExpr_storage_scalar
    (t := .bool)
    (slot := slot0F "unlocked")
    (er := { base := "slot0", steps := [.field "unlocked"] })
    (loc := loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool)
    (hbase := by simp [slot0F, setFeeProtocolStore])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
  simpa [setFeeProtocolUnlockedByte_eq_slot0UnlockedRawWord] using
    slot0StorageLocLoad_unlocked (initState cA gh bl σ σ₀ g A I)

theorem setFeeProtocolUnlockedByte_wordToElem_false {σ : AccountMap} {I : ExecutionEnv}
    (hzero : setFeeProtocolUnlockedByte σ I = ⟨0⟩) :
    wordToElem .bool (setFeeProtocolUnlockedByte σ I) = .bool false := by
  simp [wordToElem, hzero]

theorem setFeeProtocolUnlockedByte_wordToElem_true {σ : AccountMap} {I : ExecutionEnv}
    (hnz : setFeeProtocolUnlockedByte σ I ≠ ⟨0⟩) :
    wordToElem .bool (setFeeProtocolUnlockedByte σ I) = .bool true := by
  have hbeq : ((setFeeProtocolUnlockedByte σ I).val == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

theorem setFeeProtocolUnlockedByte_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    setFeeProtocolUnlockedByte σ_solm I = setFeeProtocolUnlockedByte σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [setFeeProtocolUnlockedByte, solcSlotWord]
  rw [← hslot]

theorem setFeeProtocolLockedSlotWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    setFeeProtocolLockedSlotWord σ_solm I = setFeeProtocolLockedSlotWord σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [setFeeProtocolLockedSlotWord, solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolSetFeeProtocolSourceLockedReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : setFeeProtocolUnlockedByte σ I = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      (setfeeprotocolTransition v).body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner" (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")),
        .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))),
        .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
        .assign .storage (slot0F "feeProtocol")
          (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by simp [initState, hwv]))) <|
      ExecBlock.consRevert (ExecStmt.requireFalse (by
        rw [uniswapV3PoolSetFeeProtocolEvalUnlocked]
        exact congrArg EvalResult.ok (setFeeProtocolUnlockedByte_wordToElem_false hlocked)))

theorem setFeeProtocolStorageLocStore_unlocked_false_some (evm : EVM.State) :
    ∃ evm', storageLocStore evm setFeeProtocolUnlockedLoc (.bool false) = some evm' := by
  unfold storageLocStore storageLocWriteWord setFeeProtocolUnlockedLoc loc
  simp [valueToWord]

theorem uniswapV3PoolSetFeeProtocolSourceOwnerCallSuccess {v : PoolImmutables}
    {evm evm' : EVM.State} {I : ExecutionEnv} {out : ByteArray} {value : List Value}
    (hguard :
      evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)) = .ok (.bool true))
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (AccountAddress.ofNat v.factory.toNat))
        "owner" 0 [] (true, evm', out) false)
    (hdec : (config v).externalABI.decode? "owner" out = some value) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false) ]
      (.ok { contract := contract v,
             locals := (setFeeProtocolStore I).insert "_factoryOwner" (collapseReturns value) }
        evm') := by
  exact checkedExternalCallSuccess hguard (evalExpr_setFeeProtocol_addrLit evm I v.factory)
    (by rfl) hcall hdec

theorem uniswapV3PoolSetFeeProtocolSourceOwnerCallFailure {v : PoolImmutables}
    {evm evm' : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hguard :
      evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)) = .ok (.bool true))
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (AccountAddress.ofNat v.factory.toNat))
        "owner" 0 [] (false, evm', out) false) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false) ]
      .reverted := by
  exact checkedExternalCallFailure hguard (evalExpr_setFeeProtocol_addrLit evm I v.factory)
    (by rfl) hcall

theorem uniswapV3PoolSetFeeProtocolSourceOwnerCallDecodeRevert {v : PoolImmutables}
    {evm evm' : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hguard :
      evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)) = .ok (.bool true))
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (AccountAddress.ofNat v.factory.toNat))
        "owner" 0 [] (true, evm', out) false)
    (hdec : (config v).externalABI.decode? "owner" out = none) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false) ]
      .reverted := by
    exact checkedExternalCallDecodeRevert hguard (evalExpr_setFeeProtocol_addrLit evm I v.factory)
      (by rfl) hcall hdec
  
theorem decodeReturnValueWithMode_legacy_address_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiAddress returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0n : ¬ ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiAddress]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiAddress]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [abiAddress].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_none_short (bytes := returndata.toList) (start := 0)
    htake0n]
  rfl
  
theorem decodeReturnValueWithMode_legacy_address_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiAddress returndata =
      some (.address
        (AccountAddress.ofNat
          (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat)) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiAddress]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiAddress]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [abiAddress].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := returndata.toList) (start := 0) htake0]
  simp [hword]

theorem setFeeProtocolOwnerDecodeNoneShort {v : PoolImmutables} {out : ByteArray}
    (hshort : out.size < 32) :
    (config v).externalABI.decode? "owner" out = none := by
  simp [config, poolExternalABI, decodeReturn?, addr,
    decodeReturnValueWithMode_legacy_address_none_short hshort]

theorem setFeeProtocolOwnerDecodeOk {v : PoolImmutables} {out : ByteArray}
    (hlo : 32 ≤ out.size) :
    (config v).externalABI.decode? "owner" out =
      some [Value.address
        (AccountAddress.ofNat
          (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat)] := by
  simp [config, poolExternalABI, decodeReturn?, addr,
    decodeReturnValueWithMode_legacy_address_ok hlo]

abbrev setFeeProtocolOwnerWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev setFeeProtocolOwnerAddress (out : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (setFeeProtocolOwnerWord out).toNat

abbrev setFeeProtocolStoreWithOwner (I : ExecutionEnv) (out : ByteArray) : Store :=
  (setFeeProtocolStore I).insert "_factoryOwner" (.address (setFeeProtocolOwnerAddress out))

theorem setFeeProtocolOwnerAddress_eq_source_of_mask_eq {out : ByteArray} {I : ExecutionEnv}
    (h : UInt256.land solcAddrMask (setFeeProtocolOwnerWord out) = solcSourceWord I) :
    setFeeProtocolOwnerAddress out = I.source := by
  have hvalue := solcAddressValue_masked (setFeeProtocolOwnerWord out)
  have hmasked :
      AccountAddress.ofNat (UInt256.land solcAddrMask (setFeeProtocolOwnerWord out)).toNat =
        I.source := by
    rw [h]
    exact solcSource_ofNat I
  unfold setFeeProtocolOwnerAddress
  simpa [setFeeProtocolOwnerWord, hmasked] using hvalue

theorem setFeeProtocolOwnerMask_eq_source_of_address_eq {out : ByteArray} {I : ExecutionEnv}
    (h : setFeeProtocolOwnerAddress out = I.source) :
    UInt256.land solcAddrMask (setFeeProtocolOwnerWord out) = solcSourceWord I := by
  apply u256_inj
  rw [uland_toNat, solcSourceWord_toNat]
  have haddr :
      (setFeeProtocolOwnerWord out).toNat % AccountAddress.size = I.source.val := by
    have hval := congrArg Fin.val h
    unfold setFeeProtocolOwnerAddress AccountAddress.ofNat at hval
    simpa [Fin.val_ofNat] using hval
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [show 2 ^ 160 - 1 &&& (setFeeProtocolOwnerWord out).toNat =
      (setFeeProtocolOwnerWord out).toNat &&& (2 ^ 160 - 1) by
    exact Nat.and_comm _ _]
  change Nat.land (setFeeProtocolOwnerWord out).toNat (2 ^ 160 - 1) = I.source.val
  rw [nat_land_mask_eq_mod]
  simpa [AccountAddress.size] using haddr

theorem setFeeProtocolOwnerAddress_ne_source_of_mask_ne {out : ByteArray} {I : ExecutionEnv}
    (h : UInt256.land solcAddrMask (setFeeProtocolOwnerWord out) ≠ solcSourceWord I) :
    setFeeProtocolOwnerAddress out ≠ I.source := by
  intro haddr
  exact h (setFeeProtocolOwnerMask_eq_source_of_address_eq haddr)

theorem setFeeProtocolStoreWithOwner_factoryOwner (I : ExecutionEnv) (out : ByteArray) :
    (setFeeProtocolStoreWithOwner I out).get? "_factoryOwner" =
      some (.address (setFeeProtocolOwnerAddress out)) := by
  rw [setFeeProtocolStoreWithOwner]
  exact store_get_self (setFeeProtocolStore I) "_factoryOwner"
    (.address (setFeeProtocolOwnerAddress out))

theorem evalExpr_setFeeProtocol_factoryOwner {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (.var "_factoryOwner") = .ok (.address (setFeeProtocolOwnerAddress out)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setFeeProtocolStoreWithOwner_factoryOwner]

theorem evalExpr_setFeeProtocol_ownerCaller_eq_true {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hcaller : setFeeProtocolOwnerAddress out = evm.executionEnv.source) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (eqE (.env .caller) (.var "_factoryOwner")) = .ok (.bool true) := by
  simp only [eqE, evalExpr?, evalExpr_setFeeProtocol_factoryOwner, bind, EvalResult.bind,
    evalBinaryOp?]
  rw [hcaller]
  simp [envValue, BEq.beq]

theorem evalExpr_setFeeProtocol_ownerCaller_eq_false {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hcaller : setFeeProtocolOwnerAddress out ≠ evm.executionEnv.source) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (eqE (.env .caller) (.var "_factoryOwner")) = .ok (.bool false) := by
  simp only [eqE, evalExpr?, evalExpr_setFeeProtocol_factoryOwner, bind, EvalResult.bind,
    evalBinaryOp?]
  have hcaller' : evm.executionEnv.source ≠ setFeeProtocolOwnerAddress out := by
    intro h
    exact hcaller h.symm
  simp [envValue, BEq.beq, hcaller']

theorem setFeeProtocolUnlockedClearMask_toNat :
    setFeeProtocolUnlockedClearMask.toNat = 2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1) := by
  native_decide

theorem natLandClearByte240 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1)) =
      n % 2 ^ 240 + (n / 2 ^ 248) * 2 ^ 248 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1))).testBit i =
    (n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248).testBit i
  rw [Nat.testBit_and]
  rw [show n % 2 ^ 240 + (n / 2 ^ 248) * 2 ^ 248 =
      2 ^ 248 * (n / 2 ^ 248) + n % 2 ^ 240 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 248)
    (b_lt := lt_trans (Nat.mod_lt _ (by positivity : 0 < 2 ^ 240))
      (by norm_num : 2 ^ 240 < 2 ^ 248))]
  rw [show 2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1) =
      2 ^ 248 * (2 ^ 8 - 1) + (2 ^ 240 - 1) by norm_num [Nat.pow_add]]
  have hmaskLow : 2 ^ 240 - 1 < 2 ^ 248 := by norm_num
  rw [Nat.testBit_two_pow_mul_add (a := 2 ^ 8 - 1) (b_lt := hmaskLow)]
  by_cases hi248 : i < 248
  · simp [hi248]
    change (n.testBit i && (2 ^ 240 - 1).testBit i) = (n % 2 ^ 240).testBit i
    by_cases hi240 : i < 240
    · have hmask : (2 ^ 240 - 1).testBit i = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hi240
      have hmod : (n % 2 ^ 240).testBit i = n.testBit i := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi240]
      rw [hmask, hmod]
      simp
    · have hmask : (2 ^ 240 - 1).testBit i = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hi240
      have hmod : (n % 2 ^ 240).testBit i = false := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi240]
      rw [hmask, hmod]
      simp
  · have h248le : 248 ≤ i := Nat.le_of_not_gt hi248
    simp [hi248]
    change (n.testBit i && (2 ^ 8 - 1).testBit (i - 248)) =
      (n / 2 ^ 248).testBit (i - 248)
    by_cases hi256 : i < 256
    · have hsub8 : i - 248 < 8 := by omega
      have hdiv := divPow_testBit n 248 i h248le
      have hmask : (2 ^ 8 - 1).testBit (i - 248) = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hsub8
      rw [hdiv, hmask]
      simp
    · have hsub8 : ¬ i - 248 < 8 := by omega
      have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega : 256 ≤ i)))
      have hdivfalse : (n / 2 ^ 248).testBit (i - 248) = false := by
        rw [divPow_testBit n 248 i h248le, hnbit]
      have hmask : (2 ^ 8 - 1).testBit (i - 248) = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hsub8
      rw [hmask, hdivfalse]
      simp

theorem setFeeProtocolStorageLocStore_unlocked_false (evm : EVM.State) :
    storageLocStore evm setFeeProtocolUnlockedLoc (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          setFeeProtocolUnlockedClearMask)) := by
  unfold storageLocStore storageLocWriteWord setFeeProtocolUnlockedLoc loc
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner { val := 0 }
  show fromBytes'
      ((List.take 30 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0))) ++
        List.drop (30 + 1) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (UInt256.land w setFeeProtocolUnlockedClearMask).toNat
  rw [show List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)) =
      ([0] : List UInt8) by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [u256_land_toNat, setFeeProtocolUnlockedClearMask_toNat]
  rw [natLandClearByte240 w.toNat w.val.isLt]
  have hsumLt :
      w.toNat % 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248 < UInt256.size := by
    rw [← natLandClearByte240 w.toNat w.val.isLt]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hsumLt]
  have hlen30 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1).length = 30 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen31 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1 ++ [0]).length = 31 := by
    rw [List.length_append, hlen30]
    norm_num
  rw [hlen30]
  rw [hlen31]
  simp [fromBytes']
  ring

theorem uniswapV3PoolSetFeeProtocolSourceLockPrefixExact {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : setFeeProtocolUnlockedByte σ I ≠ ⟨0⟩) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
      (initState cA gh bl σ σ₀ g A I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false) ]
      (.ok { contract := contract v, locals := setFeeProtocolStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ I))) := by
  refine nonpayableRequireAssignStorageBlock
    (cfg := config v) (solm := { contract := contract v, locals := setFeeProtocolStore I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (evm' := Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
      (setFeeProtocolLockedSlotWord σ I))
    (guard := .storage (slot0F "unlocked")) (rhs := .boolLit false)
    (ref := slot0F "unlocked") (value := .bool false)
    (by simp [initState, hwv]) ?_ ?_ ?_
  · rw [uniswapV3PoolSetFeeProtocolEvalUnlocked]
    exact congrArg EvalResult.ok (setFeeProtocolUnlockedByte_wordToElem_true hunlocked)
  · simp [evalExpr?, pure]
  · apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "unlocked"] })
      (ty := .elem .bool)
      (loc := setFeeProtocolUnlockedLoc)
    · simp [slot0F, setFeeProtocolStore]
    · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
    · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt]
    · funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
        setFeeProtocolUnlockedLoc, loc]
    · trivial
    · simpa [initState, setFeeProtocolLockedSlotWord, solcSlotWord, u256_land_comm] using
        setFeeProtocolStorageLocStore_unlocked_false (initState cA gh bl σ σ₀ g A I)

theorem uniswapV3PoolSetFeeProtocolSourceOwnerCallRevertBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : setFeeProtocolUnlockedByte σ I ≠ ⟨0⟩)
    (howner :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ I)) σ₀ g A I)
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        .reverted) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      (setfeeprotocolTransition v).body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")),
        .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))),
        .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
        .assign .storage (slot0F "feeProtocol")
          (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolSetFeeProtocolSourceLockPrefixExact (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwv hunlocked
  have hstate :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ I)) σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have hfail :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ I))
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        .reverted := by
    simpa [hstate] using howner
  have hthrough := execBlock_append hprefix hfail
  exact execBlock_append_term (s2 :=
    [ .require (eqE (.env .caller) (.var "_factoryOwner")),
      .require
        (andE (feeProtocolEnabled (.var "feeProtocol0"))
          (feeProtocolEnabled (.var "feeProtocol1"))),
      .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
      .assign .storage (slot0F "feeProtocol")
        (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
      .assign .storage (slot0F "unlocked") (.boolLit true) ])
    hthrough (by intro f e h; cases h)

theorem uniswapV3PoolSetFeeProtocolSourceOwnerRequireSuccess {v : PoolImmutables}
    {evm evm' : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (howner :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evm'))
    (hcaller : setFeeProtocolOwnerAddress out = evm'.executionEnv.source) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")) ]
      (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evm') := by
  have hreq :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
        evm' [ .require (eqE (.env .caller) (.var "_factoryOwner")) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evm') := by
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_setFeeProtocol_ownerCaller_eq_true evm' I out hcaller)) ?_
    exact ExecBlock.nil
  simpa using execBlock_append howner hreq

theorem uniswapV3PoolSetFeeProtocolSourceOwnerRequireRevert {v : PoolImmutables}
    {evm evm' : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (howner :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evm'))
    (hcaller : setFeeProtocolOwnerAddress out ≠ evm'.executionEnv.source) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")) ]
      .reverted := by
  have hreq :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
        evm' [ .require (eqE (.env .caller) (.var "_factoryOwner")) ] .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_setFeeProtocol_ownerCaller_eq_false evm' I out hcaller))
  simpa using execBlock_append howner hreq

theorem uniswapV3PoolSetFeeProtocolSourceOwnerRequireSuccessPrefixExact
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    {evmOwner : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : setFeeProtocolUnlockedByte σ I ≠ ⟨0⟩)
    (howner :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ I)) σ₀ g A I)
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner))
    (hcaller : setFeeProtocolOwnerAddress out = evmOwner.executionEnv.source) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
      (initState cA gh bl σ σ₀ g A I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")) ]
      (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner) := by
  have hprefix := uniswapV3PoolSetFeeProtocolSourceLockPrefixExact (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwv hunlocked
  have hstate :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ I)) σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have howner' :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ I))
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner) := by
    simpa [hstate] using howner
  have hownerRequire :=
    uniswapV3PoolSetFeeProtocolSourceOwnerRequireSuccess (v := v)
      (evm := Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
        (setFeeProtocolLockedSlotWord σ I))
      (evm' := evmOwner) (I := I) (out := out) howner' hcaller
  simpa using execBlock_append hprefix hownerRequire

theorem uniswapV3PoolSetFeeProtocolSourceOwnerRequireRevertBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {evmOwner : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : setFeeProtocolUnlockedByte σ I ≠ ⟨0⟩)
    (howner :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ I)) σ₀ g A I)
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner))
    (hcaller : setFeeProtocolOwnerAddress out ≠ evmOwner.executionEnv.source) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      (setfeeprotocolTransition v).body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")),
        .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))),
        .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
        .assign .storage (slot0F "feeProtocol")
          (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolSetFeeProtocolSourceLockPrefixExact (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwv hunlocked
  have hstate :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ I)) σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have howner' :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ I))
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner) := by
    simpa [hstate] using howner
  have hownerRequire :=
    uniswapV3PoolSetFeeProtocolSourceOwnerRequireRevert (v := v)
      (evm := Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
        (setFeeProtocolLockedSlotWord σ I))
      (evm' := evmOwner) (I := I) (out := out) howner' hcaller
  have hthrough := execBlock_append hprefix hownerRequire
  exact execBlock_append_term (s2 :=
    [ .require
        (andE (feeProtocolEnabled (.var "feeProtocol0"))
          (feeProtocolEnabled (.var "feeProtocol1"))),
      .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
      .assign .storage (slot0F "feeProtocol")
        (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
      .assign .storage (slot0F "unlocked") (.boolLit true) ])
    hthrough (by intro f e h; cases h)

end Benchmarks.UniswapV3Pool

import Benchmarks.Morpho.MetaMorphoV1_1.Storage

/-! Bounds checks and full-slot reads for dynamic storage arrays. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: reduce a dynamic-array bounds check to its backend length.
theorem dynamicArrayBounds {cfg : Config} {evm : EVM.State} {decls : List StorageDecl}
    {base : Ident} {pre : List EvaledStorageRefStep} {elem : StorageType} {i len : Nat}
    (hty : storageTypeAt? decls ⟨base, pre⟩ = some (.dynamicArray elem))
    (hlen : cfg.storageBackend.length ⟨base, pre⟩ (.dynamicArray elem) evm = .ok len) :
    arrayIndexInBounds? cfg evm decls base pre (.int (Int.ofNat i)) =
      if i < len then .ok () else .revert := by
  simp only [arrayIndexInBounds?, hty, hlen, Int.ofNat_eq_natCast,
    Int.natCast_nonneg, Int.ofNat_lt, true_and]

-- LIBRARY CANDIDATE: resolve an array index held in a local variable after its bounds check.
theorem evalStorageRef_arrayIndex {cfg : Config} {solm : Frame} {evm : EVM.State}
    (base name : Ident) (i : Nat)
    (hget : solm.locals.get? name = some (.int (Int.ofNat i)))
    (hbound : arrayIndexInBounds? cfg evm solm.contract.storage base []
      (.int (Int.ofNat i)) = .ok ()) :
    evalStorageRef cfg solm evm ⟨base, [.aindex (.var name)]⟩ =
      .ok ⟨base, [.aindex (.int (Int.ofNat i))]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, hbound]

-- LIBRARY CANDIDATE: a failed array bound propagates through a storage expression.
theorem evalStorage_arrayIndex_revert {cfg : Config} {solm : Frame} {evm : EVM.State}
    (base name : Ident) (i : Nat) (hbase : solm.locals.get? base = none)
    (hget : solm.locals.get? name = some (.int (Int.ofNat i)))
    (hbound : arrayIndexInBounds? cfg evm solm.contract.storage base []
      (.int (Int.ofNat i)) = .revert) :
    evalExpr? cfg solm evm (.storage ⟨base, [.aindex (.var name)]⟩) = .revert := by
  have her : evalStorageRef cfg solm evm ⟨base, [.aindex (.var name)]⟩ = .revert := by
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure, hbound]
  rw [evalExpr?]
  simp only [resolveStorageRef?, hbase, her, bind, EvalResult.bind]

theorem supplyQueueBounds (evm : EVM.State) (i : UInt256) :
    arrayIndexInBounds? config evm contract.storage "supplyQueue" []
      (.int (Int.ofNat i.toNat)) =
      if i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨20⟩).toNat
      then .ok () else .revert := by
  exact dynamicArrayBounds (elem := .elem (.bytes ⟨31, by decide⟩))
    (show storageTypeAt? contract.storage ⟨"supplyQueue", []⟩ =
      some (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) from by decide +kernel)
    (storageDynamicArrayLength (slot := ⟨20⟩) rfl rfl)

theorem withdrawQueueBounds (evm : EVM.State) (i : UInt256) :
    arrayIndexInBounds? config evm contract.storage "withdrawQueue" []
      (.int (Int.ofNat i.toNat)) =
      if i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat
      then .ok () else .revert := by
  exact dynamicArrayBounds (elem := .elem (.bytes ⟨31, by decide⟩))
    (show storageTypeAt? contract.storage ⟨"withdrawQueue", []⟩ =
      some (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) from by decide +kernel)
    (storageDynamicArrayLength (slot := ⟨21⟩) rfl rfl)

theorem evalStorage_supplyQueue (evm : EVM.State) (locals imms : Store) (i : UInt256)
    (hbase : locals.get? "supplyQueue" = none)
    (hget : locals.get? "arg0" = some (.int (Int.ofNat i.toNat)))
    (hbound : i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨20⟩).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"supplyQueue", [.aindex (.var "arg0")]⟩) =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) + i)))) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"supplyQueue", [.aindex (.int (Int.ofNat i.toNat))]⟩)
    (t := .bytes ⟨31, by decide⟩) hbase
    (evalStorageRef_arrayIndex "supplyQueue" "arg0" _ hget
      (by rw [supplyQueueBounds, if_pos hbound])) rfl rfl
    (loc := bytes32Loc (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) + i))
  · change some (StorageAddr.leaf
      { slot := uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) +
          UInt256.ofNat ((keyValueToWord (.int (Int.ofNat i.toNat))).toNat / 1)
        offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat i.toNat))).toNat % 1 * 32)
        size := 32, hbound := by simp, type := .bytes ⟨31, by decide⟩ }) = _
    simp only [keyValueToWord_uint256, Nat.div_one, Nat.mod_one, Nat.zero_mul,
      u256_ofNat_toNat]
    rfl
  · exact storageLocLoad_bytes32 evm _

theorem evalStorage_withdrawQueue_local (evm : EVM.State) (locals imms : Store)
    (name : Ident) (i : UInt256)
    (hbase : locals.get? "withdrawQueue" = none)
    (hget : locals.get? name = some (.int (Int.ofNat i.toNat)))
    (hbound : i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"withdrawQueue", [.aindex (.var name)]⟩) =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + i)))) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"withdrawQueue", [.aindex (.int (Int.ofNat i.toNat))]⟩)
    (t := .bytes ⟨31, by decide⟩) hbase
    (evalStorageRef_arrayIndex "withdrawQueue" name _ hget
      (by rw [withdrawQueueBounds, if_pos hbound])) rfl rfl
    (loc := bytes32Loc (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + i))
  · change some (StorageAddr.leaf
      { slot := uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) +
          UInt256.ofNat ((keyValueToWord (.int (Int.ofNat i.toNat))).toNat / 1)
        offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat i.toNat))).toNat % 1 * 32)
        size := 32, hbound := by simp, type := .bytes ⟨31, by decide⟩ }) = _
    simp only [keyValueToWord_uint256, Nat.div_one, Nat.mod_one, Nat.zero_mul,
      u256_ofNat_toNat]
    rfl
  · exact storageLocLoad_bytes32 evm _

theorem evalStorage_withdrawQueue (evm : EVM.State) (locals imms : Store) (i : UInt256)
    (hbase : locals.get? "withdrawQueue" = none)
    (hget : locals.get? "arg0" = some (.int (Int.ofNat i.toNat)))
    (hbound : i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"withdrawQueue", [.aindex (.var "arg0")]⟩) =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + i)))) := by
  exact evalStorage_withdrawQueue_local evm locals imms "arg0" i hbase hget hbound

end Benchmarks.Morpho.MetaMorphoV1_1

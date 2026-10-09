import Benchmarks.Safe.ModuleStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def ownerLink (evm : EVM.State) (key : UInt256) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨2⟩))
    solcAddrMask

def ownerLinkAt (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : UInt256 :=
  UInt256.land (solcSlotWordAt (mapSlot key ⟨2⟩) σ I) solcAddrMask

theorem ownerLink_eq_at (evm : EVM.State) (key : UInt256) :
    ownerLink evm key = ownerLinkAt evm.accountMap evm.executionEnv key := by
  simp only [ownerLink, ownerLinkAt, storageLoad_eq_solcSlotWord]
  rfl

theorem safeOwnerSentinelSlot : mapSlot ⟨1⟩ ⟨2⟩ =
    UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136
      := by
  native_decide

def writeOwnerLink (evm : EVM.State) (key value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (mapSlot key ⟨2⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨2⟩)) value)

theorem safeEvalOwnerLink (evm : EVM.State) (locals : Store) (expr : Expr) (key : UInt256)
    (hbase : locals["owners"]? = none)
    (hcanon : key.toNat < EVM.addressModulus)
    (heval : evalExpr? config { contract := contract, locals := locals } evm expr =
      .ok (.address (AccountAddress.ofNat key.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ownersRef expr)) = .ok (.address (AccountAddress.ofNat (ownerLink evm
        key).toNat)) := by
  apply evalExpr_storage_scalar_value (er := { base := "owners", steps :=
      [.mindex (.address (AccountAddress.ofNat key.toNat))] })
    (loc := addressOffset0Loc (mapSlot key ⟨2⟩))
  · exact hbase
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ownersRef,
      heval, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (addrLoc (mapSlot
      (keyValueToWord (.address (AccountAddress.ofNat key.toNat))) ⟨2⟩))) = _
    rw [keyValueToWord_address_of_canonical key hcanon]
    rfl
  · exact storageLocLoad_address_offset0 evm (mapSlot key ⟨2⟩)

theorem safeAssignOwnerLink (evm : EVM.State) (locals : Store)
    (expr : Expr) (key value : UInt256)
    (hbase : locals["owners"]? = none)
    (hkey : key.toNat < EVM.addressModulus) (hvalue : value.toNat < EVM.addressModulus)
    (heval : evalExpr? config { contract := contract, locals := locals } evm expr =
      .ok (.address (AccountAddress.ofNat key.toNat))) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (ownersRef expr) (.address (AccountAddress.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals }, writeOwnerLink evm key value) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "owners", steps :=
      [.mindex (.address (AccountAddress.ofNat key.toNat))] })
    (loc := addressOffset0Loc (mapSlot key ⟨2⟩))
  · exact hbase
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ownersRef,
      heval, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (addrLoc (mapSlot
      (keyValueToWord (.address (AccountAddress.ofNat key.toNat))) ⟨2⟩))) = _
    rw [keyValueToWord_address_of_canonical key hkey]
    rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_address_offset0 evm (mapSlot key ⟨2⟩) value hvalue


end Benchmarks.Safe

import Benchmarks.Safe.OwnerStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def ownerCount (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩

def storedThreshold (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩

theorem safeEvalOwnerCount (evm : EVM.State) (locals : Store)
    (hb : locals["ownerCount"]? = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ownerCountRef) =
      .ok (.int (Int.ofNat (ownerCount evm).toNat)) := by
  apply evalExpr_storage_scalar_value (er := { base := "ownerCount" }) (loc := uint256Loc ⟨3⟩)
  · exact hb
  · simp [evalStorageRef, evalStorageRefSteps, ownerCountRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm ⟨3⟩

theorem safeAssignOwnerCount (evm : EVM.State) (locals : Store) (value : UInt256)
    (hb : locals["ownerCount"]? = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage ownerCountRef
      (.int (Int.ofNat value.toNat)) = .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ value) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "ownerCount" })
    (loc := uint256Loc ⟨3⟩)
  · exact hb
  · simp [evalStorageRef, evalStorageRefSteps, ownerCountRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm ⟨3⟩ value

theorem safeEvalStoredThreshold (evm : EVM.State) (locals : Store)
    (hb : locals["threshold"]? = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage thresholdRef) =
      .ok (.int (Int.ofNat (storedThreshold evm).toNat)) := by
  apply evalExpr_storage_scalar_value (er := { base := "threshold" }) (loc := uint256Loc ⟨4⟩)
  · exact hb
  · simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm ⟨4⟩

theorem safeEvalOwnerSentinel (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm sentinelAddr =
      .ok (.address (AccountAddress.ofNat (⟨1⟩ : UInt256).toNat)) := by
  simp [sentinelAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    bind, pure]
  rfl

end Benchmarks.Safe

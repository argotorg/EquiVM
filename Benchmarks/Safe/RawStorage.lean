import Benchmarks.Safe.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeEvalRawStorage (evm : EVM.State) (locals : Store) (expr : Expr) (slot : UInt256)
    (hbase : locals["_rawStorage"]? = none)
    (heval : evalExpr? config { contract := contract, locals := locals } evm expr =
      .ok (.int (Int.ofNat slot.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (rawStorageRef expr)) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := { base := "_rawStorage", steps := [.mindex (.int (Int.ofNat slot.toNat))] })
    (loc := uint256Loc slot)
  · exact hbase
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rawStorageRef,
      heval, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf
      (wordLoc (keyValueToWord (.int (Int.ofNat slot.toNat))) _)) = _
    rw [keyValueToWord_uint256]
    rfl
  · exact storageLocLoad_uint256 evm slot

end Benchmarks.Safe

import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayStorage
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueSyntax

/-! Exact source storage updates for supply-queue assignment. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def supplyQueueSourceAccounts (owner : AccountAddress) (σ : AccountMap)
    (oldLength : Nat) (words : Nat → UInt256) (n : Nat) : AccountMap :=
  sstoreAccountMap owner
    (storeWordArray owner
      (sstoreAccountMap owner
        (clearDataWordsForwardFrom owner σ (solidityBytesDataBaseSlot ⟨20⟩) ⟨0⟩ oldLength)
        ⟨20⟩ ⟨0⟩)
      (solidityBytesDataBaseSlot ⟨20⟩) words 0 n)
    ⟨20⟩ (UInt256.ofNat n)

def supplyQueueSourceState (evm : State) (words : Nat → UInt256) (n : Nat) : State :=
  { evm with
    accountMap := supplyQueueSourceAccounts evm.executionEnv.codeOwner evm.accountMap
      (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨20⟩).toNat words n }

theorem supplyQueueBackendWrite (evm : State) (words : Nat → UInt256) (n : Nat) :
    config.storageBackend.write ⟨"supplyQueue", []⟩ (.dynamicArray (.elem (.bytes abiBytes32Width)))
      (.array (wordArrayValues words 0 n)) evm = .ok (supplyQueueSourceState evm words n) := by
  have hlen : solidityDynamicLength? stringStorageLayout evm ⟨"supplyQueue", []⟩ =
      .ok (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨20⟩).toNat :=
    storageDynamicArrayLength (cfg := config) (elem := .elem (.bytes abiBytes32Width)) rfl rfl
  exact solidityReplaceWordArray supplyQueueElementLayout rfl evm words n hlen

theorem supplyQueueStorageResolve {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "supplyQueue" = none) :
    resolveStorageRef? config frame evm ⟨"supplyQueue", []⟩ =
      .ok (⟨"supplyQueue", []⟩, .dynamicArray (.elem (.bytes abiBytes32Width))) := by
  simp only [resolveStorageRef?, hbase, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, bind, pure, hcontract]
  rfl

theorem supplyQueueAssign {frame : Frame} {evm : State} {words : Nat → UInt256} {n i : Nat}
    (hready : SupplyQueueReady frame (wordArrayValues words 0 n) i) :
    ExecStmt config frame evm
      (.assign .storage ⟨"supplyQueue", []⟩ (.var "newSupplyQueue"))
      (.ok frame (supplyQueueSourceState evm words n)) := by
  apply ExecStmt.assign (value := .array (wordArrayValues words 0 n))
    (by simp only [evalExpr?, hready.array, EvalResult.ofOption])
  simp only [assignStorageRef?, supplyQueueStorageResolve hready.contract hready.supplyQueue,
    supplyQueueBackendWrite, EvalResult.bind, bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1

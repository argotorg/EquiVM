import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayStorageAlgebra
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueReady

/-! Exact withdrawal-queue replacement in the source and runtime storage orders. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem withdrawQueueDataBase_eq : solidityBytesDataBaseSlot ⟨21⟩ = UInt256.ofNat
    38878206584692966203415385907871375197469080758325516314230789535345649042549 := by
  native_decide

theorem withdrawQueueDataBase_bounds :
    21 < (solidityBytesDataBaseSlot ⟨21⟩).toNat ∧
      (solidityBytesDataBaseSlot ⟨21⟩).toNat + 2 ^ 251 < UInt256.size := by
  rw [withdrawQueueDataBase_eq]
  decide

theorem withdrawQueueDataSlot_ne_header {i : Nat} (hi : i < 2 ^ 251) :
    (⟨21⟩ : UInt256) ≠ solidityBytesDataBaseSlot ⟨21⟩ + UInt256.ofNat i := by
  intro he
  have hb := withdrawQueueDataBase_bounds
  have hn := congrArg UInt256.toNat he
  rw [uadd_word_ofNat_toNat _ _ (by omega)] at hn
  change 21 = _ at hn
  omega

def updateWithdrawQueueSourceState (evm : State) (queue : List UInt256) : State :=
  { evm with
    accountMap := replaceWordArraySourceAccounts evm.executionEnv.codeOwner evm.accountMap
      ⟨21⟩ (solidityBytesDataBaseSlot ⟨21⟩)
      (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat
      (fun i ↦ queue[i]?.getD ⟨0⟩) queue.length }

theorem updateWithdrawQueueAccounts_match (evm : State) (queue : List UInt256)
    (hold : (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat < 2 ^ 251)
    (hnew : queue.length < 2 ^ 251) :
    (updateWithdrawQueueSourceState evm queue).accountMap =
      replaceWordArrayRuntimeAccounts evm.executionEnv.codeOwner evm.accountMap
        ⟨21⟩ (solidityBytesDataBaseSlot ⟨21⟩)
        (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat
        (fun i ↦ queue[i]?.getD ⟨0⟩) queue.length :=
  replaceWordArrayAccounts_match _ _ _ _ _ _ _
    (fun j hj ↦ withdrawQueueDataSlot_ne_header (by omega))
    (fun j hj ↦ withdrawQueueDataSlot_ne_header (by omega))

theorem updateWithdrawQueueBackendWrite (evm : State) (queue : List UInt256) :
    config.storageBackend.write ⟨"withdrawQueue", []⟩
      (.dynamicArray (.elem (.bytes abiBytes32Width))) (.array (queue.map wordBytes32Value)) evm =
      .ok (updateWithdrawQueueSourceState evm queue) := by
  have hlen : solidityDynamicLength? stringStorageLayout evm ⟨"withdrawQueue", []⟩ =
      .ok (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat :=
    storageDynamicArrayLength (cfg := config) (elem := .elem (.bytes abiBytes32Width)) rfl rfl
  rw [← wordArrayValues_getD queue]
  exact solidityReplaceWordArray withdrawQueueElementLayout rfl evm _ _ hlen

theorem updateWithdrawQueueStorageResolve {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "withdrawQueue" = none) :
    resolveStorageRef? config frame evm ⟨"withdrawQueue", []⟩ =
      .ok (⟨"withdrawQueue", []⟩, .dynamicArray (.elem (.bytes abiBytes32Width))) := by
  simp only [resolveStorageRef?, hbase, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, bind, pure, hcontract]
  rfl

theorem updateWithdrawQueueAssign {frame : Frame} {evm : State} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor) :
    ExecStmt config frame evm
      (.assign .storage ⟨"withdrawQueue", []⟩ (.var "newWithdrawQueue"))
      (.ok frame (updateWithdrawQueueSourceState evm queue)) := by
  apply ExecStmt.assign (value := .array (queue.map wordBytes32Value))
    (by simp only [evalExpr?, h.queue, EvalResult.ofOption])
  simp only [assignStorageRef?, updateWithdrawQueueStorageResolve h.contract h.withdrawQueue,
    updateWithdrawQueueBackendWrite, EvalResult.bind, bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1

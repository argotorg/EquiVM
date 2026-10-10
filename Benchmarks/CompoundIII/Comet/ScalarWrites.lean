import Benchmarks.CompoundIII.Comet.PackedWrites
import Benchmarks.CompoundIII.Comet.AccrualTime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def storeLastAccrual (evm : EVM.State) (time : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (packedWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) time 26 5)

def storeTotalsIndex (evm : EVM.State) (borrow : Bool) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      value (totalsIndexOffset borrow).val 8)

theorem assignLastAccrual (evm : EVM.State) (locals imms : Store) (time : UInt256)
    (hlocal : locals.get? "lastAccrualTime" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"lastAccrualTime", []⟩ (.int time.toNat) =
      .ok ({ contract := contract, locals := locals, immutables := imms }, storeLastAccrual evm time) := by
  apply assignStorageRef_storage_scalar (hbackend := rfl)
    (loc := { slot := ⟨1⟩, offset := 26, size := 5, hbound := by decide,
              type := .int (.uint ⟨40, by decide⟩) })
    (er := ⟨"lastAccrualTime", []⟩) (ty := .elem (.int (.uint ⟨40, by decide⟩))) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_packed_int evm ⟨1⟩ time 26 5 _

theorem assignTotalsIndex (evm : EVM.State) (locals imms : Store) (borrow : Bool)
    (value : UInt256) (hlocal : locals.get? (totalsIndexName borrow) = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨totalsIndexName borrow, []⟩ (.int value.toNat) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeTotalsIndex evm borrow value) := by
  apply assignStorageRef_storage_scalar (hbackend := rfl)
    (loc := { slot := ⟨0⟩, offset := totalsIndexOffset borrow, size := 8,
              hbound := by cases borrow <;> decide, type := .int (.uint ⟨64, by decide⟩) })
    (er := ⟨totalsIndexName borrow, []⟩) (ty := .elem (.int (.uint ⟨64, by decide⟩))) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · cases borrow <;> rfl
  · cases borrow <;> rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_packed_int evm ⟨0⟩ value (totalsIndexOffset borrow) 8 _

end Benchmarks.CompoundIII.Comet

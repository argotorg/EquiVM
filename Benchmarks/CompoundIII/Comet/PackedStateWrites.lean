import Benchmarks.CompoundIII.Comet.PackedWrites
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: source-state update for one byte-aligned packed storage field.
def storePackedWord (evm : EVM.State) (slot data : UInt256) (offset size : Nat) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (packedWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) data offset size)

-- LIBRARY CANDIDATE: repeated writes to one slot, including an absent account.
theorem storageStore_same (evm : EVM.State) (owner : AccountAddress)
    (slot first last : UInt256) :
    Solm.EVM.storageStore (Solm.EVM.storageStore evm owner slot first) owner slot last =
      Solm.EVM.storageStore evm owner slot last := by
  have hm : (Solm.EVM.storageStore (Solm.EVM.storageStore evm owner slot first)
      owner slot last).accountMap = (Solm.EVM.storageStore evm owner slot last).accountMap := by
    rw [storageStore_accountMap, storageStore_accountMap, ← sstoreAccountMap_self_update,
      storageStore_accountMap]
  have hs := stateAccountMapUpdate_trans
    (storageStore_eq_accountMap_update evm owner slot first)
    (storageStore_eq_accountMap_update (Solm.EVM.storageStore evm owner slot first)
      owner slot last)
  rw [hm, storageStore_eq_accountMap_update] at hs
  exact hs.symm

-- LIBRARY CANDIDATE: compose read-modify-write operations without a presence assumption.
theorem storageModify_compose (evm : EVM.State) (slot : UInt256) (f g : UInt256 → UInt256) :
    (let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))
     Solm.EVM.storageStore evm' evm'.executionEnv.codeOwner slot
      (g (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner slot))) =
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (g (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  dsimp only
  simp only [storageStore_executionEnv]
  cases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none => simp only [storageStore_absent evm _ hacc]
  | some acc =>
      rw [storageLoad_storageStore_same_present evm _ hacc, storageStore_same]

theorem storePackedWord_after_modify (evm : EVM.State) (slot data : UInt256)
    (offset size : Nat) (f : UInt256 → UInt256) :
    storePackedWord
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))
      slot data offset size =
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (packedWriteWord (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))
        data offset size) := storageModify_compose evm slot f (packedWriteWord · data offset size)

end Benchmarks.CompoundIII.Comet

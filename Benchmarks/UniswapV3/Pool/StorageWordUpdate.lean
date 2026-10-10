import Benchmarks.UniswapV3.Pool.PackedPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def modifyStorageWord (evm : EVM.State) (slot : UInt256) (f : UInt256 → UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner slot
    (f (EVM.storageLoad evm evm.executionEnv.codeOwner slot))

-- LIBRARY CANDIDATE: successive word updates at one slot compose, including absent accounts.
theorem modifyStorageWord_comp (evm : EVM.State) (slot : UInt256) (f g : UInt256 → UInt256) :
    modifyStorageWord (modifyStorageWord evm slot f) slot g =
      modifyStorageWord evm slot (fun old ↦ g (f old)) := by
  unfold modifyStorageWord
  cases ha : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
    rw [storageStore_absent evm _ ha, storageStore_absent evm _ ha,
      storageStore_absent evm _ ha]
  | some acc =>
    rw [storageStore_executionEnv, storageLoad_storageStore_same_present evm _ ha,
      storageStore_overwrite]

-- GENERALIZES masked packed writes to a storage location of any scalar type.
theorem storageLocStore_masked (evm : EVM.State) (loc : StorageLoc)
    (value : Value) (word mask field : UInt256)
    (hv : valueToWord value = some word) (hbit : loc.bitOffset = none)
    (hmask : mask.toNat = (2 ^ (8 * loc.offset.val) - 1) |||
      (2 ^ 256 - 2 ^ (8 * (loc.offset.val + loc.size.val))))
    (hfield : field.toNat = (word.toNat % 2 ^ (8 * loc.size.val)) * 2 ^ (8 * loc.offset.val)) :
    storageLocStore evm loc value =
      some (modifyStorageWord evm loc.slot (fun old ↦ UInt256.lor (UInt256.land old mask) field)) := by
  apply storageLocStore_packed_of_toNat evm loc value word _ hv hbit
  rw [packedMaskedWord_toNat _ mask field (8 * loc.offset.val) (8 * loc.size.val)
    (word.toNat % 2 ^ (8 * loc.size.val))
    (by have h := loc.hbound; omega) (by simpa only [Nat.mul_add] using hmask)
    hfield (Nat.mod_lt _ (by positivity))]
  simp only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul,
    Nat.mul_add, Nat.add_mul, Nat.mul_comm]

end Benchmarks.UniswapV3.Pool

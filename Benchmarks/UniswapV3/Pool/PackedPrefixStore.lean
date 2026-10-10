import Benchmarks.UniswapV3.Pool.OracleInitializeStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: append one packed field to an already written low prefix.
theorem storageLocStore_extendPrefix (evm : EVM.State) (loc : StorageLoc)
    (value : Value) (word low next : UInt256)
    (hword : valueToWord value = some word) (hbit : loc.bitOffset = none)
    (hlow : low.toNat < 2 ^ (8 * loc.offset.val))
    (hnext : next.toNat = low.toNat + 2 ^ (8 * loc.offset.val) *
      (word.toNat % 2 ^ (8 * loc.size.val))) :
    let old := EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot
    storageLocStore
      (EVM.storageStore evm evm.executionEnv.codeOwner loc.slot
        (packedPrefixWord old low (8 * loc.offset.val))) loc value =
      some (EVM.storageStore evm evm.executionEnv.codeOwner loc.slot
        (packedPrefixWord old next (8 * (loc.offset.val + loc.size.val)))) := by
  dsimp only
  let old := EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot
  let mid := EVM.storageStore evm evm.executionEnv.codeOwner loc.slot
    (packedPrefixWord old low (8 * loc.offset.val))
  cases ha : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
    rw [storageStore_absent evm _ ha, storageStore_absent evm _ ha]
    exact storageLocStore_absent evm loc value word hword ha
  | some acc =>
    have hb : loc.offset.val + loc.size.val ≤ 32 := by have h := loc.hbound; omega
    have hwidth : 8 * (loc.offset.val + loc.size.val) ≤ 256 := by omega
    have hstart : 8 * loc.offset.val ≤ 8 * (loc.offset.val + loc.size.val) := by omega
    have hfit : next.toNat < 2 ^ (8 * (loc.offset.val + loc.size.val)) := by
      rw [hnext, Nat.mul_add, Nat.pow_add]
      have hp : 0 < 2 ^ (8 * loc.size.val) := by positivity
      have hm := Nat.mod_lt word.toNat hp
      calc
        low.toNat + 2 ^ (8 * loc.offset.val) * (word.toNat % 2 ^ (8 * loc.size.val)) <
            2 ^ (8 * loc.offset.val) +
              2 ^ (8 * loc.offset.val) * (word.toNat % 2 ^ (8 * loc.size.val)) :=
          Nat.add_lt_add_right hlow _
        _ = 2 ^ (8 * loc.offset.val) * (word.toNat % 2 ^ (8 * loc.size.val) + 1) := by ring
        _ ≤ 2 ^ (8 * loc.offset.val) * 2 ^ (8 * loc.size.val) :=
          Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hm)
    have hs : storageLocStore mid loc value =
        some (EVM.storageStore mid mid.executionEnv.codeOwner loc.slot
          (packedPrefixWord old next (8 * (loc.offset.val + loc.size.val)))) := by
      apply storageLocStore_packed_of_toNat mid loc value word _ hword hbit
      rw [packedPrefixWord_toNat old next _ hwidth hfit]
      dsimp only [mid]
      rw [storageStore_executionEnv, storageLoad_storageStore_same_present evm _ ha]
      simp only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      rw [packedPrefixWord_mod old low _ (hstart.trans hwidth) hlow,
        packedPrefixWord_div old low _ _ hstart hwidth hlow, hnext]
    simpa only [mid, storageStore_executionEnv, storageStore_overwrite] using hs

def packedAppend (low field : UInt256) (offset width : Nat) : UInt256 :=
  UInt256.ofNat (low.toNat + 2 ^ offset * (field.toNat % 2 ^ width))

theorem packedAppend_bound (low field : UInt256) (offset width : Nat)
    (hlow : low.toNat < 2 ^ offset) :
    low.toNat + 2 ^ offset * (field.toNat % 2 ^ width) < 2 ^ (offset + width) := by
  rw [Nat.pow_add]
  have hm := Nat.mod_lt field.toNat (by positivity : 0 < 2 ^ width)
  calc
    low.toNat + 2 ^ offset * (field.toNat % 2 ^ width) <
        2 ^ offset + 2 ^ offset * (field.toNat % 2 ^ width) := Nat.add_lt_add_right hlow _
    _ = 2 ^ offset * (field.toNat % 2 ^ width + 1) := by ring
    _ ≤ 2 ^ offset * 2 ^ width := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hm)

theorem packedAppend_toNat (low field : UInt256) (offset width : Nat)
    (hb : offset + width ≤ 256) (hlow : low.toNat < 2 ^ offset) :
    (packedAppend low field offset width).toNat =
      low.toNat + 2 ^ offset * (field.toNat % 2 ^ width) := by
  apply UInt256.toNat_ofNat_of_lt
  exact lt_of_lt_of_le (packedAppend_bound low field offset width hlow)
    (Nat.pow_le_pow_right (by decide) hb)

theorem packedAppend_lt (low field : UInt256) (offset width : Nat)
    (hb : offset + width ≤ 256) (hlow : low.toNat < 2 ^ offset) :
    (packedAppend low field offset width).toNat < 2 ^ (offset + width) := by
  rw [packedAppend_toNat low field offset width hb hlow]
  exact packedAppend_bound low field offset width hlow

end Benchmarks.UniswapV3.Pool

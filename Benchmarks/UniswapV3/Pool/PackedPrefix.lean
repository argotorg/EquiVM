import Benchmarks.UniswapV3.Pool.PackedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: repeated writes at the same account and slot retain the last value.
theorem storageStore_overwrite (evm : EVM.State) (owner : AccountAddress)
    (slot first last : UInt256) :
    EVM.storageStore (EVM.storageStore evm owner slot first) owner slot last =
      EVM.storageStore evm owner slot last := by
  have hstate := stateAccountMapUpdate_trans
    (storageStore_eq_accountMap_update evm owner slot first)
    (storageStore_eq_accountMap_update (EVM.storageStore evm owner slot first) owner slot last)
  rw [← hstate, storageStore_accountMap, storageStore_accountMap,
    ← sstoreAccountMap_self_update]
  simpa only [storageStore_accountMap] using storageStore_eq_accountMap_update evm owner slot last

-- A low field with the original bits above a boundary retained.
def packedPrefixWord (old value : UInt256) (bits : Nat) : UInt256 :=
  UInt256.ofNat (value.toNat + 2 ^ bits * (old.toNat / 2 ^ bits))

theorem packedPrefixWord_toNat (old value : UInt256) (bits : Nat)
    (hb : bits ≤ 256) (hv : value.toNat < 2 ^ bits) :
    (packedPrefixWord old value bits).toNat = value.toNat + 2 ^ bits * (old.toNat / 2 ^ bits) := by
  have hp : 0 < 2 ^ bits := by positivity
  have hpow : 2 ^ bits * 2 ^ (256 - bits) = UInt256.size := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hb]
    rfl
  have hq : old.toNat / 2 ^ bits < 2 ^ (256 - bits) := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [Nat.mul_comm, hpow]
    exact old.val.isLt
  apply UInt256.toNat_ofNat_of_lt
  calc
    value.toNat + 2 ^ bits * (old.toNat / 2 ^ bits) <
        2 ^ bits + 2 ^ bits * (old.toNat / 2 ^ bits) := Nat.add_lt_add_right hv _
    _ = 2 ^ bits * (old.toNat / 2 ^ bits + 1) := by ring
    _ ≤ 2 ^ bits * 2 ^ (256 - bits) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hq)
    _ = UInt256.size := hpow

theorem packedPrefixWord_mod (old value : UInt256) (bits : Nat)
    (hb : bits ≤ 256) (hv : value.toNat < 2 ^ bits) :
    (packedPrefixWord old value bits).toNat % 2 ^ bits = value.toNat := by
  rw [packedPrefixWord_toNat old value bits hb hv, Nat.add_mod, Nat.mul_mod_right,
    Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hv]

theorem packedPrefixWord_div (old value : UInt256) (bits top : Nat)
    (hb : bits ≤ top) (ht : top ≤ 256) (hv : value.toNat < 2 ^ bits) :
    (packedPrefixWord old value bits).toNat / 2 ^ top = old.toNat / 2 ^ top := by
  have hp : 0 < 2 ^ bits := by positivity
  have hpow : 2 ^ top = 2 ^ bits * 2 ^ (top - bits) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hb]
  rw [packedPrefixWord_toNat old value bits (hb.trans ht) hv, hpow,
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hv, Nat.zero_add]

end Benchmarks.UniswapV3.Pool

import Benchmarks.Midnight.CollateralStorage
import Benchmarks.Midnight.Uint128HighStore

/-! The packed uint128 array write used by collateral supply and withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def collateralWriteWord (old index value : UInt256) : UInt256 :=
  let shift := UInt256.ofNat (128 * (index.toNat % 2))
  UInt256.lor (UInt256.land (UInt256.lnot (UInt256.shiftLeft uint128Mask shift)) old)
    (UInt256.shiftLeft (UInt256.land value uint128Mask) shift)

def collateralWriteState (evm : EVM.State) (id user index value : UInt256) : EVM.State :=
  let slot := (collateralLoc id user index).slot
  EVM.storageStore evm evm.executionEnv.codeOwner slot
    (collateralWriteWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot) index value)

theorem collateralWriteWord_toNat (old index value : UInt256) :
    (collateralWriteWord old index value).toNat =
      old.toNat % 2^(128 * (index.toNat % 2)) +
      (value.toNat % 2^128) * 2^(128 * (index.toNat % 2)) +
      old.toNat / 2^(128 * (index.toNat % 2) + 128) *
        2^(128 * (index.toNat % 2) + 128) := by
  let shift := UInt256.ofNat (128 * (index.toNat % 2))
  have hs : shift.toNat = 128 * (index.toNat % 2) :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hv : (UInt256.land value uint128Mask).toNat = value.toNat % 2^128 := by
    rw [uland_toNat]; exact nat_land_mask_eq_mod _ 128
  have hp : value.toNat % 2^128 < 2^128 := Nat.mod_lt _ (by decide)
  have hf : (UInt256.shiftLeft (UInt256.land value uint128Mask) shift).toNat =
      (value.toNat % 2^128) * 2^(128 * (index.toNat % 2)) := by
    rw [shiftLeft_toNat_of_noOverflow _ _ (by rw [hs]; omega), hv, hs]
    rw [hv, hs]
    rcases Nat.mod_two_eq_zero_or_one index.toNat with he | he <;> rw [he] <;>
      norm_num only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.mul_one] <;>
      change _ < 2^256 <;> omega
  have hm : (UInt256.lnot (UInt256.shiftLeft uint128Mask shift)).toNat =
      (2^(128 * (index.toNat % 2)) - 1) |||
        (2^256 - 2^(128 * (index.toNat % 2) + 128)) := by
    dsimp only [shift]
    rcases Nat.mod_two_eq_zero_or_one index.toNat with he | he <;> rw [he] <;> decide
  dsimp only [collateralWriteWord]
  rw [u256_land_comm (UInt256.lnot _)]
  exact packedMaskedWord_toNat old _ _ (128 * (index.toNat % 2)) 128 (value.toNat % 2^128)
    (by omega) hm hf hp

theorem storageLocStore_collateral (evm : EVM.State) (id user index value : UInt256) :
    storageLocStore evm (collateralLoc id user index) (.int value.toNat) =
      some (collateralWriteState evm id user index value) := by
  apply storageLocStore_packed_of_toNat evm _ _ value _
    (by change some (EVM.wordOfInt (Int.ofNat value.toNat)) = some value
        rw [wordOfInt_ofNat_toNat]) rfl
  rw [collateralWriteWord_toNat]
  dsimp only [collateralLoc]
  change _ =
    (EVM.storageLoad evm evm.executionEnv.codeOwner
      (positionSlot id user + ⟨3⟩ + UInt256.ofNat (index.toNat / 2))).toNat %
        256^(16 * (index.toNat % 2)) +
    256^(16 * (index.toNat % 2)) * (value.toNat % 256^16) +
    256^(16 * (index.toNat % 2) + 16) *
      ((EVM.storageLoad evm evm.executionEnv.codeOwner
        (positionSlot id user + ⟨3⟩ + UInt256.ofNat (index.toNat / 2))).toNat /
          256^(16 * (index.toNat % 2) + 16))
  rcases Nat.mod_two_eq_zero_or_one index.toNat with he | he <;>
    simp only [he, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.pow_zero,
      Nat.mod_one, Nat.zero_mul, Nat.one_mul, Nat.add_zero,
      show (256 : Nat)^16 = 2^128 from by decide,
      show (256 : Nat)^(16+16) = 2^(128+128) from by decide, Nat.mul_comm]

@[simp] theorem collateralWriteState_env (evm : EVM.State) (id user index value : UInt256) :
    (collateralWriteState evm id user index value).executionEnv = evm.executionEnv := by
  simp only [collateralWriteState, storageStore_executionEnv]

end Benchmarks.Midnight

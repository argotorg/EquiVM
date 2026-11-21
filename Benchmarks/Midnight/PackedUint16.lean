import Benchmarks.Midnight.PackedStore

/-! Writes to the sixteen two-byte fields in an EVM storage word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def packedUInt16Int : IntType := .uint ⟨16, by decide⟩

def uint16Loc (slot : UInt256) (i : Fin 16) : StorageLoc :=
  { slot := slot, offset := ⟨2 * i.val, by omega⟩, size := 2,
    type := .int packedUInt16Int, hbound := by change 2 * i.val + 2 - 1 < 32; omega }

def setUint16Word (old value : UInt256) (i : Fin 16) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat (16 * i.val)))))
    (UInt256.shiftLeft (UInt256.land value ⟨65535⟩) (UInt256.ofNat (16 * i.val)))

theorem setUint16Word_toNat (old value : UInt256) (i : Fin 16) :
    (setUint16Word old value i).toNat =
      old.toNat % 2 ^ (16 * i.val) +
      (value.toNat % 2 ^ 16) * 2 ^ (16 * i.val) +
      old.toNat / 2 ^ (16 * i.val + 16) * 2 ^ (16 * i.val + 16) := by
  have hi := i.isLt
  have hb : (UInt256.ofNat (16 * i.val)).toNat = 16 * i.val := by
    apply UInt256.toNat_ofNat_of_lt
    have hlarge : 256 < UInt256.size := by decide
    omega
  have hv : (UInt256.land value ⟨65535⟩).toNat = value.toNat % 2 ^ 16 := by
    rw [uland_toNat]
    exact nat_land_mask_eq_mod _ 16
  apply packedMaskedWord_toNat old _ _ (16 * i.val) 16 (value.toNat % 2 ^ 16) (by omega)
  · clear * - i
    revert i
    native_decide
  · rw [shiftLeft_toNat_of_noOverflow _ _ (by rw [hb]; omega) ?_, hb, hv]
    rw [hb, hv]
    have hfit : value.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
    apply lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hfit (by positivity))
    rw [← Nat.pow_add]
    change 2 ^ (16 + 16 * i.val) ≤ 2 ^ 256
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact Nat.mod_lt _ (by decide)

-- LIBRARY CANDIDATE: arbitrary two-byte field updates, including packed fixed arrays.
theorem storageLocStore_uint16_word (evm : EVM.State) (slot value : UInt256) (i : Fin 16) :
    storageLocStore evm (uint16Loc slot i) (.int (Int.ofNat value.toNat)) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint16Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value i)) := by
  apply storageLocStore_packed_of_toNat evm _ _ value _
    (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
  rw [setUint16Word_toNat]
  change _ =
    (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 256 ^ (2 * i.val) +
      256 ^ (2 * i.val) * (value.toNat % 256 ^ 2) +
      256 ^ (2 * i.val + 2) *
        ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 256 ^ (2 * i.val + 2))
  simp only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  have he : 8 * (2 * i.val) = 16 * i.val := by omega
  have he' : 8 * (2 * i.val + 2) = 16 * i.val + 16 := by omega
  rw [he, he']
  simp only [Nat.mul_comm]

theorem setUint16Word_clean (old value : UInt256) (i : Fin 16) (hvalue : value.toNat < 2 ^ 16) :
    setUint16Word old value i =
      UInt256.lor (UInt256.land old (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩
        (UInt256.ofNat (16 * i.val))))) (UInt256.shiftLeft value (UInt256.ofNat (16 * i.val))) := by
  rw [setUint16Word, u256LandMaskCleanOfToNat value ⟨65535⟩ (by decide) hvalue]

theorem setUint16Word_solc (old value : UInt256) (i : Fin 7) (hvalue : value.toNat < 2 ^ 16) :
    UInt256.lor
      (UInt256.land (UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat (16 * i.val)))
        (UInt256.shiftLeft value (UInt256.ofNat (16 * i.val))))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat (16 * i.val)))) old) =
      setUint16Word old value ⟨i.val, by omega⟩ := by
  have hm : UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat (16 * i.val)) =
      UInt256.ofNat ((2 ^ 16 - 1) * 2 ^ (16 * i.val)) := by
    clear * - i
    revert i
    decide
  have hs : UInt256.land (UInt256.shiftLeft ⟨65535⟩ (UInt256.ofNat (16 * i.val)))
      (UInt256.shiftLeft value (UInt256.ofNat (16 * i.val))) =
      UInt256.shiftLeft value (UInt256.ofNat (16 * i.val)) := by
    rw [u256_land_comm, hm]
    exact shiftLeft_land_mask value 16 (16 * i.val) (by have := i.isLt; omega)
      (by have := i.isLt; omega) hvalue
  rw [hs, setUint16Word_clean old value _ hvalue]
  simp only [u256_lor_comm, u256_land_comm]

end Benchmarks.Midnight

import Benchmarks.Midnight.CalldataDynamicValues

/-! References to dynamic arguments in the external calldata tuple. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def calldataArgumentHead (bytes : ByteArray) (slot : Nat) : UInt256 :=
  UInt256.ofNat 4 + calldataWord bytes slot

def calldataArgumentLength (bytes : ByteArray) (slot : Nat) : UInt256 :=
  calldataWord bytes (calldataArgumentHead bytes slot).toNat

def calldataArgumentPointer (bytes : ByteArray) (slot : Nat) : UInt256 :=
  calldataArgumentHead bytes slot + UInt256.ofNat 32

def CalldataArgumentValid (isBytes : Bool) (bytes : ByteArray) (slot : Nat) : Prop :=
  (calldataWord bytes slot).toNat < 2^64 ∧
    CalldataSliceValid isBytes bytes (calldataArgumentHead bytes slot)

instance (isBytes : Bool) (bytes : ByteArray) (slot : Nat) :
    Decidable (CalldataArgumentValid isBytes bytes slot) := by
  unfold CalldataArgumentValid
  infer_instance

theorem calldataArgumentHead_eq (bytes : ByteArray) (slot : Nat) :
    calldataArgumentHead bytes slot = UInt256.ofNat (4 + (calldataWord bytes slot).toNat) := by
  apply u256_inj
  rw [calldataArgumentHead, uadd_toNat]
  rfl

theorem calldataArgumentHead_toNat {bytes : ByteArray} {slot : Nat}
    (ho : (calldataWord bytes slot).toNat < 2^64) :
    (calldataArgumentHead bytes slot).toNat = 4 + (calldataWord bytes slot).toNat := by
  rw [calldataArgumentHead_eq, UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]

theorem CalldataArgumentValid.bounds {isBytes : Bool} {bytes : ByteArray} {slot : Nat}
    (h : CalldataArgumentValid isBytes bytes slot) :
    (calldataArgumentLength bytes slot).toNat < 2^64 ∧
      (calldataArgumentPointer bytes slot).toNat + calldataSliceStride isBytes *
        (calldataArgumentLength bytes slot).toNat ≤ bytes.size := by
  have hh := calldataArgumentHead_toNat h.1
  have hp : (calldataArgumentPointer bytes slot).toNat =
      (calldataArgumentHead bytes slot).toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by rw [hh]; change _ < 2^256; have := h.1; omega)
  exact ⟨h.2.2.2.1, by rw [hp]; exact h.2.2.2.2⟩

theorem decodeCalldataArrayWords_valid {bytes : ByteArray} {slot : Nat}
    (hv : CalldataArgumentValid false bytes slot) :
    decodeCalldataArrayWords bytes slot = some
      (calldataArrayWords bytes (calldataArgumentLength bytes slot).toNat
        (calldataArgumentPointer bytes slot).toNat) := by
  have hh := calldataArgumentHead_toNat hv.1
  have hp : (calldataArgumentPointer bytes slot).toNat =
      (calldataArgumentHead bytes slot).toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by rw [hh]; change _ < 2^256; have := hv.1; omega)
  have hs := hv.2
  rw [calldataArgumentHead_eq] at hs
  simp only [decodeCalldataArrayWords, hv.1, if_true, hs,
    calldataArgumentLength, hp, hh]

theorem decodeCalldataArrayWords_invalid {bytes : ByteArray} {slot : Nat}
    (hv : ¬ CalldataArgumentValid false bytes slot) :
    decodeCalldataArrayWords bytes slot = none := by
  unfold decodeCalldataArrayWords
  by_cases ho : (calldataWord bytes slot).toNat < 2^64
  · have hs : ¬ CalldataSliceValid false bytes
        (UInt256.ofNat (4 + (calldataWord bytes slot).toNat)) := by
      intro hs
      exact hv ⟨ho, by simpa only [calldataArgumentHead_eq] using hs⟩
    simp only [ho, hs, if_true, if_false]
  · simp only [ho, if_false]

theorem decodeCalldataBytes_valid {bytes : ByteArray} {slot : Nat}
    (hv : CalldataArgumentValid true bytes slot) :
    decodeCalldataBytes bytes slot = some
      (bytes.extract (calldataArgumentPointer bytes slot).toNat
        ((calldataArgumentPointer bytes slot).toNat +
          (calldataArgumentLength bytes slot).toNat)) := by
  have hh := calldataArgumentHead_toNat hv.1
  have hp : (calldataArgumentPointer bytes slot).toNat =
      (calldataArgumentHead bytes slot).toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by rw [hh]; change _ < 2^256; have := hv.1; omega)
  have hs := hv.2
  rw [calldataArgumentHead_eq] at hs
  simp only [decodeCalldataBytes, hv.1, if_true, hs, calldataArgumentLength, hp, hh]

theorem decodeCalldataBytes_invalid {bytes : ByteArray} {slot : Nat}
    (hv : ¬ CalldataArgumentValid true bytes slot) :
    decodeCalldataBytes bytes slot = none := by
  unfold decodeCalldataBytes
  by_cases ho : (calldataWord bytes slot).toNat < 2^64
  · have hs : ¬ CalldataSliceValid true bytes
        (UInt256.ofNat (4 + (calldataWord bytes slot).toNat)) := by
      intro hs
      exact hv ⟨ho, by simpa only [calldataArgumentHead_eq] using hs⟩
    simp only [ho, hs, if_true, if_false]
  · simp only [ho, if_false]

end Benchmarks.Midnight

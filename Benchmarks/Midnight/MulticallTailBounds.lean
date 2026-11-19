import Benchmarks.Midnight.CalldataPaddedRead

/-! Signed bounds for direct references to the bytes elements of multicall calldata. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxHeartbeats 1000000

def multicallTailBound (bytes : ByteArray) (base : UInt256) : UInt256 :=
  UInt256.sub (UInt256.sub (UInt256.ofNat bytes.size) base) (UInt256.ofNat 31)

def multicallTailOffset (bytes : ByteArray) (base : UInt256) (index : Nat) : UInt256 :=
  calldataWord bytes (base.toNat + 32 * index)

def multicallTailHead (bytes : ByteArray) (base : UInt256) (index : Nat) : UInt256 :=
  base + multicallTailOffset bytes base index

def multicallTailLength (bytes : ByteArray) (base : UInt256) (index : Nat) : UInt256 :=
  calldataWord bytes (multicallTailHead bytes base index).toNat

def multicallTailPointer (bytes : ByteArray) (base : UInt256) (index : Nat) : UInt256 :=
  UInt256.ofNat 32 + multicallTailHead bytes base index

def MulticallTailValid (bytes : ByteArray) (base : UInt256) (index : Nat) : Prop :=
  UInt256.sltBool (multicallTailOffset bytes base index) (multicallTailBound bytes base) = true ∧
    (multicallTailLength bytes base index).toNat < 2^64 ∧
    UInt256.sgtBool (multicallTailPointer bytes base index)
      (UInt256.sub (UInt256.ofNat bytes.size) (multicallTailLength bytes base index)) = false

instance (bytes : ByteArray) (base : UInt256) (index : Nat) :
    Decidable (MulticallTailValid bytes base index) := by
  unfold MulticallTailValid
  infer_instance

def multicallBytesAt (bytes : ByteArray) (base : UInt256) (index : Nat) : ByteArray :=
  bytes.readWithPadding (multicallTailPointer bytes base index).toNat
    (multicallTailLength bytes base index).toNat

theorem multicallTailBound_toNat {bytes : ByteArray} {base : UInt256}
    (hs : bytes.size < UInt256.size) (hb : base.toNat + 32 ≤ bytes.size) :
    (multicallTailBound bytes base).toNat = bytes.size - base.toNat - 31 := by
  have hsub := usub_ofNat_word_toNat (by omega : base.toNat ≤ bytes.size) hs
  unfold multicallTailBound
  rw [usub_toNat (by rw [hsub]; change 31 ≤ bytes.size - base.toNat; omega), hsub]
  rfl

theorem multicallTailHead_bounded_or_zero {bytes : ByteArray} {base : UInt256} {index : Nat}
    (hs : bytes.size < 2^255) (hb : base.toNat + 32 ≤ bytes.size)
    (ho : UInt256.sltBool (multicallTailOffset bytes base index)
      (multicallTailBound bytes base) = true) :
    (multicallTailHead bytes base index).toNat + 32 ≤ bytes.size ∨
      multicallTailLength bytes base index = ⟨0⟩ := by
  have hs' : bytes.size < UInt256.size := by change _ < 2^256; omega
  have hbound := multicallTailBound_toNat hs' hb
  have hboundlo : ¬ 2^255 ≤ (multicallTailBound bytes base).toNat := by rw [hbound]; omega
  let offset := multicallTailOffset bytes base index
  change UInt256.sltBool offset (multicallTailBound bytes base) = true at ho
  have hhead : (multicallTailHead bytes base index).toNat =
      (base.toNat + offset.toNat) % UInt256.size := uadd_toNat _ _
  by_cases hlo : offset.toNat < 2^255
  · have hlt : offset.toNat < bytes.size - base.toNat - 31 := by
      simp only [UInt256.sltBool, show ¬ 2^255 ≤ offset.toNat from by omega,
        hboundlo, if_false, decide_eq_true_eq] at ho
      change offset.toNat < (multicallTailBound bytes base).toNat at ho
      rwa [hbound] at ho
    left
    rw [hhead, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
    omega
  · by_cases hw : base.toNat + offset.toNat < UInt256.size
    · right
      apply calldataWord_eq_zero_of_ge
      rw [hhead, Nat.mod_eq_of_lt hw]
      omega
    · left
      have hoff := offset.val.isLt
      change offset.toNat < UInt256.size at hoff
      rw [hhead, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

theorem MulticallTailValid.bounds {bytes : ByteArray} {base : UInt256} {index : Nat}
    (h : MulticallTailValid bytes base index) (hs : bytes.size < 2^255)
    (hb : base.toNat + 32 ≤ bytes.size) :
    (multicallTailLength bytes base index).toNat = 0 ∨
      (multicallTailHead bytes base index).toNat + 32 +
        (multicallTailLength bytes base index).toNat ≤ bytes.size := by
  rcases multicallTailHead_bounded_or_zero hs hb h.1 with hhead | hz
  · right
    have hp : (multicallTailPointer bytes base index).toNat =
        (multicallTailHead bytes base index).toNat + 32 := by
      rw [multicallTailPointer, u256_add_comm]
      exact uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hn := h.2.1
    have hc := h.2.2
    have hp0 : ¬ 2^255 ≤ (multicallTailPointer bytes base index).toNat := by rw [hp]; omega
    by_cases he : (multicallTailLength bytes base index).toNat ≤ bytes.size
    · have hd := usub_ofNat_word_toNat he (by change bytes.size < 2^256; omega)
      have hd0 : ¬ 2^255 ≤
          (UInt256.sub (UInt256.ofNat bytes.size) (multicallTailLength bytes base index)).toNat := by
        rw [hd]
        omega
      simp only [UInt256.sgtBool, hp0, hd0, if_false, decide_eq_false_iff_not] at hc
      change ¬ (UInt256.sub (UInt256.ofNat bytes.size)
        (multicallTailLength bytes base index)).toNat <
          (multicallTailPointer bytes base index).toNat at hc
      rw [hd, hp] at hc
      omega
    · have hd := usub_toNat_underflow (a := UInt256.ofNat bytes.size)
        (b := multicallTailLength bytes base index)
        (by rw [UInt256.toNat_ofNat_of_lt (by change bytes.size < 2^256; omega)]; omega)
      have hd0 : 2^255 ≤
          (UInt256.sub (UInt256.ofNat bytes.size) (multicallTailLength bytes base index)).toNat := by
        rw [hd, UInt256.toNat_ofNat_of_lt (by change bytes.size < 2^256; omega)]
        change 2^255 ≤ 2^256 + bytes.size - (multicallTailLength bytes base index).toNat
        omega
      simp only [UInt256.sgtBool, hp0, hd0, if_false, if_true] at hc
      contradiction
  · exact Or.inl (congrArg UInt256.toNat hz)

theorem MulticallTailValid.copyBounds {bytes : ByteArray} {base : UInt256} {index : Nat}
    (h : MulticallTailValid bytes base index) (hs : bytes.size < 2^255)
    (hb : base.toNat + 32 ≤ bytes.size) :
    (multicallTailLength bytes base index).toNat = 0 ∨
      (multicallTailPointer bytes base index).toNat +
        (multicallTailLength bytes base index).toNat ≤ bytes.size := by
  rcases h.bounds hs hb with hz | hbound
  · exact Or.inl hz
  · right
    rw [multicallTailPointer, u256_add_comm,
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]
    exact hbound

end Benchmarks.Midnight

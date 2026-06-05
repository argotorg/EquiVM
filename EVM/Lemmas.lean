import EVM.Types

namespace EVM

-- These theoreoms are used by Act.Storage.
-- They should be implemented in EVMLean and become public there at some point

    -- | A bound for the natural number value of a list of bytes.
lemma fromBytes'_le  : Ethereum.fromBytes' bs < 2^(8 * bs.length) := by
  induction bs with
  | nil => unfold Ethereum.fromBytes'; simp
  | cons b bs ih =>
    unfold Ethereum.fromBytes'
    have h := b.toFin.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have _ :=
      Nat.add_le_of_le_sub
        (Nat.one_le_pow _ _ (by decide))
        (Nat.le_sub_one_of_lt ih)
    linarith

    -- | A bound for the natural number value of a list of bytes.
lemma fromByteArrayBigEndian_le {bs : ByteArray}  : Ethereum.fromByteArrayBigEndian bs < 2^(8 * bs.toList.length) := by
  simp [Ethereum.fromByteArrayBigEndian, Ethereum.fromBytesBigEndian]
  simpa [List.length_reverse] using (fromBytes'_le (bs := bs.toList.reverse))


-- | If n < 2⁸ᵏ, then (toBytes' n).length ≤ k.
lemma toBytes'_le {k : ℕ} (h : n < 2 ^ (8 * k)) : (Ethereum.toBytes' n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    simp at h
    rw [h]
    simp [Ethereum.toBytes']
  | succ e ih =>
    match n with
    | .zero => simp [Ethereum.toBytes']
    | .succ n =>
      unfold Ethereum.toBytes'
      simp
      apply ih (Nat.div_lt_of_lt_mul _)
      rw [Nat.mul_succ, Nat.pow_add] at h
      linarith

-- | If n < 2²⁵⁶, then (toBytes' n).length ≤ 32.
lemma toBytes'_UInt256_le (h : n < Ethereum.UInt256.size) : (Ethereum.toBytes' n).length ≤ 32 := toBytes'_le h

def UInt256.toBytes (u : Ethereum.UInt256) : List UInt8 :=
  let b := Ethereum.toBytes' u.val
  List.replicate (32 - b.length) 0 ++ b

def UInt256.toBytesWithSizeProof (val : Ethereum.UInt256) : { b : List UInt8 // b.length = 32 } :=
  let b := Ethereum.toBytes' val.val
  let pad := List.replicate (32 - b.length) 0 ++ b
  ⟨pad,
    by
      simp [pad]
      have hb : b.length ≤ 32 := by
        have ha : (val.toNat : ℕ) < 2 ^ (8 * 32) := by
          simp [Ethereum.UInt256.size, Ethereum.UInt256.toNat]
        simpa [b, BE] using toBytes'_le (k := 32) ha
      have h32 : 32 < USize.size := by
        rcases System.Platform.numBits_eq with h | h <;> rw [USize.size, h] <;> norm_num
      have h32' : (OfNat.ofNat 32 : USize).toNat = 32 := by
        exact USize.toNat_ofNat_of_le_of_lt (n := 32) (i := 32) h32 le_rfl
      have hbsize : (OfNat.ofNat b.length : USize).toNat = b.length := by
        exact USize.toNat_ofNat_of_le_of_lt (n := 32) (i := b.length) h32 hb
      omega
    ⟩

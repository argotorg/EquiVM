import EVM.Types

namespace EVM

-- These theoreoms are used by Stele.Storage.
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

/-! ## Bytes and words -/

section Bytes

open Ethereum

/-- Appending high-order zero bytes does not change the little-endian value. -/
theorem fromBytes'_append_zeros (l : List UInt8) (k : ℕ) :
    fromBytes' (l ++ List.replicate k 0) = fromBytes' l := by
  induction l with
  | nil =>
    induction k with
    | zero => rfl
    | succ k ih => simp only [List.nil_append, List.replicate, fromBytes'] at ih ⊢; rw [ih]; rfl
  | cons b bs ih => simp only [List.cons_append, fromBytes']; rw [ih]

/-- `fromBytes'` inverts `toBytes'`. evmlean has this lemma, but it is private. -/
theorem fromBytes'_toBytes' (x : ℕ) : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp [UInt8.size]
    exact Nat.mod_add_div _ _

/-- `ByteArray.toList` is the list of the underlying array. -/
theorem byteArray_toList_eq_data (b : ByteArray) : b.toList = b.data.toList := by
  show ByteArray.toList.loop b 0 [] = _
  suffices h : ∀ i r, ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i by
    simpa using h 0 []
  intro i r
  induction i, r using ByteArray.toList.loop.induct (bs := b) with
  | case1 i r hlt ih =>
    rw [ByteArray.toList.loop, if_pos hlt, ih, List.reverse_cons, List.append_assoc]
    congr 1
    have hi : i < b.data.size := hlt
    have hlen : i < b.data.toList.length := by rw [Array.length_toList]; exact hi
    have hget : b.get! i = b.data.toList[i]'hlen := by
      rw [Array.getElem_toList]; exact getElem!_pos b.data i hi
    rw [hget, List.singleton_append, List.getElem_cons_drop]
  | case2 i r hge =>
    rw [ByteArray.toList.loop, if_neg hge]
    have : b.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt hge
    simp [List.drop_eq_nil_of_le this]

/-- `UInt256.ofNat` inverts `toNat`. -/
theorem Word.ofNat_toNat (a : Word) : UInt256.ofNat a.toNat = a := by
  have hv : Fin.ofNat UInt256.size a.toNat = a.val :=
    Fin.ext (by rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt a.val.isLt)
  show (⟨Fin.ofNat UInt256.size a.toNat⟩ : UInt256) = a
  rw [hv]

/-- `Word.toBytesBE` returns 32 bytes. -/
theorem Word.toBytesBE_length (w : Word) : (Word.toBytesBE w).length = 32 := by
  have h : (toBytesBigEndian w.val).length ≤ 32 := toBytesBigEndian_le (k := 32) w.val.isLt
  simp only [Word.toBytesBE, List.length_append, List.length_replicate]
  omega

/-- `fromBytesBigEndian` inverts `Word.toBytesBE`. -/
theorem Word.fromBytesBigEndian_toBytesBE (w : Word) :
    fromBytesBigEndian (Word.toBytesBE w) = w.toNat := by
  simp only [Word.toBytesBE, fromBytesBigEndian, toBytesBigEndian, Function.comp_apply,
    List.reverse_append, List.reverse_reverse, List.reverse_replicate, fromBytes'_append_zeros,
    fromBytes'_toBytes']
  rfl

end Bytes

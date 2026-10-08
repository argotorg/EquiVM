import Benchmarks.CompoundIII.Comet.PackedFields
import Benchmarks.CompoundIII.Comet.StaticReturns
import Std.Tactic.BVDecide

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the signed integer view of a word round-trips through the EVM cast.
theorem bitvecWordOfInt (x : BitVec 256) : EVM.wordOfInt x.toInt = ⟨x.toFin⟩ := by
  rw [BitVec.toInt_eq_toNat_cond]
  split_ifs with h
  · exact wordOfInt_ofNat_toNat ⟨x.toFin⟩
  · apply u256_inj
    have hx := x.isLt
    have hn : (x.toNat : Int) - (2^256 : Nat) < 0 := by omega
    rw [wordOfInt_toNat_of_neg_of_abs_lt _ hn (by
      change ((x.toNat : Int) - (2^256 : Nat)).natAbs < 2^256
      omega)]
    change 2^256 - ((x.toNat : Int) - (2^256 : Nat)).natAbs = x.toNat
    omega

-- LIBRARY CANDIDATE: source signed casts agree with Lean's bit-vector interpretation.
theorem normalizeSigned_bitvec (width : ABI.BitWidth) (hw : 0 < width.val) (n : Nat) :
    normalizeInt (.sint width) (Int.ofNat n) = (BitVec.ofNat width.val n).toInt := by
  have hp := Nat.two_pow_pred_add_two_pow_pred hw
  simp only [normalizeInt, EVM.twoPow, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  congr 1
  apply propext
  change ((n : Int) % (2^width.val : Nat) < (2^(width.val-1) : Nat)) ↔ _
  rw [← Int.natCast_emod]
  omega

-- LIBRARY CANDIDATE: signed packed loads retain the normalized low field bits.
theorem packedSint_load (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (width : ABI.BitWidth)
    {hbound : offset.val + size.val - 1 < 32} :
    storageLocLoad evm
      { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.sint width) } =
      .int (normalizeInt (.sint width)
        (packedUint (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          offset.val size.val).toNat) := by
  unfold storageLocLoad wordToElem
  change Value.int (normalizeInt (.sint width) (Int.ofNat (fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract
        offset.val (offset.val + size.val))))) = _
  rw [List.extract_eq_take_drop, Nat.add_sub_cancel_left,
    fromBytes'_drop_take_wordLE_land_div_mask _ _ _ (by omega) (by omega)]
  rfl

theorem signextend104_bitvec (x : BitVec 256) :
    (UInt256.signextend ⟨12⟩ ⟨x.toFin⟩).val =
      ((x.setWidth 104).signExtend 256).toFin := by
  unfold UInt256.signextend
  simp only [show (⟨12⟩ : UInt256).toNat ≤ 31 from by decide, if_true]
  change (if (⟨x.toFin &&& (⟨2^103, by decide⟩ : Fin (2^256))⟩ : UInt256) ≠ ⟨0⟩
    then (⟨x.toFin ||| (⟨2^256-2^103, by decide⟩ : Fin (2^256))⟩ : UInt256)
    else ⟨x.toFin &&& (⟨2^103-1, by decide⟩ : Fin (2^256))⟩).val = _
  simp only [ne_eq, UInt256.mk.injEq]
  change (if ¬x.toFin &&& (BitVec.ofNat 256 (2^103)).toFin = (0#256).toFin
    then (⟨x.toFin ||| (BitVec.ofNat 256 (2^256-2^103)).toFin⟩ : UInt256)
    else ⟨x.toFin &&& (BitVec.ofNat 256 (2^103-1)).toFin⟩).val = _
  simp only [← BitVec.toFin_and, BitVec.toFin_inj, ← BitVec.toFin_or]
  have h : (if x &&& BitVec.ofNat 256 (2^103) ≠ 0#256
      then x ||| BitVec.ofNat 256 (2^256-2^103)
      else x &&& BitVec.ofNat 256 (2^103-1)) = (x.setWidth 104).signExtend 256 := by
    bv_decide
  split <;> rename_i hc <;>
    simpa only [ne_eq, hc, if_true, if_false] using congrArg BitVec.toFin h

def signed104 (w : UInt256) : Int :=
  normalizeInt (.sint ⟨104, by decide⟩) (Int.ofNat (packedUint w 0 13).toNat)

theorem signed104_bitvec (w : UInt256) :
    signed104 w = (((⟨w.val⟩ : BitVec 256)).setWidth 104).toInt := by
  unfold signed104
  rw [normalizeSigned_bitvec _ (by decide)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofFin]
  have hm : (packedUint w 0 13).toNat = w.toNat % 2^104 := by
    change (UInt256.land (UInt256.div w ⟨1⟩) (UInt256.ofNat (2^104-1))).toNat = _
    rw [word_div_one, uland_toNat]
    rw [UInt256.toNat_ofNat_of_lt (by decide)]
    exact nat_land_mask_eq_mod w.toNat 104
  rw [hm, Nat.mod_mod]
  rfl

theorem signed104_word (w : UInt256) :
    EVM.wordOfInt (signed104 w) = UInt256.signextend ⟨12⟩ w := by
  rw [signed104_bitvec, ← BitVec.toInt_signExtend_of_le (v := 256) (by decide),
    bitvecWordOfInt]
  exact congrArg UInt256.mk (signextend104_bitvec (⟨w.val⟩ : BitVec 256)).symm

theorem sint104WordEncoding (w : UInt256) :
    encodeABIValue? (.elem (.int (.sint ⟨104, by decide⟩))) (.int (signed104 w)) =
      some (EVM.Word.toBytesBE (UInt256.signextend ⟨12⟩ w)) := by
  have hlo := BitVec.le_toInt (x := (⟨w.val⟩ : BitVec 256).setWidth 104)
  have hhi := BitVec.toInt_lt (x := (⟨w.val⟩ : BitVec 256).setWidth 104)
  have hb : -(Int.ofNat (EVM.twoPow 103)) ≤ signed104 w ∧
      signed104 w < Int.ofNat (EVM.twoPow 103) := by
    rw [signed104_bitvec]
    exact ⟨hlo, hhi⟩
  simp only [encodeABIValue?, encodeABIWord?, show (104 : Nat) ≠ 0 from by decide,
    if_false, hb, if_true, signed104_word]
  rfl

end Benchmarks.CompoundIII.Comet

import Reasoning.Storage
import Reasoning.Solc

/-!
# Storage locations of `int256` and packed fields

`Reasoning/Storage.lean` states the loads and stores of full-slot `uint256`/`bytes32`, packed
`uintN`, `bool` and `address` locations.  The Solidity proofs also need full-slot `int256`
(`int256Loc`, two's complement `s256OfWord`), packed `uintN`/`intN` stores at any byte offset
(`setPackedWordNat`) and packed signed loads (`sextAt`).  They are stated here in the same style,
on `Solm.storageLocLoad`/`storageLocStore`.
-/

open Solm Ethereum

namespace Reasoning.Theory

/-! ## Packed unsigned integer fields (any byte offset and size) -/

/-- The slot word after writing the low `size` bytes of `v` at byte `off` (little-endian slot bytes). -/
def setPackedWordNat (old off size v : ℕ) : ℕ :=
  old % 256 ^ off + 256 ^ off * (v % 256 ^ size + 256 ^ size * (old / 256 ^ (off + size)))

theorem storageLocStore_uint_packed (evm : EVM.State) (slot : UInt256) (offset : Fin 32) (size : Fin 33)
    (width : ABI.BitWidth) {hbound : offset.val + size.val - 1 < 32} (n : ℕ) (hn : n < 2 ^ 256) :
    storageLocStore evm { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.uint width) }
        (.int n) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
          offset.val size.val n))) := by
  unfold storageLocStore storageLocWriteWord
  simp only [Solm.valueToWord, wordOfInt_nonneg (n : Int) (Int.natCast_nonneg n), Int.toNat_natCast, bind,
    Option.bind, pure]
  congr 2
  apply u256_inj
  have hsbl := (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvbl := (EVM.Word.toBytesLEWithSizeProof (EVM.word n)).2
  have hoff : offset.val ≤ 32 := by have := offset.isLt; omega
  have hsz : size.val ≤ 32 := by have := size.isLt; omega
  have hos : offset.val + size.val ≤ 32 := by have := offset.isLt; have := size.isLt; omega
  have hres : fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take offset.val
        ++ (EVM.Word.toBytesLEWithSizeProof (EVM.word n)).1.take size.val
        ++ (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
          (offset.val + size.val)) =
      setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat offset.val size.val n := by
    rw [fromBytes'_append, fromBytes'_append, List.length_append, List.length_take, List.length_take, hsbl, hvbl,
      Nat.min_eq_left hoff, Nat.min_eq_left hsz, fromBytes'_take_wordLE, fromBytes'_take_wordLE,
      fromBytes'_drop_wordLE, show (EVM.word n).toNat = n from ulit_toNat' n hn]
    unfold setPackedWordNat
    rw [Nat.pow_mul, Nat.pow_mul, show (2 : ℕ) ^ 8 = 256 from rfl, Nat.pow_add]
    ring
  have hlen : ((EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take
        offset.val
        ++ (EVM.Word.toBytesLEWithSizeProof (EVM.word n)).1.take size.val
        ++ (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
          (offset.val + size.val)).length = 32 := by
    rw [List.length_append, List.length_append, List.length_take, List.length_take, List.length_drop, hsbl, hvbl,
      Nat.min_eq_left hoff, Nat.min_eq_left hsz]
    omega
  have hlt : setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat offset.val size.val n
      < UInt256.size := by
    rw [← hres]
    have := EVM.fromBytes'_le (bs := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take offset.val
        ++ (EVM.Word.toBytesLEWithSizeProof (EVM.word n)).1.take size.val
        ++ (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
          (offset.val + size.val))
    rw [hlen] at this
    exact this
  rw [ulit_toNat' _ hlt]
  exact hres

/-! ## Full-slot int256 storage -/

def int256Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide,
    type := .int (.sint ⟨256, by decide⟩) }

/-- The two's-complement reading of a word (`int256`). -/
def s256OfWord (w : UInt256) : Int :=
  if w.toNat < 2 ^ 255 then (w.toNat : Int) else (w.toNat : Int) - 2 ^ 256

/-- A full-slot location of any element type decodes the stored word. -/
theorem storageLocLoad_full_word (evm : EVM.State) (slot : UInt256) (t : ABI.ElemType)
    {hbound : (0 : Fin 32).val + (32 : Fin 33).val - 1 < 32} :
    storageLocLoad evm { slot := slot, offset := 0, size := 32, hbound := hbound, type := t } =
      Solm.wordToElem t (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad
  simp only [Fin.val_zero, Nat.zero_add]
  congr 1
  apply u256_inj
  show fromBytes' _ = _
  rw [htake, fromBytes'_toBytesLEWithSizeProof]

theorem storageLocLoad_int256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (int256Loc slot) =
      .int (s256OfWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  rw [int256Loc, storageLocLoad_full_word]
  simp only [Solm.wordToElem, normalizeInt_sint256_word, s256OfWord]
  rw [show EVM.twoPow 255 = 2 ^ 255 from rfl, show (Int.ofNat EVM.wordModulus) = (2 : Int) ^ 256 by rfl]
  split <;> rfl

theorem s256OfWord_bounds (w : UInt256) : -2 ^ 255 ≤ s256OfWord w ∧ s256OfWord w < 2 ^ 255 := by
  have hlt : w.toNat < 2 ^ 256 := w.val.isLt
  unfold s256OfWord
  split <;> omega

theorem storageLocStore_int256 (evm : EVM.State) (slot : UInt256) (i : Int) :
    storageLocStore evm (int256Loc slot) (.int i) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt i)) := by
  unfold storageLocStore storageLocWriteWord int256Loc
  simp only [Solm.valueToWord, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt i)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (EVM.wordOfInt i).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

/-- `wordOfInt` of an in-range signed value round-trips through `s256OfWord`. -/
theorem s256OfWord_wordOfInt (i : Int) (hlo : -2 ^ 255 ≤ i) (hhi : i < 2 ^ 255) :
    s256OfWord (EVM.wordOfInt i) = i := by
  unfold s256OfWord EVM.wordOfInt
  split
  · rename_i hneg
    have hr : i.natAbs % EVM.wordModulus = i.natAbs := Nat.mod_eq_of_lt (by
      show i.natAbs < 2 ^ 256; omega)
    rw [hr]
    have hne : i.natAbs ≠ 0 := by omega
    simp only [hne, if_false]
    rw [show EVM.wordModulus = 2 ^ 256 from rfl]
    have h1 : 2 ^ 256 - i.natAbs < UInt256.size := by
      show 2 ^ 256 - i.natAbs < 2 ^ 256; omega
    rw [show EVM.word (2 ^ 256 - i.natAbs) = UInt256.ofNat (2 ^ 256 - i.natAbs) from rfl, ulit_toNat' _ h1]
    rw [if_neg (by omega)]
    omega
  · rename_i hnn
    have h1 : i.toNat < UInt256.size := by show i.toNat < 2 ^ 256; omega
    rw [show EVM.word i.toNat = UInt256.ofNat i.toNat from rfl, ulit_toNat' _ h1, if_pos (by omega)]
    omega

/-! ## Packed fields of any element type, packed signed fields -/

/-- The field word of a packed location (`bitOffset = none`): the slot word shifted down and masked. -/
theorem storageLocLoad_offset_word (evm : EVM.State) (slot : UInt256) (offset : Fin 32) (size : Fin 33)
    (t : ABI.ElemType) {hbound : offset.val + size.val - 1 < 32} (hoff : 8 * offset.val < 256)
    (hsize : 8 * size.val ≤ 256) :
    storageLocLoad evm { slot := slot, offset := offset, size := size, hbound := hbound, type := t } =
      Solm.wordToElem t (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
        (UInt256.ofNat (256 ^ size.val - 1))) := by
  unfold storageLocLoad
  dsimp only
  congr 1
  apply u256_inj
  show fromBytes' _ = _
  rw [List.extract_eq_take_drop]
  simpa [Nat.add_sub_cancel_left] using
    fromBytes'_drop_take_wordLE_land_div_mask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val size.val hoff hsize

/-- Sign extension of `x` at `bits` bits (`int<bits>` reading of a field word). -/
def sextAt (bits x : ℕ) : Int :=
  if x % 2 ^ bits < 2 ^ (bits - 1) then ((x % 2 ^ bits : ℕ) : Int) else ((x % 2 ^ bits : ℕ) : Int) - 2 ^ bits

theorem sextAt_bounds (bits x : ℕ) (hb : 0 < bits) : -2 ^ (bits - 1) ≤ sextAt bits x ∧ sextAt bits x < 2 ^ (bits - 1) := by
  unfold sextAt
  have hlt : x % 2 ^ bits < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
  have hsplit : 2 ^ bits = 2 * 2 ^ (bits - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hk : ((2 : ℤ) ^ (bits - 1)) = ((2 ^ (bits - 1) : ℕ) : ℤ) := by push_cast; rfl
  have hk2 : ((2 : ℤ) ^ bits) = ((2 ^ bits : ℕ) : ℤ) := by push_cast; rfl
  rw [hk, hk2]
  split <;> omega

/-- `normalizeInt` at a signed width is sign extension. -/
theorem normalizeInt_sint_ofNat (bits : ABI.BitWidth) (x : ℕ) :
    normalizeInt (.sint bits) (Int.ofNat x) = sextAt bits.val x := by
  have hmod : ((x : Int) % ((2 ^ bits.val : ℕ) : Int)) = ((x % 2 ^ bits.val : ℕ) : Int) := by norm_cast
  simp only [normalizeInt, sextAt, EVM.twoPow, Int.ofNat_eq_natCast, hmod]
  by_cases h : x % 2 ^ bits.val < 2 ^ (bits.val - 1)
  · rw [if_pos (Int.ofNat_lt.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (Int.ofNat_lt.mp h')), if_neg h]
    norm_cast

/-- A packed `int<8·size>` field at byte `offset`. -/
theorem storageLocLoad_sint_offset (evm : EVM.State) (slot : UInt256) (offset : Fin 32) (size : Fin 33)
    (w : ABI.BitWidth) {hbound : offset.val + size.val - 1 < 32} (hoff : 8 * offset.val < 256)
    (hsize : 8 * size.val ≤ 256) :
    storageLocLoad evm { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.sint w) } =
      .int (sextAt w.val (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
        (UInt256.ofNat (256 ^ size.val - 1))).toNat) := by
  rw [storageLocLoad_offset_word evm slot offset size _ hoff hsize]
  simp only [Solm.wordToElem, normalizeInt_sint_ofNat]

/-- A packed store of any `.int` value: the two's-complement word's low `size` bytes. -/
theorem storageLocStore_int_packed (evm : EVM.State) (slot : UInt256) (offset : Fin 32) (size : Fin 33)
    (t : ABI.ElemType) {hbound : offset.val + size.val - 1 < 32} (i : Int) :
    storageLocStore evm { slot := slot, offset := offset, size := size, hbound := hbound, type := t } (.int i) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
          offset.val size.val (EVM.wordOfInt i).toNat))) := by
  unfold storageLocStore storageLocWriteWord
  simp only [Solm.valueToWord, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  have hsbl := (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvbl := (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt i)).2
  have hoff : offset.val ≤ 32 := by have := offset.isLt; omega
  have hsz : size.val ≤ 32 := by have := size.isLt; omega
  have hos : offset.val + size.val ≤ 32 := by have := offset.isLt; have := size.isLt; omega
  have hres : fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take offset.val
        ++ (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt i)).1.take size.val
        ++ (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
          (offset.val + size.val)) =
      setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat offset.val size.val
        (EVM.wordOfInt i).toNat := by
    rw [fromBytes'_append, fromBytes'_append, List.length_append, List.length_take, List.length_take, hsbl, hvbl,
      Nat.min_eq_left hoff, Nat.min_eq_left hsz, fromBytes'_take_wordLE, fromBytes'_take_wordLE,
      fromBytes'_drop_wordLE]
    unfold setPackedWordNat
    rw [Nat.pow_mul, Nat.pow_mul, show (2 : ℕ) ^ 8 = 256 from rfl, Nat.pow_add]
    ring
  have hlen : ((EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take
        offset.val
        ++ (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt i)).1.take size.val
        ++ (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
          (offset.val + size.val)).length = 32 := by
    rw [List.length_append, List.length_append, List.length_take, List.length_take, List.length_drop, hsbl, hvbl,
      Nat.min_eq_left hoff, Nat.min_eq_left hsz]
    omega
  have hlt : setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat offset.val size.val
      (EVM.wordOfInt i).toNat < UInt256.size := by
    rw [← hres]
    have := EVM.fromBytes'_le (bs := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take offset.val
        ++ (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt i)).1.take size.val
        ++ (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
          (offset.val + size.val))
    rw [hlen] at this
    exact this
  rw [ulit_toNat' _ hlt]
  exact hres

end Reasoning.Theory

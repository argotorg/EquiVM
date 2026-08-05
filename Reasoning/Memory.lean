import Reasoning.EVMWord
import Reasoning.Stepping
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Memory — reusable EVM memory / `ByteArray` lemmas

The EVM `MSTORE`/`MLOAD`/`RETURN`, `ffi.ByteArray.zeroes`, and the `UInt256.toByteArray` word
encoding are computable `ByteArray` operations, unlike genuinely opaque bytecode facts such as
`D_J`/keccak.  This module proves the generic, contract-agnostic memory lemmas: the big-endian
byte round-trip, `fromByteArrayBigEndian ∘ toByteArray = toNat`, the
`MSTORE`-then-`MLOAD`/`RETURN` round-trip, and the `toByteArray`/`toBytesBE` bridge.  ABI-level
encode/decode reasoning lives in `Reasoning.ABI` (which imports this module).
-/

open Ethereum Ethereum.EVM Solm ABI

set_option maxRecDepth 8000

namespace Reasoning.Theory

/-- `ffi.ByteArray.zeroes` yields zero bytes. -/
theorem byteArray_zeroes_toList (n : Nat) :
    (ffi.ByteArray.zeroes n).data.toList = List.replicate n 0 := by
  simp [ffi.ByteArray.zeroes]

/-- **Trusted (extern spec).** Keccak-256 returns a 32-byte digest.  This does not assert
    collision-resistance or injectivity; it only exposes the byte length guaranteed by the FFI
    implementation of `ffi.KEC`. -/
axiom keccak_size (b : ByteArray) : (ffi.KEC b).size = 32

/-! ## 0. Memory expansion cost shorthands -/

/-- Compute `MSTORE` memory expansion cost from the literal stack shape. -/
theorem mstoreCost_of_stack {s : State} {aw off val : UInt256} {t : List UInt256}
    {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: val :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw = mcost) :
    memoryExpansionCost s .MSTORE = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  rw [htop, haw]
  exact hcost

/-- Compute `MLOAD` memory expansion cost from the literal stack shape. -/
theorem mloadCost_of_stack {s : State} {aw off : UInt256} {t : List UInt256}
    {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw = mcost) :
    memoryExpansionCost s .MLOAD = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  rw [htop, haw]
  exact hcost

/-! ## 1. Little-endian byte arithmetic (`fromBytes'` / `toBytes'`) -/

theorem fromBytes'_replicate_zero (k : ℕ) : fromBytes' (List.replicate k (0 : UInt8)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate, fromBytes']; rw [ih]; rfl

/-- Appending high-order zero bytes does not change the little-endian value. -/
theorem fromBytes'_append_zeros (l : List UInt8) (k : ℕ) :
    fromBytes' (l ++ List.replicate k 0) = fromBytes' l := by
  induction l with
  | nil => simpa using fromBytes'_replicate_zero k
  | cons b bs ih => simp only [List.cons_append, fromBytes']; rw [ih]

/-- The little-endian round-trip `fromBytes' (toBytes' x) = x` (evmlean's version is `private`,
    so it is proved here). -/
theorem fromBytes'_toBytes' (x : ℕ) : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp [UInt8.size]
    exact Nat.mod_add_div _ _

/-- Nonnegative integers are embedded as their natural-value EVM word. -/
theorem wordOfInt_nonneg (i : Int) (h0 : 0 ≤ i) :
    EVM.wordOfInt i = EVM.word i.toNat := by
  rw [EVM.wordOfInt, if_neg (by omega)]

/-- A nonnegative integer built from a word's natural value round-trips to that word. -/
theorem wordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

/-- Little-endian word-byte round-trip for `EVM.Word.toBytesLEWithSizeProof`. -/
theorem fromBytes'_toBytesLEWithSizeProof (w : UInt256) :
    fromBytes' (EVM.Word.toBytesLEWithSizeProof w).1 = w.toNat := by
  show fromBytes' (toBytes' w.val ++ List.replicate (32 - (toBytes' w.val).length) 0) = w.toNat
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']
  rfl

/-! ## 1a. Digit views of little-endian word slices -/

theorem fromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fromBytes', Nat.ofDigits, ih]

theorem fromBytes'_take_wordLE (w : UInt256) (n : Nat) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take n) = w.toNat % 256 ^ n := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) n (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [fromBytes'_eq_ofDigits (bs.take n), List.map_take]
  rw [← htake, hfull]

theorem fromBytes'_drop_wordLE (w : UInt256) (n : Nat) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.drop n) = w.toNat / 256 ^ n := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have hdrop := Nat.ofDigits_div_pow_eq_ofDigits_drop (p := 256) n (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [fromBytes'_eq_ofDigits (bs.drop n), List.map_drop]
  rw [← hdrop, hfull]

theorem fromBytes'_take_wordLE_land_mask (w : UInt256) (n : Nat) (hbits : 8 * n ≤ 256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take n) =
      (UInt256.land w (UInt256.ofNat (2 ^ (8 * n) - 1))).toNat := by
  rw [fromBytes'_take_wordLE]
  show w.toNat % 256 ^ n =
    Nat.land w.toNat (UInt256.ofNat (2 ^ (8 * n) - 1)).toNat % UInt256.size
  have hmaskLt : 2 ^ (8 * n) - 1 < UInt256.size := by
    have hpow : (2 : Nat) ^ (8 * n) ≤ 2 ^ 256 :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) hbits
    have hpos : 0 < (2 : Nat) ^ (8 * n) := by positivity
    change 2 ^ (8 * n) - 1 < 2 ^ 256
    omega
  rw [ulit_toNat' _ hmaskLt]
  rw [show 256 ^ n = 2 ^ (8 * n) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
  rw [nat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ (8 * n) < UInt256.size := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ (8 * n))) (by
      simpa [UInt256.size] using
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) hbits)
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

/-! ## 2. `ByteArray.toList` = `data.toList`, and the `fromByteArrayBigEndian ∘ toByteArray` round-trip -/

/-- `ByteArray.toList` (the reversing `loop`) equals `data.toList`. -/
theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList := by
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
    rw [List.drop_eq_nil_of_le this, List.append_nil]

/-- Size of the internal accumulator used by `List.toByteArray`. -/
theorem list_toByteArray_loop_size (xs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop xs acc).size = acc.size + xs.length := by
  induction xs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons x xs ih =>
    rw [List.toByteArray.loop]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (acc.push x)

/-- Turning a byte list into a `ByteArray` preserves length. -/
theorem list_toByteArray_size (xs : List UInt8) : xs.toByteArray.size = xs.length := by
  simpa [List.toByteArray] using list_toByteArray_loop_size xs ByteArray.empty

/-- `List.toByteArray` preserves append structure. -/
theorem list_toByteArray_append (xs ys : List UInt8) :
    (xs ++ ys).toByteArray = xs.toByteArray ++ ys.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_append, Array.toList_append]
  simp

/-- **MLOAD round-trip.**  Big-endian-decoding the 32-byte encoding of `v` recovers `v.toNat`.
    The only opacity (the `ffi.zeroes` leading padding) cancels because it is zero. -/
theorem fromByteArrayBigEndian_toByteArray (v : UInt256) :
    fromByteArrayBigEndian (UInt256.toByteArray v) = v.toNat := by
  unfold fromByteArrayBigEndian UInt256.toByteArray BE
  rw [byteArray_toList_eq]
  simp only [fromBytesBigEndian, Function.comp, ByteArray.toList_data_append,
    byteArray_zeroes_toList, List.toList_data_toByteArray, List.reverse_append,
    List.reverse_replicate, toBytesBigEndian, List.reverse_reverse]
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']

/-! ## 3. `MSTORE` write / `MLOAD`-`RETURN` read -/

/-- A 32-byte word's `toByteArray` has size 32. -/
theorem toByteArray_size (v : UInt256) : (UInt256.toByteArray v).size = 32 :=
  (UInt256.toByteArrayWithSizeProof v).2

theorem toByteArray_extract_all (v : UInt256) :
    (UInt256.toByteArray v).extract 0 32 = UInt256.toByteArray v := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (Nat.le_of_eq (toByteArray_size v))

/-- Reading the appended tail back. -/
theorem extract_append_right (A B : ByteArray) :
    (A ++ B).extract A.size (A.size + B.size) = B := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append]
  show (A.data ++ B.data).extract A.data.size (A.data.size + B.data.size) = B.data
  rw [Array.extract_append_right]; simp

/-- Extracting the whole bytearray returns it unchanged. -/
theorem byteArray_extract_self (b : ByteArray) : b.extract 0 b.size = b := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
  exact le_rfl

/-- A `ByteArray` of size zero is empty. -/
theorem byteArray_eq_empty_of_size_eq_zero (b : ByteArray) (h : b.size = 0) :
    b = ByteArray.empty := by
  apply ByteArray.ext
  exact Array.eq_empty_of_size_eq_zero (by simpa using h)

/-- Writing zero bytes leaves the destination bytearray unchanged. -/
theorem byteArray_write_len_zero (src base : ByteArray) (srcOff dstOff : ℕ) :
    src.write srcOff base dstOff 0 = base := by
  unfold ByteArray.write
  simp

/-- `ffi.ByteArray.zeroes` of a `toNat`-zero size is the empty array. -/
theorem zeroes_zero {n : Nat} (hn : n = 0) : ffi.ByteArray.zeroes n = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [byteArray_zeroes_toList, hn]; rfl

theorem zero_toByteArray_eq_zeroes32 :
    UInt256.toByteArray (⟨0⟩ : UInt256) = ffi.ByteArray.zeroes 32 := by
  native_decide

/-- Reading zero bytes with padding returns the empty bytearray. -/
theorem byteArray_readWithPadding_zero (mem : ByteArray) (addr : ℕ) :
    mem.readWithPadding addr 0 = ByteArray.empty := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  by_cases h : addr ≥ mem.size
  · simp [h]
    exact zeroes_zero (n := 0) (by rfl)
  · simp [h]
    exact zeroes_zero (n := 0) (by rfl)

/-- A bounded padded read starting at or beyond the concrete byte-array end consists entirely of
zero bytes. -/
theorem readWithPadding_past_end (source : ByteArray) (addr len : ℕ)
    (haddr : source.size ≤ addr) (hlen : len < 2 ^ 64) :
    source.readWithPadding addr len = ffi.ByteArray.zeroes len := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬ len ≥ 2 ^ 64), if_pos haddr]
  change ByteArray.empty ++ ffi.ByteArray.zeroes len = ffi.ByteArray.zeroes len
  apply ByteArray.ext
  simp only [ByteArray.data_append]
  rw [show ByteArray.empty.data = (#[] : Array UInt8) from rfl, Array.empty_append]

theorem empty_readWithPadding_word_zero :
    uInt256OfByteArray (ByteArray.empty.readWithPadding 0 32) = (⟨0⟩ : UInt256) := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp [byteArray_zeroes_toList, uInt256OfByteArray]
  rfl

/-- **MSTORE write.**  Storing a 32-byte word `v` at offset `off ≥ mem.size` appends it past a
    zero gap: `mem ++ zeroes (off - mem.size) ++ v.toByteArray`.  (Generic, contract-agnostic.) -/
theorem toByteArray_write_eq (v : UInt256) (mem : ByteArray) (off : ℕ)
    (hoff : mem.size ≤ off) (_hb : off - mem.size < USize.size) :
    (UInt256.toByteArray v).write 0 mem off 32
      = mem ++ ffi.ByteArray.zeroes (off - mem.size) ++ UInt256.toByteArray v := by
  have hsz : (UInt256.toByteArray v).data.size = 32 := UInt256.toByteArrayWithSizeProof v |>.2
  have hpz : (ffi.ByteArray.zeroes (off - mem.size)).data.size = off - mem.size := by
    rw [show (ffi.ByteArray.zeroes (off - mem.size)).data.size
          = (ffi.ByteArray.zeroes (off - mem.size)).size from rfl,
        ByteArray_zeroes_size]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ ((32:ℕ) = 0)),
      if_neg (show ¬ (0 ≥ (UInt256.toByteArray v).size) from by
                rw [show (UInt256.toByteArray v).size = 32 from hsz]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hv : v.toByteArray.size = 32 := hsz
  have hDsz : (mem.data ++ (ffi.ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]; show mem.size + (off - mem.size) = off; omega
  rw [hv, show (min 32 (32 - 0) : ℕ) = 32 from rfl,
      show min mem.size (off + 32) - (off + 32) = 0 from by omega,
      show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
        rw [zeroes_zero (n := 0) (by rfl)]; rfl]
  rw [Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hDsz]),
      Array.extract_eq_self_of_le (show v.toByteArray.data.size ≤ 0 + (32 + 0) from by rw [hsz]),
      Array.extract_eq_empty_of_le (by rw [hDsz]; omega),
      Array.append_empty]

/-- An arbitrary nonempty write beginning beyond the concrete destination appends a zero gap and
the requested source prefix.  This is the variable-length counterpart of `toByteArray_write_eq`
and is especially useful for `MSTORE8`. -/
theorem write_eq_gap (src base : ByteArray) (off len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hoff : base.size ≤ off)
    (_hgap : off - base.size < USize.size) :
    src.write 0 base off len =
      base ++ ffi.ByteArray.zeroes (off - base.size) ++ src.extract 0 len := by
  have hpz : (ffi.ByteArray.zeroes (off - base.size)).data.size = off - base.size := by
    rw [show (ffi.ByteArray.zeroes (off - base.size)).data.size =
      (ffi.ByteArray.zeroes (off - base.size)).size from rfl, ByteArray_zeroes_size]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (0 ≥ src.size) from by omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
  have hDsz : (base.data ++ (ffi.ByteArray.zeroes (off - base.size)).data).size = off := by
    rw [Array.size_append, hpz]
    show base.size + (off - base.size) = off
    omega
  rw [show min len (src.size - 0) = len from by omega,
      show min base.size (off + len) - (off + len) = 0 from by omega,
      show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
        rw [zeroes_zero (n := 0) (by rfl)]; rfl,
      Array.append_empty]
  have hprefix :
      (base.data ++ (ffi.ByteArray.zeroes (off - base.size)).data).extract 0 off =
        base.data ++ (ffi.ByteArray.zeroes (off - base.size)).data :=
    Array.extract_eq_self_of_le (by rw [hDsz])
  have hcopy : min (len + 0) (src.data.size - 0) = len := by
    change min len (src.size - 0) = len
    omega
  have hsuffix :
      (base.data ++ (ffi.ByteArray.zeroes (off - base.size)).data).extract (off + len) =
        #[] := Array.extract_eq_empty_of_le (by rw [hDsz]; omega)
  rw [hprefix, hcopy, hsuffix]
  simp

/-- Extracting an in-bounds window from a zero block produces a zero block of the window length. -/
theorem zeroes_extract (total start stop : Nat) (hstart : start ≤ stop)
    (hstop : stop ≤ total) :
    (ffi.ByteArray.zeroes total).extract start stop =
      ffi.ByteArray.zeroes (stop - start) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract,
    byteArray_zeroes_toList, byteArray_zeroes_toList]
  simp only [List.extract_eq_take_drop]
  rw [List.drop_replicate, List.take_replicate]
  congr 1
  omega

/-- **Partial-overwrite write.**  Storing a 32-byte slice of `src` (its first word) at offset
    `destAddr ≤ base.size` splits `base` into `base[0..destAddr] ++ src[0..32] ++ base[destAddr+32..]`
    (the trailing piece is empty when the write reaches/extends the end).  Unlike `toByteArray_write_eq`
    this covers `destAddr < base.size`, the partial-overwrite case the post-call calldata buffer uses. -/
theorem write32_eq (src base : ByteArray) (destAddr : ℕ)
    (hsrc : 32 ≤ src.size) (hlo : destAddr ≤ base.size) :
    src.write 0 base destAddr 32
      = base.extract 0 destAddr ++ src.extract 0 32 ++ base.extract (destAddr + 32) base.size := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ (32:ℕ) = 0),
      if_neg (show ¬ (0 ≥ src.size) from by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min 32 (src.size - 0) = 32 := by omega
  have hsp : min base.size (destAddr + 32) - (destAddr + 32) = 0 :=
    Nat.sub_eq_zero_of_le (Nat.min_le_right _ _)
  have hdp : destAddr - base.size = 0 := Nat.sub_eq_zero_of_le hlo
  have hz0 : ffi.ByteArray.zeroes 0 = ByteArray.empty :=
    zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.zero_add, show base.data.size = base.size from rfl]

/-- A 32-byte word write grows memory far enough to cover its written word, whether it overwrites
    existing memory or extends by a zero gap. -/
theorem toByteArray_write_size_ge_off_add32 (b : UInt256) (mem : ByteArray) (off : ℕ)
    (hgap : off - mem.size < USize.size) :
    off + 32 ≤ ((UInt256.toByteArray b).write 0 mem off 32).size := by
  by_cases hle : off ≤ mem.size
  · rw [write32_eq _ _ off (by rw [toByteArray_size]) hle]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    rw [toByteArray_size]
    rw [Nat.min_eq_left hle]
    norm_num
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
      toByteArray_size]
    omega

/-- Size of an in-bounds or partially-overwriting 32-byte word write. -/
theorem toByteArray_write32_size_of_le
    (base : ByteArray) (word : UInt256) (off baseSize finalSize : Nat)
    (hbase : base.size = baseSize) (hoff : off ≤ base.size)
    (hfinal : max baseSize (off + 32) = finalSize) :
    ((UInt256.toByteArray word).write 0 base off 32).size = finalSize := by
  rw [write32_eq _ _ off (by rw [toByteArray_size]) hoff, ByteArray.size_append,
    ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hbase, toByteArray_size]
  rw [← hfinal]
  omega

/-- Size of a 32-byte word write at or after the end of memory, with a bounded zero gap. -/
theorem toByteArray_write32_size_of_ge
    (base : ByteArray) (word : UInt256) (off baseSize finalSize : Nat)
    (hbase : base.size = baseSize) (hoff : baseSize ≤ off)
    (hgap : off - baseSize < USize.size) (hfinal : off + 32 = finalSize) :
    ((UInt256.toByteArray word).write 0 base off 32).size = finalSize := by
  rw [toByteArray_write_eq word base off (by rw [hbase]; exact hoff) (by rwa [hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    hbase, toByteArray_size]
  omega

/-- Extracting a window `[i,j)` from a prefix `b[0..n]` (with `j ≤ n`) is the same as extracting it
    from `b` directly. -/
theorem extract_prefix (b : ByteArray) (n i j : ℕ) (hjn : j ≤ n) :
    (b.extract 0 n).extract i j = b.extract i j := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, Array.extract_extract, Nat.zero_add]
  congr 1
  omega

/-- Reading the head of an append when the window fits in the left component. -/
theorem extract_append_left (A B : ByteArray) (i j : ℕ) (h : j ≤ A.size) :
    (A ++ B).extract i j = A.extract i j := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_extract,
      Array.extract_append_of_stop_le_size_left (by rwa [← ByteArray.size_data] at h)]

/-- Extracting the first two 32-byte chunks of `A ++ B ++ C` returns `A ++ B`. -/
theorem byteArray_extract_two_chunks_0 (A B C : ByteArray) (hA : A.size = 32)
    (hB : B.size = 32) :
    (A ++ B ++ C).extract 0 64 = A ++ B := by
  rw [extract_append_left (A ++ B) C 0 64 (by rw [ByteArray.size_append, hA, hB])]
  rw [show 64 = (A ++ B).size by rw [ByteArray.size_append, hA, hB]]
  exact byteArray_extract_self _

/-- `empty ++ A = A`. -/
theorem empty_append (A : ByteArray) : ByteArray.empty ++ A = A := by
  apply ByteArray.ext
  rw [ByteArray.data_append]; show #[] ++ A.data = A.data; rw [Array.empty_append]

/-- A `< 2^32` natural is below `USize.size` on every supported platform. -/
theorem lt_usize (n : ℕ) (h : n < 2 ^ 32) : n < USize.size := by
  rcases System.Platform.numBits_eq with he | he <;> rw [USize.size, he] <;> omega

/-- The size of a `zeroes` block. -/
theorem zeroes_ofNat_size (n : ℕ) (_h : n < 2 ^ 32) :
    (ffi.ByteArray.zeroes n).size = n := by
  rw [ByteArray_zeroes_size]

-- `zeroes` used to be an `opaque` extern in evmlean, i.e. an unfolding WALL during defeq.  It is
-- now a plain def (`Array.replicate`), and letting defeq descend into it makes large state
-- comparisons stack-overflow (observed in UniswapV2Pair/Mint).  Re-erect the wall: reason about
-- `zeroes` only through the equations above (`ByteArray_zeroes_size`, `zeroes_zero`, …).
set_option allowUnsafeReducibility true in
attribute [irreducible] ffi.ByteArray.zeroes

theorem zeroes32_extract_zeroes (n : Nat) (hn : n ≤ 32) :
    (ffi.ByteArray.zeroes 32).extract 0 n =
      ffi.ByteArray.zeroes n := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [byteArray_zeroes_toList, byteArray_zeroes_toList]
  rw [List.extract_eq_take_drop, List.drop_zero, List.take_replicate,
    show min (n - 0) 32 = n by omega]

/-- `extract` at explicit (size-matched) bounds reads the right append component. -/
theorem extract_append_right' (A B : ByteArray) (i j : ℕ)
    (hi : i = A.size) (hj : j = A.size + B.size) : (A ++ B).extract i j = B := by
  subst hi; subst hj; exact extract_append_right A B

/-- `readWithoutPadding` of a window that fits is exactly the slice. -/
theorem readWithoutPadding_eq_extract (source : ByteArray) (addr : ℕ)
    (h : addr + 32 ≤ source.size) :
    source.readWithoutPadding addr 32 = source.extract addr (addr + 32) := by
  unfold ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬ (addr ≥ source.size))]
  simp only [show min 32 source.size = 32 from by omega]

/-- **`MLOAD`/`RETURN` read of a 32-byte aligned window.**  When `[addr, addr+32)` lies inside
    `source`, `readWithPadding addr 32` is exactly that slice (no trailing pad). -/
theorem readWithPadding_eq_extract (source : ByteArray) (addr : ℕ)
    (h : addr + 32 ≤ source.size) :
    source.readWithPadding addr 32 = source.extract addr (addr + 32) := by
  have hsz : (source.extract addr (addr + 32)).size = 32 := by
    rw [ByteArray.size_extract]; omega
  unfold ByteArray.readWithPadding
  rw [if_neg (by norm_num : ¬ ((32:ℕ) ≥ 2 ^ 64)), readWithoutPadding_eq_extract source addr h]
  simp only []
  rw [hsz]
  rw [zeroes_zero (n := 32 - 32) (by rfl)]
  apply ByteArray.ext; rw [ByteArray.data_append]; show _ ++ #[] = _; rw [Array.append_empty]

/-- `readWithoutPadding` of an in-bounds window of arbitrary length is exactly the slice. -/
theorem readWithoutPadding_eq_extract' (source : ByteArray) (addr len : ℕ)
    (hpos : 0 < len) (h : addr + len ≤ source.size) :
    source.readWithoutPadding addr len = source.extract addr (addr + len) := by
  unfold ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬ (addr ≥ source.size))]
  simp only [show min len source.size = len from by omega]

/-- **In-bounds read of an arbitrary-length window.**  When `[addr, addr+len)` lies inside
    `source` (and `len < 2⁶⁴`), `readWithPadding addr len` is exactly that slice (no trailing pad). -/
theorem readWithPadding_eq_extract' (source : ByteArray) (addr len : ℕ)
    (hpos : 0 < len) (hlen : len < 2 ^ 64) (h : addr + len ≤ source.size) :
    source.readWithPadding addr len = source.extract addr (addr + len) := by
  have hsz : (source.extract addr (addr + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega : ¬ ((len:ℕ) ≥ 2 ^ 64)), readWithoutPadding_eq_extract' source addr len hpos h]
  simp only []
  rw [hsz]
  rw [zeroes_zero (n := len - len) (by omega)]
  apply ByteArray.ext; rw [ByteArray.data_append]; show _ ++ #[] = _; rw [Array.append_empty]

/-- Split an in-bounds padded read into adjacent pieces. -/
theorem byteArray_readWithPadding_split (source : ByteArray) (addr len₁ len₂ : Nat)
    (hpos₁ : 0 < len₁) (hpos₂ : 0 < len₂)
    (hlen₁ : len₁ < 2 ^ 64) (hlen₂ : len₂ < 2 ^ 64)
    (hsum : len₁ + len₂ < 2 ^ 64)
    (hin : addr + len₁ + len₂ ≤ source.size) :
    source.readWithPadding addr (len₁ + len₂) =
      source.readWithPadding addr len₁ ++ source.readWithPadding (addr + len₁) len₂ := by
  rw [readWithPadding_eq_extract' source addr (len₁ + len₂) (by omega) hsum (by omega)]
  rw [readWithPadding_eq_extract' source addr len₁ hpos₁ hlen₁ (by omega)]
  rw [readWithPadding_eq_extract' source (addr + len₁) len₂ hpos₂ hlen₂ (by omega)]
  symm
  rw [ByteArray.extract_append_extract]
  congr <;> omega

/-- **Non-overlap read below a write.**  A 32-byte read at `readAddr` strictly below the write
    region `[destAddr, destAddr+32)` is unaffected by the write. -/
theorem write32_read_below (src base : ByteArray) (destAddr readAddr : ℕ)
    (hsrc : 32 ≤ src.size) (hlo : destAddr ≤ base.size) (hbelow : readAddr + 32 ≤ destAddr) :
    (src.write 0 base destAddr 32).readWithPadding readAddr 32 = base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by rw [ByteArray.size_extract]; omega
  have hsz32 : (src.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  rw [write32_eq src base destAddr hsrc hlo,
      readWithPadding_eq_extract _ readAddr
        (by rw [ByteArray.size_append, ByteArray.size_append, hbsz, hsz32]; omega),
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hbsz, hsz32]; omega),
      extract_append_left _ _ _ _ (by rw [hbsz]; omega),
      extract_prefix _ _ _ _ (by omega),
      ← readWithPadding_eq_extract _ readAddr (by omega)]

/-- **`write` of an arbitrary length, in bounds.**  When the destination window `[destAddr,
    destAddr+len)` lies inside `base` (and `0 < len ≤ src.size`), `write` splices `src`'s first
    `len` bytes into `base`. -/
theorem write_eq_gen (src base : ByteArray) (destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hin : destAddr + len ≤ base.size) :
    src.write 0 base destAddr len
      = base.extract 0 destAddr ++ src.extract 0 len ++ base.extract (destAddr + len) base.size := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (0 ≥ src.size) from by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min len (src.size - 0) = len := by omega
  have hsp : min base.size (destAddr + len) - (destAddr + len) = 0 :=
    Nat.sub_eq_zero_of_le (Nat.min_le_right _ _)
  have hdp : destAddr - base.size = 0 := Nat.sub_eq_zero_of_le (by omega)
  have hz0 : ffi.ByteArray.zeroes 0 = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.add_zero, Nat.zero_add, show base.data.size = base.size from rfl]

/-- **`write` of an arbitrary length, extending memory.**  When the destination starts inside
    `base` but reaches past its end, `write` keeps the prefix and appends the source prefix. -/
theorem write_eq_gen_extend (src base : ByteArray) (destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hext : base.size < destAddr + len) :
    src.write 0 base destAddr len =
      base.extract 0 destAddr ++ src.extract 0 len := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (0 ≥ src.size) from by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min len (src.size - 0) = len := by omega
  have hsp : min base.size (destAddr + len) - (destAddr + len) = 0 := by
    rw [Nat.min_eq_left (by omega)]
    omega
  have hdp : destAddr - base.size = 0 := Nat.sub_eq_zero_of_le hdest
  have hz0 : ffi.ByteArray.zeroes 0 = ByteArray.empty :=
    zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract, show (ByteArray.empty).data = (#[] : Array UInt8) from rfl,
    Array.append_empty, hsize, hpL, hsp, Nat.add_zero, Nat.zero_add,
    show base.data.size = base.size from rfl]
  have htail : base.data.extract (destAddr + len) base.size = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  rw [htail, Array.append_empty]

/-- **`write` of an arbitrary source window, in bounds.**  This is `write_eq_gen` with a nonzero
    source offset. -/
theorem write_eq_gen_from (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hin : destAddr + len ≤ base.size) :
    src.write srcAddr base destAddr len
      = base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + len)
          ++ base.extract (destAddr + len) base.size := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (srcAddr ≥ src.size) from by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min len (src.size - srcAddr) = len := by omega
  have hsp : min base.size (destAddr + len) - (destAddr + len) = 0 :=
    Nat.sub_eq_zero_of_le (Nat.min_le_right _ _)
  have hdp : destAddr - base.size = 0 := Nat.sub_eq_zero_of_le (by omega)
  have hz0 : ffi.ByteArray.zeroes 0 = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.add_zero, show base.data.size = base.size from rfl]

/-- An in-bounds arbitrary-offset write preserves the concrete destination size. -/
theorem write_size_of_inBounds_from (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hin : destAddr + len ≤ base.size) :
    (src.write srcAddr base destAddr len).size = base.size := by
  rw [write_eq_gen_from src base srcAddr destAddr len hlen hsrc hin,
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  omega

/-- **`write` of an arbitrary source window, extending memory.**  This is the arbitrary-source
offset counterpart of `write_eq_gen_extend`: the destination begins in `base`, but the copied
window reaches beyond its concrete end. -/
theorem write_eq_gen_extend_from (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hext : base.size < destAddr + len) :
    src.write srcAddr base destAddr len =
      base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (srcAddr ≥ src.size) from by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min len (src.size - srcAddr) = len := by omega
  have hsp : min base.size (destAddr + len) - (destAddr + len) = 0 := by
    rw [Nat.min_eq_left (by omega)]
    omega
  have hdp : destAddr - base.size = 0 := Nat.sub_eq_zero_of_le hdest
  have hz0 : ffi.ByteArray.zeroes 0 = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract, show (ByteArray.empty).data = (#[] : Array UInt8) from rfl,
    Array.append_empty, hsize, hpL, hsp, Nat.add_zero,
    show base.data.size = base.size from rfl]
  have htail : base.data.extract (destAddr + len) base.size = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  rw [htail, Array.append_empty]

/-- Reading exactly the destination window of an arbitrary-offset `ByteArray.write` recovers the
source window.  The destination may be overwritten in bounds or extended at its end; the only
required geometric condition is that the write starts within the existing destination. -/
theorem write_read_back_from_gen (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base destAddr len).readWithPadding destAddr len =
      src.extract srcAddr (srcAddr + len) := by
  have hpre : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hslice : (src.extract srcAddr (srcAddr + len)).size = len := by
    rw [ByteArray.size_extract]
    omega
  by_cases hin : destAddr + len ≤ base.size
  · rw [write_eq_gen_from src base srcAddr destAddr len hlen hsrc hin]
    rw [readWithPadding_eq_extract' _ destAddr len (Nat.pos_of_ne_zero hlen) hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hpre, hslice]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hpre, hslice])]
    exact extract_append_right' _ _ _ _ hpre.symm (by rw [hpre, hslice])
  · have hext : base.size < destAddr + len := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend_from src base srcAddr destAddr len hlen hsrc hdest hext]
    rw [readWithPadding_eq_extract' _ destAddr len (Nat.pos_of_ne_zero hlen) hlen64 (by
      rw [ByteArray.size_append, hpre, hslice])]
    exact extract_append_right' _ _ _ _ hpre.symm (by rw [hpre, hslice])

/-- A copy whose source starts at or beyond the source end and whose destination starts at or
beyond the destination end is a byte-array no-op.  The EVM still expands its logical active-memory
high-water mark and charges for the requested range; this lemma only records the concrete
`ByteArray.write` payload behavior. -/
theorem write_from_source_end_past_dest (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hsrc : src.size ≤ srcAddr) (hdest : base.size ≤ destAddr) :
    src.write srcAddr base destAddr len = base := by
  unfold ByteArray.write
  by_cases hlen : len = 0
  · rw [if_pos hlen]
  · rw [if_neg hlen, if_pos hsrc]
    have hcopyLen : min len (base.size - destAddr) = 0 := by omega
    have hdestAddr : min destAddr base.size = base.size := Nat.min_eq_right hdest
    rw [hcopyLen, hdestAddr]
    apply ByteArray.ext
    simp only [ByteArray.data_copySlice]
    rw [zeroes_zero (n := 0) (by rfl)]
    simp [show base.data.size = base.size from rfl]

/-- Data shape of a write to destination offset `0` that may extend the destination. -/
theorem write0_data (src base : ByteArray) (len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) :
    (src.write 0 base 0 len).data = src.data.extract 0 len ++ base.data.extract len base.data.size := by
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (0 ≥ src.size) from by omega)]
  simp only [show min len (src.size - 0) = len from by omega,
    show min base.size (0 + len) - (0 + len) = 0 from by omega,
    show 0 - base.size = 0 from by omega]
  have hz : (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) := by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl
  simp only [ByteArray.data_copySlice, ByteArray.data_append, hz, Array.append_empty, Nat.zero_add]
  rw [show min (len + 0) (src.data.size - 0) = len from by
    have : src.data.size = src.size := rfl
    omega]
  simp only [Nat.add_zero]
  rw [Array.extract_eq_empty_of_le (by omega), Array.empty_append]

/-- Data shape of a write from an arbitrary source offset to destination offset `0`,
    possibly extending the destination. -/
theorem write0_data_from (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    (src.write srcAddr base 0 len).data =
      src.data.extract srcAddr (srcAddr + len) ++ base.data.extract len base.data.size := by
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (srcAddr ≥ src.size) from by omega)]
  simp only [show min len (src.size - srcAddr) = len from by omega,
    show min base.size (0 + len) - (0 + len) = 0 from by omega,
    show 0 - base.size = 0 from by omega]
  have hz : (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) := by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl
  simp only [ByteArray.data_copySlice, ByteArray.data_append, hz, Array.append_empty, Nat.zero_add]
  rw [show min (len + 0) (src.data.size - srcAddr) = len from by
    have : src.data.size = src.size := rfl
    omega]
  simp only [Nat.add_zero]
  rw [Array.extract_eq_empty_of_le (by omega), Array.empty_append]

/-- Read back a write at destination offset `0`, even when the write extends the destination. -/
theorem write0_read_back_gen (src base : ByteArray) (len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base 0 len).readWithPadding 0 len = src.extract 0 len := by
  apply ByteArray.ext
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬ len ≥ 2 ^ 64)]
  have hdata := write0_data src base len hlen hsrc
  have hsize : (src.write 0 base 0 len).size ≥ len := by
    show (src.write 0 base 0 len).data.size ≥ len
    rw [hdata, Array.size_append]
    have : (src.data.extract 0 len).size = len := by
      rw [Array.size_extract]
      have : src.data.size = src.size := rfl
      omega
    omega
  rw [if_neg (by omega : ¬ 0 ≥ (src.write 0 base 0 len).size)]
  simp only [show min len (src.write 0 base 0 len).size = len from by omega, Nat.zero_add]
  have hextract_size : ((src.write 0 base 0 len).extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  rw [ByteArray.data_append]
  rw [show (ffi.ByteArray.zeroes (len - ((src.write 0 base 0 len).extract 0 len).size)).data
      = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := len - ((src.write 0 base 0 len).extract 0 len).size)
      (by rw [hextract_size]; omega)]
    rfl]
  simp only [ByteArray.data_extract, Array.append_empty]
  rw [hdata]
  rw [Array.extract_append_of_stop_le_size_left]
  · rw [Array.extract_extract]
    simp
  · rw [Array.size_extract]
    have : src.data.size = src.size := rfl
    omega

/-- Read back a destination-0 write from an arbitrary source offset, even when the write extends
    the destination. -/
theorem write0_read_back_from_gen (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base 0 len).readWithPadding 0 len = src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬ len ≥ 2 ^ 64)]
  have hdata := write0_data_from src base srcAddr len hlen hsrc
  have hsize : (src.write srcAddr base 0 len).size ≥ len := by
    show (src.write srcAddr base 0 len).data.size ≥ len
    rw [hdata, Array.size_append]
    have : (src.data.extract srcAddr (srcAddr + len)).size = len := by
      rw [Array.size_extract]
      have : src.data.size = src.size := rfl
      omega
    omega
  rw [if_neg (by omega : ¬ 0 ≥ (src.write srcAddr base 0 len).size)]
  simp only [show min len (src.write srcAddr base 0 len).size = len from by omega, Nat.zero_add]
  have hextract_size : ((src.write srcAddr base 0 len).extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  rw [ByteArray.data_append]
  rw [show (ffi.ByteArray.zeroes (len - ((src.write srcAddr base 0 len).extract 0 len).size)).data
      = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := len - ((src.write srcAddr base 0 len).extract 0 len).size)
      (by rw [hextract_size]; omega)]
    rfl]
  simp only [ByteArray.data_extract, Array.append_empty]
  rw [hdata]
  rw [Array.extract_append_of_stop_le_size_left]
  · rw [Array.extract_extract]
    simp
  · rw [Array.size_extract]
    have : src.data.size = src.size := rfl
    omega

/-- **Read below an arbitrary-length write.**  A 32-byte read strictly below an in-bounds write of
    any length is unaffected. -/
theorem write_read_below_gen (src base : ByteArray) (destAddr len readAddr : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hin : destAddr + len ≤ base.size)
    (hbelow : readAddr + 32 ≤ destAddr) :
    (src.write 0 base destAddr len).readWithPadding readAddr 32 = base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by rw [ByteArray.size_extract]; omega
  have hszl : (src.extract 0 len).size = len := by rw [ByteArray.size_extract]; omega
  rw [write_eq_gen src base destAddr len hlen hsrc hin,
      readWithPadding_eq_extract _ readAddr
        (by rw [ByteArray.size_append, ByteArray.size_append, hbsz, hszl]; omega),
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hbsz, hszl]; omega),
      extract_append_left _ _ _ _ (by rw [hbsz]; omega),
      extract_prefix _ _ _ _ (by omega),
      ← readWithPadding_eq_extract _ readAddr (by omega)]

/-- **Read below an arbitrary-length write, allowing extension.**  A 32-byte read strictly below
    `[destAddr, destAddr+len)` is unaffected even when the write extends past `base.size`. -/
theorem write_read_below_gen_extend (src base : ByteArray) (destAddr len readAddr : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hbelow : readAddr + 32 ≤ destAddr) :
    (src.write 0 base destAddr len).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  by_cases hin : destAddr + len ≤ base.size
  · exact write_read_below_gen src base destAddr len readAddr hlen hsrc hin hbelow
  · have hext : base.size < destAddr + len := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend src base destAddr len hlen hsrc hdest hext]
    have hbasePrefix : (base.extract 0 destAddr).size = destAddr := by
      rw [ByteArray.size_extract]
      omega
    have hsrcPrefix : (src.extract 0 len).size = len := by
      rw [ByteArray.size_extract]
      omega
    rw [readWithPadding_eq_extract _ readAddr (by
      rw [ByteArray.size_append, hbasePrefix, hsrcPrefix]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [hbasePrefix]; omega)]
    rw [extract_prefix _ destAddr readAddr (readAddr + 32) hbelow]
    rw [← readWithPadding_eq_extract base readAddr (by omega)]

/-- An arbitrary bounded read below an arbitrary-offset write is unaffected, whether that write
stays within the concrete destination or extends it. -/
theorem write_read_below_gen_from_extend (src base : ByteArray)
    (srcAddr destAddr written readAddr len : ℕ)
    (hwritten : written ≠ 0) (hsrc : srcAddr + written ≤ src.size)
    (hdest : destAddr ≤ base.size) (hbelow : readAddr + len ≤ destAddr)
    (hreadIn : readAddr + len ≤ base.size) (hpos : 0 < len)
    (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base destAddr written).readWithPadding readAddr len =
      base.readWithPadding readAddr len := by
  have hpre : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hslice : (src.extract srcAddr (srcAddr + written)).size = written := by
    rw [ByteArray.size_extract]
    omega
  by_cases hin : destAddr + written ≤ base.size
  · rw [write_eq_gen_from src base srcAddr destAddr written hwritten hsrc hin]
    rw [readWithPadding_eq_extract' _ readAddr len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hpre, hslice]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hpre, hslice]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [hpre]; exact hbelow)]
    rw [extract_prefix _ destAddr readAddr (readAddr + len) hbelow]
    exact (readWithPadding_eq_extract' base readAddr len hpos hlen64 hreadIn).symm
  · have hext : base.size < destAddr + written := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend_from src base srcAddr destAddr written hwritten hsrc hdest hext]
    rw [readWithPadding_eq_extract' _ readAddr len hpos hlen64 (by
      rw [ByteArray.size_append, hpre, hslice]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [hpre]; exact hbelow)]
    rw [extract_prefix _ destAddr readAddr (readAddr + len) hbelow]
    exact (readWithPadding_eq_extract' base readAddr len hpos hlen64 hreadIn).symm

/-- **Readback of a write.**  Reading the 32-byte window just written returns the source's first
    word. -/
theorem write32_read_back (src base : ByteArray) (destAddr : ℕ)
    (hsrc : 32 ≤ src.size) (hlo : destAddr ≤ base.size) :
    (src.write 0 base destAddr 32).readWithPadding destAddr 32 = src.extract 0 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by rw [ByteArray.size_extract]; omega
  have hsz32 : (src.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  rw [write32_eq src base destAddr hsrc hlo,
      readWithPadding_eq_extract _ destAddr
        (by rw [ByteArray.size_append, ByteArray.size_append, hbsz, hsz32]; omega),
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hbsz, hsz32]),
      extract_append_right' _ _ _ _ hbsz.symm (by rw [hbsz, hsz32])]

/-- Reading back a just-written `UInt256.toByteArray` word returns the whole word. -/
theorem toByteArray_write32_read_back
    (base : ByteArray) (word : UInt256) (off : Nat) (hoff : off ≤ base.size) :
    ((UInt256.toByteArray word).write 0 base off 32).readWithPadding off 32 =
      UInt256.toByteArray word := by
  rw [write32_read_back _ _ off (by rw [toByteArray_size]) hoff]
  rw [toByteArray_extract_all]

/-- `extract` of the right component of an append, for a window past the left component. -/
theorem extract_append_right_window (A B : ByteArray) (i j : ℕ) (h : A.size ≤ i) :
    (A ++ B).extract i j = B.extract (i - A.size) (j - A.size) := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append,
    Array.extract_append_of_size_left_le_start h, show A.data.size = A.size from rfl]

/-- **Boundary-spanning extract of an append.**  A window `[i, j)` with `i ≤ |A| ≤ j` reads the
    tail of `A` followed by the head of `B`. -/
theorem extract_append_span (A B : ByteArray) (i j : ℕ) (hi : i ≤ A.size) (hj : A.size ≤ j) :
    (A ++ B).extract i j = A.extract i A.size ++ B.extract 0 (j - A.size) := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append]
  rw [Array.extract_append]
  congr 1
  · exact Array.extract_eq_of_size_le_stop hj
  · rw [show A.data.size = A.size from rfl]; congr 1; omega

/-- `extract` composition for `ByteArray` (lifts `Array.extract_extract`). -/
theorem extract_extract_BA (b : ByteArray) (s e s' e' : ℕ) :
    (b.extract s e).extract s' e' = b.extract (s + s') (min (s + e') e) := by
  apply ByteArray.ext; simp only [ByteArray.data_extract, Array.extract_extract]

/-- A bounded read above an arbitrary-offset, arbitrary-length in-bounds write is unaffected. -/
theorem write_read_above_gen_from (src base : ByteArray)
    (srcAddr destAddr written readAddr len : ℕ)
    (hwritten : written ≠ 0) (hsrc : srcAddr + written ≤ src.size)
    (hwriteIn : destAddr + written ≤ base.size)
    (habove : destAddr + written ≤ readAddr) (hreadIn : readAddr + len ≤ base.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base destAddr written).readWithPadding readAddr len =
      base.readWithPadding readAddr len := by
  have hpre : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hslice : (src.extract srcAddr (srcAddr + written)).size = written := by
    rw [ByteArray.size_extract]
    omega
  have hprefSize :
      (base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + written)).size =
        destAddr + written := by
    rw [ByteArray.size_append, hpre, hslice]
  have hsuffix :
      (base.extract (destAddr + written) base.size).size =
        base.size - (destAddr + written) := by
    rw [ByteArray.size_extract]
    omega
  rw [write_eq_gen_from src base srcAddr destAddr written hwritten hsrc hwriteIn]
  rw [readWithPadding_eq_extract' _ readAddr len hpos hlen64 (by
    rw [ByteArray.size_append, hprefSize, hsuffix]
    omega)]
  rw [readWithPadding_eq_extract' base readAddr len hpos hlen64 hreadIn]
  rw [extract_append_right_window _ _ _ _ (by rw [hprefSize]; exact habove), hprefSize]
  rw [extract_extract_BA]
  rw [show destAddr + written + (readAddr - (destAddr + written)) = readAddr by omega]
  rw [show min (destAddr + written + (readAddr + len - (destAddr + written))) base.size =
      readAddr + len by omega]

/-- **Non-overlap read above a write.**  A 32-byte read at `readAddr ≥ destAddr+32` (within bounds)
    is unaffected by a write at `destAddr`. -/
theorem write32_read_above (src base : ByteArray) (destAddr readAddr : ℕ)
    (hsrc : 32 ≤ src.size) (hlo : destAddr ≤ base.size)
    (habove : destAddr + 32 ≤ readAddr) (hin : readAddr + 32 ≤ base.size) :
    (src.write 0 base destAddr 32).readWithPadding readAddr 32 = base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by rw [ByteArray.size_extract]; omega
  have hsz32 : (src.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have hcsz : (base.extract (destAddr + 32) base.size).size = base.size - (destAddr + 32) := by
    rw [ByteArray.size_extract]; omega
  have habsz : (base.extract 0 destAddr ++ src.extract 0 32).size = destAddr + 32 := by
    rw [ByteArray.size_append, hbsz, hsz32]
  rw [write32_eq src base destAddr hsrc hlo,
      readWithPadding_eq_extract _ readAddr
        (by rw [ByteArray.size_append, habsz, hcsz]; omega),
      readWithPadding_eq_extract _ readAddr (by omega),
      extract_append_right_window _ _ _ _ (by rw [habsz]; omega), habsz,
      extract_extract_BA,
      show destAddr + 32 + (readAddr - (destAddr + 32)) = readAddr from by omega,
      show min (destAddr + 32 + (readAddr + 32 - (destAddr + 32))) base.size = readAddr + 32 from by
        omega]

/-- A padded 32-byte read above an in-bounds word write is unaffected, even when the read
    reaches or lies beyond the concrete end of memory.  This is the form needed when an EVM
    allocation turns formerly implicit zero padding into concrete zero bytes. -/
theorem write32_read_above_padded (src base : ByteArray) (destAddr readAddr : ℕ)
    (hsrc : 32 ≤ src.size) (hlo : destAddr + 32 ≤ base.size)
    (habove : destAddr + 32 ≤ readAddr) :
    (src.write 0 base destAddr 32).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  have hsize : (src.write 0 base destAddr 32).size = base.size := by
    rw [write32_eq src base destAddr hsrc (by omega), ByteArray.size_append,
      ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  by_cases hpast : base.size ≤ readAddr
  · rw [readWithPadding_past_end base readAddr 32 hpast (by decide)]
    rw [readWithPadding_past_end (src.write 0 base destAddr 32) readAddr 32
      (by rw [hsize]; exact hpast) (by decide)]
  · have hread : readAddr < base.size := by omega
    by_cases hin : readAddr + 32 ≤ base.size
    · exact write32_read_above src base destAddr readAddr hsrc (by omega) habove hin
    have hspan : base.size ≤ readAddr + 32 := by omega
    have hreadBase : ¬ readAddr ≥ base.size := by omega
    unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
    simp only [if_neg (by norm_num : ¬ ((32 : Nat) ≥ 2 ^ 64)),
      if_neg hreadBase, hsize]
    have hmin : min 32 base.size = 32 := by omega
    rw [hmin]
    have hextract :
        (src.write 0 base destAddr 32).extract readAddr (readAddr + 32) =
          base.extract readAddr (readAddr + 32) := by
      rw [write32_eq src base destAddr hsrc (by omega)]
      have hpre : (base.extract 0 destAddr ++ src.extract 0 32).size =
          destAddr + 32 := by
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega
      rw [extract_append_right_window _ _ _ _ (by rw [hpre]; exact habove), hpre]
      rw [extract_extract_BA]
      rw [show destAddr + 32 + (readAddr - (destAddr + 32)) = readAddr by omega]
      rw [show min (destAddr + 32 + (readAddr + 32 - (destAddr + 32))) base.size =
          base.size by omega]
      apply ByteArray.ext
      simp only [ByteArray.data_extract]
      exact (Array.extract_eq_of_size_le_stop (by simpa using hspan)).symm
    rw [hextract]

/-- Read back a prefix of a 32-byte write. -/
theorem write32_read_prefix_len (src base : ByteArray) (dest len : Nat)
    (hsrc : 32 ≤ src.size) (hlo : dest ≤ base.size) (hlen : len ≤ 32)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base dest 32).readWithPadding dest len = src.extract 0 len := by
  have hbsz : (base.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hsz32 : (src.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  rw [write32_eq src base dest hsrc hlo]
  rw [readWithPadding_eq_extract' _ dest len hpos hlen64 (by
    rw [ByteArray.size_append, ByteArray.size_append, hbsz, hsz32]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hbsz, hsz32]; omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [hbsz])]
  rw [hbsz]
  rw [show dest - dest = 0 by omega, show dest + len - dest = len by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + len) 32 = len by omega]

/-- A variable-length read below a 32-byte write is unaffected. -/
theorem write32_read_below_len (src base : ByteArray) (dest read len : Nat)
    (hsrc : 32 ≤ src.size) (hlo : dest ≤ base.size)
    (hbelow : read + len ≤ dest) (hin : read + len ≤ base.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base dest 32).readWithPadding read len = base.readWithPadding read len := by
  have hbsz : (base.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hsz32 : (src.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  rw [write32_eq src base dest hsrc hlo]
  rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
    rw [ByteArray.size_append, ByteArray.size_append, hbsz, hsz32]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hbsz, hsz32]; omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbsz]; omega)]
  rw [extract_prefix _ _ _ _ (by omega)]
  rw [← readWithPadding_eq_extract' base read len hpos hlen64 hin]

/-- A variable-length read above a 32-byte write is unaffected. -/
theorem write32_read_above_len (src base : ByteArray) (dest read len : Nat)
    (hsrc : 32 ≤ src.size) (hlo : dest ≤ base.size)
    (habove : dest + 32 ≤ read) (hin : read + len ≤ base.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base dest 32).readWithPadding read len = base.readWithPadding read len := by
  have hbsz : (base.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hsz32 : (src.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have hcsz : (base.extract (dest + 32) base.size).size = base.size - (dest + 32) := by
    rw [ByteArray.size_extract]; omega
  have habsz : (base.extract 0 dest ++ src.extract 0 32).size = dest + 32 := by
    rw [ByteArray.size_append, hbsz, hsz32]
  rw [write32_eq src base dest hsrc hlo]
  rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
    rw [ByteArray.size_append, habsz, hcsz]
    omega)]
  rw [readWithPadding_eq_extract' base read len hpos hlen64 hin]
  rw [extract_append_right_window _ _ _ _ (by rw [habsz]; omega), habsz]
  rw [extract_extract_BA]
  rw [show dest + 32 + (read - (dest + 32)) = read by omega]
  rw [show min (dest + 32 + (read + len - (dest + 32))) base.size = read + len by omega]

/-- A padded variable-length read above an in-bounds word write is unaffected, even when the read
    reaches or lies beyond the concrete end of memory. -/
theorem write32_read_above_len_padded (src base : ByteArray) (dest read len : Nat)
    (hsrc : 32 ≤ src.size) (hlo : dest + 32 ≤ base.size)
    (habove : dest + 32 ≤ read)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base dest 32).readWithPadding read len = base.readWithPadding read len := by
  have hsize : (src.write 0 base dest 32).size = base.size := by
    rw [write32_eq src base dest hsrc (by omega), ByteArray.size_append,
      ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  by_cases hpast : base.size ≤ read
  · rw [readWithPadding_past_end base read len hpast hlen64]
    rw [readWithPadding_past_end (src.write 0 base dest 32) read len
      (by rw [hsize]; exact hpast) hlen64]
  · have hread : read < base.size := by omega
    by_cases hin : read + len ≤ base.size
    · exact write32_read_above_len src base dest read len hsrc (by omega)
        habove hin hpos hlen64
    have hspan : base.size ≤ read + min len base.size := by
      by_cases hle : len ≤ base.size
      · rw [min_eq_left hle]
        omega
      · rw [min_eq_right (by omega)]
        omega
    have hreadBase : ¬ read ≥ base.size := by omega
    unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
    rw [if_neg (by omega : ¬ len ≥ 2 ^ 64), if_neg hreadBase]
    simp only [hsize]
    have hextract :
        (src.write 0 base dest 32).extract read (read + min len base.size) =
          base.extract read (read + min len base.size) := by
      rw [write32_eq src base dest hsrc (by omega)]
      have hpre : (base.extract 0 dest ++ src.extract 0 32).size =
          dest + 32 := by
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega
      rw [extract_append_right_window _ _ _ _ (by rw [hpre]; exact habove), hpre]
      rw [extract_extract_BA]
      rw [show dest + 32 + (read - (dest + 32)) = read by omega]
      rw [show min (dest + 32 + (read + min len base.size - (dest + 32))) base.size =
          base.size by omega]
      apply ByteArray.ext
      simp only [ByteArray.data_extract]
      exact (Array.extract_eq_of_size_le_stop (by simpa using hspan)).symm
    rw [hextract]
    simp only [if_neg hreadBase, if_neg (by omega : ¬ len ≥ 2 ^ 64),
      ByteArray.size_extract]

/-- **Append-shaped write at memory end.**  A nonempty write from source offset `0` to
    destination offset `base.size` appends the requested source prefix. -/
theorem write_at_end_eq (src base : ByteArray) (len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) :
    src.write 0 base base.size len = base ++ src.extract 0 len := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (0 ≥ src.size) from by omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
  have hcopy : min len (src.size - 0) = len := by omega
  have htail : min base.size (base.size + len) - (base.size + len) = 0 := by omega
  have hgap : base.size - base.size = 0 := by omega
  rw [hcopy, htail, hgap]
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (by rfl : base.data.size ≤ base.size)]
  have hcopy2 : min len (src.data.size - 0) = len := by
    have : src.data.size = src.size := rfl
    omega
  rw [hcopy2]
  rw [show base.data.extract (base.size + len) = #[] from by
    apply Array.extract_eq_empty_of_le
    rw [show base.data.size = base.size from rfl]
    omega]
  simp

theorem write_at_end_eq_from (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    src.write srcAddr base base.size len = base ++ src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
  have hcopy : min len (src.size - srcAddr) = len := by omega
  have htail : min base.size (base.size + len) - (base.size + len) = 0 := by omega
  have hgap : base.size - base.size = 0 := by omega
  rw [hcopy, htail, hgap]
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (by rfl : base.data.size ≤ base.size)]
  have hcopyData : min len (src.data.size - srcAddr) = len := by
    have : src.data.size = src.size := rfl
    omega
  rw [hcopyData]
  rw [show base.data.extract (base.size + len) = #[] from by
    apply Array.extract_eq_empty_of_le
    rw [show base.data.size = base.size from rfl]
    omega]
  simp

theorem write_end_size_from (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    (src.write srcAddr base base.size len).size = base.size + len := by
  rw [write_at_end_eq_from src base srcAddr len hlen hsrc, ByteArray.size_append,
    ByteArray.size_extract]
  omega

theorem write_read_below_end_from (src base : ByteArray) (srcAddr len readAddr : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hbelow : readAddr + 32 ≤ base.size) :
    (src.write srcAddr base base.size len).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  rw [write_at_end_eq_from src base srcAddr len hlen hsrc]
  rw [readWithPadding_eq_extract _ readAddr (by rw [ByteArray.size_append, ByteArray.size_extract]; omega)]
  rw [extract_append_left _ _ _ _ (by omega)]
  exact (readWithPadding_eq_extract _ readAddr hbelow).symm

theorem write_end_extract_tail_from (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    (src.write srcAddr base base.size len).extract base.size (base.size + len) =
      src.extract srcAddr (srcAddr + len) := by
  rw [write_at_end_eq_from src base srcAddr len hlen hsrc]
  rw [show base.size + len = base.size + (src.extract srcAddr (srcAddr + len)).size by
    rw [ByteArray.size_extract]
    omega]
  rw [extract_append_right]

theorem write32_read_span_end (src base : ByteArray) (readAddr : ℕ)
    (hsrc : src.size = 32) (hstart : readAddr ≤ base.size) (hspan : base.size ≤ readAddr + 32) :
    (src.write 0 base base.size 32).readWithPadding readAddr 32 =
      base.extract readAddr base.size ++ src.extract 0 (readAddr + 32 - base.size) := by
  rw [write_at_end_eq src base 32 (by decide) (by omega)]
  rw [readWithPadding_eq_extract _ readAddr (by
    rw [ByteArray.size_append, ByteArray.size_extract]
    omega)]
  rw [extract_append_span _ _ _ _ hstart hspan]
  rw [extract_extract_BA]
  rw [show min (0 + (readAddr + 32 - base.size)) 32 =
      readAddr + 32 - base.size by omega]

/-- Reading back a 32-byte word write, allowing the write to extend memory by a zero gap. -/
theorem toByteArray_write_read_back_of_gap (b : UInt256) (mem : ByteArray) (off : ℕ)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding off 32 =
      UInt256.toByteArray b := by
  by_cases hle : off ≤ mem.size
  · rw [write32_read_back _ _ off (by rw [toByteArray_size]) hle]
    rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
    exact byteArray_extract_self _
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [readWithPadding_eq_extract _ off (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (off - mem.size))
      (UInt256.toByteArray b) off (off + 32) (by
        rw [ByteArray.size_append, ByteArray_zeroes_size]
        omega)]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    rw [show off - (mem.size + (off - mem.size)) = 0 by omega,
      show off + 32 - (mem.size + (off - mem.size)) = 32 by omega]
    rw [show (UInt256.toByteArray b).extract 0 32 = UInt256.toByteArray b from by
      rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]

/-- Reading below a 32-byte word write, allowing the write to extend memory by a zero gap. -/
theorem toByteArray_write_read_below_of_gap
    (b : UInt256) (mem : ByteArray) (off read : ℕ)
    (hread : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  by_cases hle : off ≤ mem.size
  · exact write32_read_below _ _ off read (by rw [toByteArray_size]) hle hbelow
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract _ read hread).symm

/-- Reading an arbitrary in-bounds window below a 32-byte word write is unaffected, even when
    the write extends memory by a zero gap. -/
theorem toByteArray_write_read_below_len_of_gap
    (b : UInt256) (mem : ByteArray) (off read len : ℕ)
    (hread : read + len ≤ mem.size) (hbelow : read + len ≤ off)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read len =
      mem.readWithPadding read len := by
  by_cases hle : off ≤ mem.size
  · exact write32_read_below_len _ _ off read len (by rw [toByteArray_size]) hle
      hbelow hread hpos hlen64
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract' _ read len hpos hlen64 hread).symm

/-- Reading inside the zero gap created by a word write beyond the concrete end of memory returns
exactly the requested number of zero bytes. -/
theorem toByteArray_write_read_gap_of_gap
    (b : UInt256) (mem : ByteArray) (off read len : ℕ)
    (hstart : mem.size ≤ read) (hstop : read + len ≤ off)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read len =
      ffi.ByteArray.zeroes len := by
  have hoff : mem.size ≤ off := by omega
  rw [toByteArray_write_eq b mem off hoff hgap]
  rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
      toByteArray_size]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega)]
  rw [extract_append_right_window mem (ffi.ByteArray.zeroes (off - mem.size))
    read (read + len) hstart]
  rw [zeroes_extract (off - mem.size) (read - mem.size)
    (read + len - mem.size) (by omega) (by omega)]
  congr 1
  omega

/-- A word write above a padded 32-byte read preserves the read even when the read straddles the
old concrete end of memory.  The zero gap introduced by the write is observationally identical to
the zeros supplied by `readWithPadding`. -/
theorem toByteArray_write_read_below_padded_of_gap
    (b : UInt256) (mem : ByteArray) (off read : ℕ)
    (hmem32 : 32 ≤ mem.size)
    (hbelow : read + 32 ≤ off) (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  by_cases hin : read + 32 ≤ mem.size
  · exact toByteArray_write_read_below_of_gap b mem off read hin hbelow hgap
  by_cases hpast : mem.size ≤ read
  · rw [toByteArray_write_read_gap_of_gap b mem off read 32 hpast hbelow
      (by decide) (by decide) hgap]
    exact (readWithPadding_past_end mem read 32 hpast (by decide)).symm
  · have hread : read < mem.size := by omega
    have hoff : mem.size ≤ off := by omega
    rw [toByteArray_write_eq b mem off hoff hgap]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_left _ (UInt256.toByteArray b) read (read + 32) (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_span mem (ffi.ByteArray.zeroes (off - mem.size))
      read (read + 32) (by omega) (by omega)]
    have hzero := zeroes_extract (off - mem.size) 0 (read + 32 - mem.size)
      (by omega) (by omega)
    simp only [Nat.sub_zero] at hzero
    rw [hzero]
    unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
    rw [if_neg (by norm_num : ¬ ((32 : Nat) ≥ 2 ^ 64)), if_neg (by omega)]
    simp only [min_eq_left hmem32]
    have hextract : mem.extract read (read + 32) = mem.extract read mem.size := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract]
      have h₁ : mem.data.extract read (read + 32) = mem.data.extract read :=
        Array.extract_eq_of_size_le_stop (by
          simpa using (by omega : mem.size ≤ read + 32))
      have h₂ : mem.data.extract read mem.size = mem.data.extract read :=
        Array.extract_eq_of_size_le_stop (by simp)
      exact h₁.trans h₂.symm
    rw [hextract, ByteArray.size_extract]
    rw [show min mem.size mem.size - read = mem.size - read by simp]
    rw [show 32 - (mem.size - read) = read + 32 - mem.size by omega]

/-- A word write above a padded variable-length read preserves the read even when the read
straddles the old concrete end of memory. -/
theorem toByteArray_write_read_below_len_padded_of_gap
    (b : UInt256) (mem : ByteArray) (off read len : ℕ)
    (hbelow : read + len ≤ off) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read len =
      mem.readWithPadding read len := by
  by_cases hin : read + len ≤ mem.size
  · exact toByteArray_write_read_below_len_of_gap b mem off read len hin hbelow
      hpos hlen64 hgap
  by_cases hpast : mem.size ≤ read
  · rw [toByteArray_write_read_gap_of_gap b mem off read len hpast hbelow
      hpos hlen64 hgap]
    exact (readWithPadding_past_end mem read len hpast hlen64).symm
  · have hread : read < mem.size := by omega
    have hoff : mem.size ≤ off := by omega
    have hspan : mem.size ≤ read + min len mem.size := by
      by_cases hle : len ≤ mem.size
      · rw [min_eq_left hle]
        omega
      · rw [min_eq_right (by omega)]
        omega
    rw [toByteArray_write_eq b mem off hoff hgap]
    rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_left _ (UInt256.toByteArray b) read (read + len) (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_span mem (ffi.ByteArray.zeroes (off - mem.size))
      read (read + len) (by omega) (by omega)]
    have hzero := zeroes_extract (off - mem.size) 0 (read + len - mem.size)
      (by omega) (by omega)
    simp only [Nat.sub_zero] at hzero
    rw [hzero]
    unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
    rw [if_neg (by omega : ¬ len ≥ 2 ^ 64), if_neg (by omega)]
    have hextract : mem.extract read (read + min len mem.size) =
        mem.extract read mem.size := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract]
      have h₁ : mem.data.extract read (read + min len mem.size) = mem.data.extract read :=
        Array.extract_eq_of_size_le_stop (by simpa using hspan)
      have h₂ : mem.data.extract read mem.size = mem.data.extract read :=
        Array.extract_eq_of_size_le_stop (by simp)
      exact h₁.trans h₂.symm
    rw [hextract]
    simp only [ByteArray.size_extract]
    rw [show min mem.size mem.size - read = mem.size - read by simp]
    rw [show len - (mem.size - read) = read + len - mem.size by omega]

/-- Reading a window inside a 32-byte word write, allowing the write to extend memory by a zero
    gap. -/
theorem toByteArray_write_read_window_of_gap
    (b : UInt256) (mem : ByteArray) (off start len : Nat)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding (off + start) len =
      (UInt256.toByteArray b).extract start (start + len) := by
  by_cases hle : off ≤ mem.size
  · have hprefix : (mem.extract 0 off).size = off := by
      rw [ByteArray.size_extract]
      omega
    have hword : ((UInt256.toByteArray b).extract 0 32).size = 32 := by
      rw [ByteArray.size_extract, toByteArray_size]
      omega
    rw [write32_eq _ _ off (by rw [toByteArray_size]) hle]
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hword]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hprefix, hword]; omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show off + start - off = start by omega,
      show off + start + len - off = start + len by omega]
    rw [extract_extract_BA]
    rw [show 0 + start = start by omega,
      show min (0 + (start + len)) 32 = start + len by omega]
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    have hprefix :
        (mem ++ ffi.ByteArray.zeroes (off - mem.size)).size = off := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen64 (by
      rw [ByteArray.size_append, hprefix, toByteArray_size]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show off + start - off = start by omega,
      show off + start + len - off = start + len by omega]

/-! ## 4. Two-word scratch memory for mapping-slot hashes -/

noncomputable def wordAt0Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 0 32

noncomputable def wordAt32Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 32 32

noncomputable def twoWordHashMem (key slot : UInt256) (mem : ByteArray) : ByteArray :=
  wordAt32Mem slot (wordAt0Mem key mem)

theorem wordAt0Mem_read0 (word : UInt256) (mem : ByteArray) :
    (wordAt0Mem word mem).readWithPadding 0 32 = UInt256.toByteArray word := by
  unfold wordAt0Mem
  rw [write0_read_back_gen (UInt256.toByteArray word) mem 32
    (by norm_num)
    (by rw [toByteArray_size])
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem wordAt0Mem_keccak_word (word : UInt256) (mem : ByteArray) :
    UInt256.ofNat
      (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem word mem).readWithPadding 0 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (UInt256.toByteArray word))) := by
  rw [wordAt0Mem_read0]

theorem writeWord_size_of_96 (base : ByteArray) (w : UInt256) (dest : ℕ)
    (hbase : base.size = 96) (hdest : dest + 32 ≤ 96) :
    ((UInt256.toByteArray w).write 0 base dest 32).size = 96 := by
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hbase, toByteArray_size]
  omega

theorem wordAt0Mem_size_96 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96) :
    (wordAt0Mem word mem).size = 96 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_96 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96) :
    (wordAt32Mem word mem).size = 96 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem twoWordHashMem_size_96 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).size = 96 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_96 slot (wordAt0Mem_size_96 key hmem)

theorem twoWordHashMem_read0 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_96 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_96 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_96 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_96 key hmem])]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

set_option maxHeartbeats 800000 in
theorem twoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_96 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_96 key slot hmem]; omega),
      twoWordHashMem_read0 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_96 key slot hmem]; omega),
      twoWordHashMem_read32 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

/-! ## 5. `RETURN`/ABI encoding: `UInt256.toByteArray` as the big-endian word list -/

/-- **`toByteArray` is the 32-byte big-endian list.**  `UInt256.toByteArray v` (the EVM
    `MSTORE`/`RETURN` word, with the opaque `ffi.zeroes` leading pad) equals the *concrete*
    `EVM.Word.toBytesBE v` (`List.replicate`-padded), as `ByteArray`s.  The bridge between the
    opaque-memory and the pure-ABI worlds; the only opacity (`ffi.zeroes`) cancels. -/
theorem toByteArray_eq_toBytesBE (v : UInt256) :
    UInt256.toByteArray v = ⟨(EVM.Word.toBytesBE v).toArray⟩ := by
  have hb : (BE v.toNat).size ≤ 32 := by
    apply BE_le; have := v.val.isLt; simp [UInt256.size, UInt256.toNat]
  apply ByteArray.ext; apply Array.toList_inj.mp
  rw [show (((EVM.Word.toBytesBE v).toArray).toList) = EVM.Word.toBytesBE v from by simp]
  unfold UInt256.toByteArray EVM.Word.toBytesBE
  rw [ByteArray.data_append, Array.toList_append, byteArray_zeroes_toList,
      show ((BE v.toNat).data.toList) = toBytesBigEndian v.toNat from by simp [BE]]
  rw [show (BE v.toNat).size = (toBytesBigEndian v.toNat).length from by simp [BE]]
  rfl

/-- Turning `EVM.Word.toBytesBE` into a `ByteArray` gives the same 32-byte word encoding as
    `UInt256.toByteArray`. -/
theorem word_toBytesBE_toByteArray_eq_toByteArray (w : UInt256) :
    (EVM.Word.toBytesBE w).toByteArray = UInt256.toByteArray w := by
  rw [toByteArray_eq_toBytesBE]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

/-- `EVM.Word.toBytesBE` as a `ByteArray` is 32 bytes. -/
theorem word_toBytesBE_toByteArray_size (w : UInt256) :
    (EVM.Word.toBytesBE w).toByteArray.size = 32 := by
  rw [word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_size]

theorem word_toBytesBE_inj {a b : UInt256}
    (h : EVM.Word.toBytesBE a = EVM.Word.toBytesBE b) : a = b := by
  apply u256_inj
  have ha :
      fromBytesBigEndian (EVM.Word.toBytesBE a) = a.toNat := by
    have hba := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray a)
    simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
      hba.trans (fromByteArrayBigEndian_toByteArray a)
  have hb :
      fromBytesBigEndian (EVM.Word.toBytesBE b) = b.toNat := by
    have hbb := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray b)
    simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
      hbb.trans (fromByteArrayBigEndian_toByteArray b)
  rw [← ha, ← hb, h]

/-! ## 6. `CALLDATALOAD`/`SHR` selector extraction (reusable byte arithmetic) -/

/-- `fromBytes'` (little-endian) of an append splits at the byte boundary. -/
theorem fromBytes'_append (a b : List UInt8) :
    fromBytes' (a ++ b) = fromBytes' a + 2 ^ (8 * a.length) * fromBytes' b := by
  induction a with
  | nil => simp [fromBytes']
  | cons x xs ih =>
    simp only [List.cons_append, fromBytes', ih, List.length_cons]
    rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length from by ring, pow_add]; ring

theorem fromBytesBigEndian_append_zeros (l : List UInt8) (k : Nat) :
    fromBytesBigEndian (l ++ List.replicate k 0) =
      fromBytesBigEndian l * 2 ^ (8 * k) := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, List.reverse_replicate, fromBytes'_append, fromBytes'_replicate_zero]
  simp [Nat.mul_comm]

/-- Big-endian division drops the low `|l2|` bytes. -/
theorem fromBytesBigEndian_append_div (l1 l2 : List UInt8) :
    fromBytesBigEndian (l1 ++ l2) / 2 ^ (8 * l2.length) = fromBytesBigEndian l1 := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, fromBytes'_append, List.length_reverse]
  have hlt : fromBytes' l2.reverse < 2 ^ (8 * l2.length) := by
    have := fromBytes'_le (bs := l2.reverse); rwa [List.length_reverse] at this
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

theorem copySlice32_toList (cd : ByteArray) :
    (cd.copySlice 0 ByteArray.empty 0 32).data.toList = cd.data.toList.take 32 := by
  rw [ByteArray.data_copySlice]; simp [Array.toList_extract, List.extract]
theorem copySlice32_size (cd : ByteArray) :
    (cd.copySlice 0 ByteArray.empty 0 32).size = min 32 cd.size := by
  show (cd.copySlice 0 ByteArray.empty 0 32).data.size = min 32 cd.size
  rw [← Array.length_toList, copySlice32_toList, List.length_take, Array.length_toList]; rfl

/-- `readBytes cd 0 32` is the first 32 bytes of `cd`, right-padded with zeros to length 32. -/
theorem readBytes32_toList (cd : ByteArray) :
    (ByteArray.readBytes cd 0 32).data.toList
      = cd.data.toList.take 32 ++ List.replicate (32 - min 32 cd.size) 0 := by
  unfold ByteArray.readBytes
  rw [if_pos (by decide : (decide (0 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true)]
  rw [ByteArray.toList_data_append, copySlice32_toList, byteArray_zeroes_toList, copySlice32_size]

set_option maxHeartbeats 800000 in
theorem readWithPadding_zero_toList_of_size_lt32 (b : ByteArray)
    (hpos : b.size ≠ 0) (hshort : b.size < 32) :
    (b.readWithPadding 0 32).toList =
      b.toList ++ List.replicate (32 - b.size) 0 := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by norm_num : ¬ ((32 : Nat) ≥ 2 ^ 64))]
  rw [if_neg (by omega : ¬ (0 : Nat) ≥ b.size)]
  change
    (b.extract 0 (0 + min 32 b.size) ++
        ffi.ByteArray.zeroes (32 - (b.extract 0 (0 + min 32 b.size)).size)).toList =
      b.toList ++ List.replicate (32 - b.size) 0
  rw [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, List.drop_zero,
    min_eq_right (by omega : b.size ≤ 32)]
  rw [byteArray_toList_eq]
  rw [show 0 + b.size - 0 = b.data.toList.length by
    rw [Array.length_toList]
    have hsz : b.size = b.data.size := rfl
    omega]
  rw [List.take_length]
  have hreadSize : (b.extract 0 (0 + b.size)).size = b.size := by
    rw [ByteArray.size_extract]
    omega
  rw [hreadSize]
  rw [byteArray_zeroes_toList]

theorem readBytes32_len (cd : ByteArray) :
    (ByteArray.readBytes cd 0 32).data.toList.length = 32 := by
  rw [readBytes32_toList, List.length_append, List.length_take, List.length_replicate]
  have : min 32 cd.data.toList.length = min 32 cd.size := by rw [Array.length_toList]; rfl
  omega

/-- **EVM selector extraction.**  `(uInt256OfByteArray (readBytes cd 0 32)) >>> 224` — the EVM's
    `CALLDATALOAD; PUSH 0xe0; SHR` — equals the big-endian number of `cd`'s first four bytes
    (for `4 ≤ cd.size`). -/
theorem selector_toNat (cd : ByteArray) (h : 4 ≤ cd.size) :
    (UInt256.shiftRight (uInt256OfByteArray (ByteArray.readBytes cd 0 32)) ⟨224⟩).toNat
      = fromBytesBigEndian (cd.data.toList.take 4) := by
  have hlen := readBytes32_len cd
  have hV : fromBytes' (ByteArray.readBytes cd 0 32).data.toList.reverse < 2 ^ 256 := by
    have := fromBytes'_le (bs := (ByteArray.readBytes cd 0 32).data.toList.reverse)
    rwa [List.length_reverse, hlen] at this
  unfold UInt256.shiftRight uInt256OfByteArray
  rw [if_neg (by decide : ¬ ((⟨224⟩ : UInt256).val ≥ 256))]
  show ((UInt256.ofNat _).val >>> (⟨224⟩ : UInt256).val).val = _
  rw [Fin.shiftRight_val]
  show (UInt256.ofNat _).val.val >>> (224 : ℕ) = _
  rw [Nat.shiftRight_eq_div_pow]
  show (fromBytes' _ % UInt256.size) / 2 ^ 224 = _
  rw [show UInt256.size = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hV]
  show fromBytesBigEndian (ByteArray.readBytes cd 0 32).data.toList / 2 ^ 224 = _
  conv_lhs => rw [← List.take_append_drop 4 (ByteArray.readBytes cd 0 32).data.toList]
  rw [show (224 : ℕ) = 8 * ((ByteArray.readBytes cd 0 32).data.toList.drop 4).length from by
        rw [List.length_drop, hlen], fromBytesBigEndian_append_div]
  congr 1
  have h4 : 4 ≤ cd.data.toList.length := by rw [Array.length_toList]; exact h
  rw [readBytes32_toList, List.take_append_of_le_length (by rw [List.length_take]; omega),
      List.take_take, show min 4 32 = 4 from rfl]

/-! ## 7. Generic `MLOAD` word-value helper -/

/-- Simplify the value pushed by `MLOAD` when the offset is in bounds and below the active-word
    limit, leaving the byte read uninterpreted. -/
theorem mloadValue_eq_readWithPadding_of_lt_size
    (mem : ByteArray) (aw off : UInt256) (memSize : Nat)
    (hsize : mem.size = memSize) (hmem : off.toNat < memSize)
    (haw : ¬ off ≥ aw * ⟨32⟩) :
    (if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32)) := by
  rw [if_neg (not_or.mpr ⟨by rw [hsize]; omega, haw⟩)]

/-- Simplify the value pushed by `MLOAD` when the 32-byte memory read is known. -/
theorem mloadWordValue_of_readWithPadding {mem : ByteArray} {aw off v : UInt256}
    (hmem : off.toNat < mem.size)
    (haw : ¬ off ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding off.toNat 32 = UInt256.toByteArray v) :
    (if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))) = v := by
  rw [if_neg (not_or.mpr ⟨by omega, haw⟩), hread, fromByteArrayBigEndian_toByteArray,
    u256_ofNat_toNat]

/-! ## 8. ABI calldata decode coupling (shared by every contract with arguments) -/

/-- `uInt256OfByteArray` is the big-endian decode then `ofNat`. -/
theorem uInt256OfByteArray_eq (arr : ByteArray) :
    uInt256OfByteArray arr = UInt256.ofNat (fromByteArrayBigEndian arr) := by
  unfold uInt256OfByteArray fromByteArrayBigEndian fromBytesBigEndian
  rw [byteArray_toList_eq]; rfl

theorem uInt256OfByteArray_readWithPadding_zero_low_zero (b : ByteArray)
    (hpos : b.size ≠ 0) (hshort : b.size < 32) :
    (uInt256OfByteArray (b.readWithPadding 0 32)).toNat %
        2 ^ (8 * (32 - b.size)) = 0 := by
  have hlist := readWithPadding_zero_toList_of_size_lt32 b hpos hshort
  have hlen : (b.readWithPadding 0 32).toList.length = 32 := by
    rw [hlist, List.length_append, List.length_replicate]
    rw [byteArray_toList_eq, Array.length_toList]
    have hsz : b.size = b.data.size := rfl
    omega
  rw [uInt256OfByteArray_eq]
  have hlt :
      fromByteArrayBigEndian (b.readWithPadding 0 32) < UInt256.size := by
    unfold fromByteArrayBigEndian fromBytesBigEndian
    have hle := fromBytes'_le (bs := (b.readWithPadding 0 32).data.toList.reverse)
    rw [List.length_reverse, ← byteArray_toList_eq, hlen] at hle
    simpa [UInt256.size] using hle
  rw [ulit_toNat' _ hlt]
  unfold fromByteArrayBigEndian fromBytesBigEndian Function.comp
  rw [hlist]
  rw [List.reverse_append, List.reverse_replicate, fromBytes'_append,
    fromBytes'_replicate_zero]
  simp only [List.length_replicate, zero_add]
  exact Nat.mul_mod_right _ _

theorem fromBytes'_inj_of_length {xs ys : List UInt8}
    (hlen : xs.length = ys.length)
    (h : fromBytes' xs = fromBytes' ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp at hlen
          unfold fromBytes' at h
          have hx : x.toFin.val < 2 ^ 8 := x.toFin.isLt
          have hy : y.toFin.val < 2 ^ 8 := y.toFin.isLt
          have hheadNat : x.toFin.val = y.toFin.val := by
            have hmod := congrArg (fun n => n % 2 ^ 8) h
            omega
          have htail : fromBytes' xs = fromBytes' ys := by
            have hdiv := congrArg (fun n => n / 2 ^ 8) h
            omega
          have hxy : x = y := UInt8.toNat_inj.mp hheadNat
          rw [hxy]
          congr
          exact ih hlen htail

theorem fromBytesBigEndian_inj_of_length {xs ys : List UInt8}
    (hlen : xs.length = ys.length)
    (h : fromBytesBigEndian xs = fromBytesBigEndian ys) : xs = ys := by
  unfold fromBytesBigEndian at h
  apply List.reverse_injective
  apply fromBytes'_inj_of_length
  · simp [hlen]
  · exact h

theorem toBytesBE_uInt256OfByteArray_of_size {arr : ByteArray}
    (hsize : arr.size = 32) :
    EVM.Word.toBytesBE (uInt256OfByteArray arr) = arr.toList := by
  apply fromBytesBigEndian_inj_of_length
  · rw [show (EVM.Word.toBytesBE (uInt256OfByteArray arr)).length = 32 by
        simpa using word_toBytesBE_toByteArray_size (uInt256OfByteArray arr)]
    simpa [byteArray_toList_eq] using hsize.symm
  · have hleft :
        fromBytesBigEndian (EVM.Word.toBytesBE (uInt256OfByteArray arr)) =
          (uInt256OfByteArray arr).toNat := by
      have h := congrArg fromByteArrayBigEndian
        (word_toBytesBE_toByteArray_eq_toByteArray (uInt256OfByteArray arr))
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        h.trans (fromByteArrayBigEndian_toByteArray (uInt256OfByteArray arr))
    have hright : (uInt256OfByteArray arr).toNat = fromBytesBigEndian arr.toList := by
      rw [uInt256OfByteArray_eq]
      unfold fromByteArrayBigEndian
      have hlen : arr.toList.length = 32 := by
        simpa [byteArray_toList_eq] using hsize
      have hlt : fromBytesBigEndian arr.toList < UInt256.size := by
        unfold fromBytesBigEndian
        have hle := fromBytes'_le (bs := arr.toList.reverse)
        rw [List.length_reverse, hlen] at hle
        simpa [UInt256.size] using hle
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        (ulit_toNat' (fromBytesBigEndian arr.toList) hlt)
    rw [hleft, hright]

theorem toBytesBE_keccak_uInt256OfByteArray (b : ByteArray) :
    EVM.Word.toBytesBE (uInt256OfByteArray (ffi.KEC b)) = (ffi.KEC b).toList :=
  toBytesBE_uInt256OfByteArray_of_size (keccak_size b)

/-- `readBytes cd off 32` is `cd`'s bytes `[off, off+32)` when `cd` has at least `off+32` bytes. -/
theorem readBytes_at_toList (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size)
    (hoff : off < 2 ^ 64) :
    (ByteArray.readBytes cd off 32).data.toList = (cd.data.toList.drop off).take 32 := by
  have hcopy : (cd.copySlice off ByteArray.empty 0 32).data = cd.data.extract off (off + 32) := by
    rw [ByteArray.data_copySlice]; simp
  have hcl : (cd.copySlice off ByteArray.empty 0 32).data.toList = (cd.data.toList.drop off).take 32 := by
    rw [hcopy, Array.toList_extract]; rw [List.extract_eq_take_drop]; congr 1; omega
  have hds : cd.data.size = cd.size := rfl
  have hcsize : (cd.copySlice off ByteArray.empty 0 32).size = 32 := by
    show (cd.copySlice off ByteArray.empty 0 32).data.size = 32
    rw [← Array.length_toList, hcl, List.length_take, List.length_drop, Array.length_toList]; omega
  unfold ByteArray.readBytes
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hoff, by decide⟩)]
  change (cd.copySlice off ByteArray.empty 0 32 ++
      ffi.ByteArray.zeroes (32 - (cd.copySlice off ByteArray.empty 0 32).size)).data.toList =
    (cd.data.toList.drop off).take 32
  rw [ByteArray.data_append, Array.toList_append, hcl, byteArray_zeroes_toList, hcsize]
  simp

theorem readBytes_at_toList_any (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size) :
    (ByteArray.readBytes cd off 32).data.toList = (cd.data.toList.drop off).take 32 := by
  by_cases hoff : off < 2 ^ 64
  · exact readBytes_at_toList cd off hsz hoff
  · unfold ByteArray.readBytes
    rw [if_neg (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      intro h
      exact hoff h.1)]
    have hlen : ((cd.toList.drop off).take 32).length = 32 := by
      have htlen : cd.toList.length = cd.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_take, List.length_drop, htlen]
      omega
    have hreadSize : (ByteArray.mk ((cd.toList.drop off).take 32).toArray).size = 32 := by
      change ((cd.toList.drop off).take 32).toArray.size = 32
      simp [hlen]
    change ((ByteArray.mk ((cd.toList.drop off).take 32).toArray) ++
        ffi.ByteArray.zeroes
          (32 - (ByteArray.mk ((cd.toList.drop off).take 32).toArray).size)).data.toList =
      (cd.data.toList.drop off).take 32
    rw [ByteArray.data_append, Array.toList_append, byteArray_zeroes_toList, hreadSize]
    simp [byteArray_toList_eq]

/-- The Solm decoder's word at byte offset `off` equals the EVM's `uInt256OfByteArray (readBytes off)`. -/
theorem decode_word_at_eq (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size) (hoff : off < 2 ^ 64) :
    ABI.bytesToWord ((cd.toList.drop off).take 32)
      = uInt256OfByteArray (cd.readBytes off 32) := by
  rw [uInt256OfByteArray_eq]
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 2
  rw [byteArray_toList_eq (cd.readBytes off 32), readBytes_at_toList _ _ hsz hoff]
  simp [byteArray_toList_eq]

/-- Decoding 32 bytes as an ABI word and writing it back big-endian returns the same 32 bytes. -/
theorem toBytesBE_bytesToWord_of_length {bs : List UInt8}
    (hlen : bs.length = 32) :
    EVM.Word.toBytesBE (ABI.bytesToWord bs) = bs := by
  apply fromBytesBigEndian_inj_of_length
  · rw [show (EVM.Word.toBytesBE (ABI.bytesToWord bs)).length = 32 by
        simpa using word_toBytesBE_toByteArray_size (ABI.bytesToWord bs), hlen]
  · have hleft :
        fromBytesBigEndian (EVM.Word.toBytesBE (ABI.bytesToWord bs)) =
          (ABI.bytesToWord bs).toNat := by
      have h := congrArg fromByteArrayBigEndian
        (word_toBytesBE_toByteArray_eq_toByteArray (ABI.bytesToWord bs))
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        h.trans (fromByteArrayBigEndian_toByteArray (ABI.bytesToWord bs))
    have hright : (ABI.bytesToWord bs).toNat = fromBytesBigEndian bs := by
      unfold ABI.bytesToWord
      have hlt : fromBytesBigEndian bs < UInt256.size := by
        unfold fromBytesBigEndian
        have hle := fromBytes'_le (bs := bs.reverse)
        rw [List.length_reverse, hlen] at hle
        simpa [UInt256.size] using hle
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        (ulit_toNat' (fromBytesBigEndian bs) hlt)
    rw [hleft, hright]

theorem decode_word_at_eq_any (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size) :
    ABI.bytesToWord ((cd.toList.drop off).take 32)
      = uInt256OfByteArray (cd.readBytes off 32) := by
  rw [uInt256OfByteArray_eq]
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 2
  rw [byteArray_toList_eq (cd.readBytes off 32), readBytes_at_toList_any _ _ hsz]
  simp [byteArray_toList_eq]

/-! ## 9. Mapping storage-slot and load coupling

Solidity stores `mapping[key]` at base slot `s` in `keccak256(key ‖ s)` (each a 32-byte big-endian
word); the Solm layout (`Solm.SolidityLayout`) computes exactly
`uInt256OfByteArray (KEC (keyWord.toByteArray ++ s.toByteArray))`.  The EVM bytecode writes the key
and slot into scratch memory and runs `KECCAK256`, and `RD.keccak256` pushes
`UInt256.ofNat (fromByteArrayBigEndian (KEC …))`.  These lemmas bridge the two representations so a
mapping `SLOAD`/`SSTORE` at the EVM-computed slot couples to the Solm storage ref's slot, and
`RD.sload`'s pushed value couples to the Solm `storageLoad`.  The byte-preimage (that the scratch
memory reads back as `key ++ slot`) and the partial-slot store decoding are reused from the existing
memory/`storageLocStore` lemmas; these supply the mapping-specific keccak-slot identities. -/

/-- The slot word an EVM `KECCAK256` pushes (`RD.keccak256`'s result — the big-endian decode of the
    hash) is exactly the Solm layout's mapping-slot interpretation `uInt256OfByteArray (KEC …)`. -/
theorem keccakSlot_eq (b : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC b)) = uInt256OfByteArray (ffi.KEC b) :=
  (uInt256OfByteArray_eq _).symm

/-- **Single-mapping slot.**  The EVM `KECCAK256` over the 64-byte preimage `key ‖ baseSlot` (both
    32-byte big-endian words) yields the Solm layout slot for `mapping[key]` at base `baseSlot`. -/
theorem mappingSlot_single (key baseSlot : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray)))
      = uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray)) :=
  keccakSlot_eq _


end Reasoning.Theory

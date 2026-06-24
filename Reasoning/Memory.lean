import Reasoning.EVMWord
import Reasoning.Stepping

/-!
# Memory — reusable EVM memory / `ByteArray` lemmas

The EVM `MSTORE`/`MLOAD`/`RETURN` and the `UInt256.toByteArray` word encoding are *computable*
`ByteArray` operations — **not** opaque like `D_J`/keccak.  The single genuine opacity is the
*content* of `ffi.ByteArray.zeroes` (the `memset_zero` extern): evmlean axiomatizes only its
**size** (`ByteArray_zeroes_size`), not that the bytes are `0`.  We admit that one extern-spec
fact (`byteArray_zeroes_toList`) and **prove everything else** as generic, contract-agnostic
lemmas: the big-endian byte round-trip, `fromByteArrayBigEndian ∘ toByteArray = toNat`, the
`MSTORE`-then-`MLOAD`/`RETURN` round-trip, and the `toByteArray`/`toBytesBE` bridge.  ABI-level
encode/decode reasoning lives in `Reasoning.ABI` (which imports this module).
-/

open Ethereum Ethereum.EVM Solm ABI

set_option maxRecDepth 8000

namespace Reasoning.Theory

/-- **Trusted (extern spec).** `ffi.ByteArray.zeroes` (`@[extern "memset_zero"]`) yields zero
    bytes.  Companion to evmlean's admitted `ByteArray_zeroes_size`; the only `ffi.zeroes` fact
    not already derivable from the base.  Everything below is proved from it. -/
axiom byteArray_zeroes_toList (n : USize) :
    (ffi.ByteArray.zeroes n).data.toList = List.replicate n.toNat 0

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

/-- The little-endian round-trip `fromBytes' (toBytes' x) = x` (re-proved; evmlean's is
    `private`). -/
theorem fromBytes'_toBytes' (x : ℕ) : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp [UInt8.size]
    exact Nat.mod_add_div _ _

/-- Big-endian round-trip: decoding the big-endian bytes of `x` gives back `x`. -/
theorem fromBytesBigEndian_toBytesBigEndian (x : ℕ) :
    fromBytesBigEndian (toBytesBigEndian x) = x := by
  simp only [fromBytesBigEndian, toBytesBigEndian, Function.comp, List.reverse_reverse]
  exact fromBytes'_toBytes' x

/-- Nonnegative integers are embedded as their natural-value EVM word. -/
theorem wordOfInt_nonneg (i : Int) (h0 : 0 ≤ i) :
    EVM.wordOfInt i = EVM.word i.toNat := by
  rw [EVM.wordOfInt, if_neg (by omega)]

/-- Little-endian word-byte round-trip for `EVM.Word.toBytesLEWithSizeProof`. -/
theorem fromBytes'_toBytesLEWithSizeProof (w : UInt256) :
    fromBytes' (EVM.Word.toBytesLEWithSizeProof w).1 = w.toNat := by
  show fromBytes' (toBytes' w.val ++ List.replicate (32 - (toBytes' w.val).length) 0) = w.toNat
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']
  rfl

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

/-- Reading the appended tail back. -/
theorem extract_append_right (A B : ByteArray) :
    (A ++ B).extract A.size (A.size + B.size) = B := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append]
  show (A.data ++ B.data).extract A.data.size (A.data.size + B.data.size) = B.data
  rw [Array.extract_append_right]; simp

/-- `(A ++ B).size = A.size + B.size` for `ByteArray`. -/
theorem byteArray_size_append (A B : ByteArray) : (A ++ B).size = A.size + B.size :=
  ByteArray.size_append

/-- `ffi.ByteArray.zeroes` of a `toNat`-zero size is the empty array. -/
theorem zeroes_zero {n : USize} (hn : n.toNat = 0) : ffi.ByteArray.zeroes n = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [byteArray_zeroes_toList, hn]; rfl

/-- **MSTORE write.**  Storing a 32-byte word `v` at offset `off ≥ mem.size` appends it past a
    zero gap: `mem ++ zeroes (off - mem.size) ++ v.toByteArray`.  (Generic, contract-agnostic;
    `off - mem.size < USize.size` rules out the address wrap.) -/
theorem toByteArray_write_eq (v : UInt256) (mem : ByteArray) (off : ℕ)
    (hoff : mem.size ≤ off) (hb : off - mem.size < USize.size) :
    (UInt256.toByteArray v).write 0 mem off 32
      = mem ++ ffi.ByteArray.zeroes (USize.ofNat (off - mem.size)) ++ UInt256.toByteArray v := by
  have hsz : (UInt256.toByteArray v).data.size = 32 := UInt256.toByteArrayWithSizeProof v |>.2
  have hpz : (ffi.ByteArray.zeroes (USize.ofNat (off - mem.size))).data.size = off - mem.size := by
    rw [show (ffi.ByteArray.zeroes (USize.ofNat (off - mem.size))).data.size
          = (ffi.ByteArray.zeroes (USize.ofNat (off - mem.size))).size from rfl,
        ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' hb]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ ((32:ℕ) = 0)),
      if_neg (show ¬ (0 ≥ (UInt256.toByteArray v).size) from by
                rw [show (UInt256.toByteArray v).size = 32 from hsz]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append,
    show (⟨↑(off - mem.size)⟩ : USize) = USize.ofNat (off - mem.size) from rfl]
  have hv : v.toByteArray.size = 32 := hsz
  have hDsz : (mem.data ++ (ffi.ByteArray.zeroes (USize.ofNat (off - mem.size))).data).size = off := by
    rw [Array.size_append, hpz]; show mem.size + (off - mem.size) = off; omega
  rw [hv, show (min 32 (32 - 0) : ℕ) = 32 from rfl,
      show min mem.size (off + 32) - (off + 32) = 0 from by omega,
      show (ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize)).data = (#[] : Array UInt8) from by
        rw [show (⟨↑(0:ℕ)⟩ : USize) = USize.ofNat 0 from rfl,
            zeroes_zero (n := USize.ofNat 0) (by rw [USize.toNat_ofNat_of_lt' (by omega)])]; rfl]
  rw [Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hDsz]),
      Array.extract_eq_self_of_le (show v.toByteArray.data.size ≤ 0 + (32 + 0) from by rw [hsz]),
      Array.extract_eq_empty_of_le (by rw [hDsz]; omega),
      Array.append_empty]

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
  have hz0 : ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize) = ByteArray.empty :=
    zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.zero_add, show base.data.size = base.size from rfl]

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

/-- `empty ++ A = A`. -/
theorem empty_append (A : ByteArray) : ByteArray.empty ++ A = A := by
  apply ByteArray.ext
  rw [ByteArray.data_append]; show #[] ++ A.data = A.data; rw [Array.empty_append]

/-- A `< 2^32` natural is below `USize.size` on every supported platform. -/
theorem lt_usize (n : ℕ) (h : n < 2 ^ 32) : n < USize.size := by
  rcases System.Platform.numBits_eq with he | he <;> rw [USize.size, he] <;> omega

theorem zeroes32_extract_zeroes (n : ℕ) (hn : n ≤ 32) :
    (ffi.ByteArray.zeroes (USize.ofNat 32)).extract 0 n =
      ffi.ByteArray.zeroes (USize.ofNat n) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, byteArray_zeroes_toList,
    byteArray_zeroes_toList]
  have h32 : (USize.ofNat 32).toNat = 32 := by
    exact USize.toNat_ofNat_of_lt' (lt_usize 32 (by norm_num))
  have hn' : (USize.ofNat n).toNat = n := by
    exact USize.toNat_ofNat_of_lt' (lt_usize n (by omega))
  rw [h32, hn']
  rw [List.extract_eq_take_drop, List.drop_zero, List.take_replicate]
  rw [show min (n - 0) 32 = n by omega]

theorem zero_toByteArray_eq_zeroes32 :
    UInt256.toByteArray (⟨0⟩ : UInt256) = ffi.ByteArray.zeroes (USize.ofNat 32) := by
  have h32 : (USize.ofNat 32).toNat = 32 :=
    USize.toNat_ofNat_of_lt' (lt_usize 32 (by norm_num))
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [UInt256.toByteArray, BE, Ethereum.toBytesBigEndian, Ethereum.toBytes',
    byteArray_zeroes_toList, h32]
  rw [show (OfNat.ofNat 32 : USize).toNat = 32 by exact h32]
  rfl

/-- The size of a small `zeroes` block (no `USize` wrap). -/
theorem zeroes_ofNat_size (n : ℕ) (h : n < 2 ^ 32) :
    (ffi.ByteArray.zeroes (USize.ofNat n)).size = n := by
  rw [ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' (lt_usize n h)]

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
  rw [zeroes_zero (n := ⟨↑(32:ℕ) - ↑(32:ℕ)⟩)
        (by show (↑(32:ℕ) - ↑(32:ℕ) : BitVec System.Platform.numBits).toNat = 0; rw [sub_self]; rfl)]
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
  rw [zeroes_zero (n := ⟨↑len - ↑len⟩)
        (by show (↑len - ↑len : BitVec System.Platform.numBits).toNat = 0; rw [sub_self]; rfl)]
  apply ByteArray.ext; rw [ByteArray.data_append]; show _ ++ #[] = _; rw [Array.append_empty]

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
  have hz0 : ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize) = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.add_zero, Nat.zero_add, show base.data.size = base.size from rfl]

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
  have hz0 : ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize) = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.add_zero, show base.data.size = base.size from rfl]

/-- **`write` appending at the end from an arbitrary source window.**  If the destination offset is
    exactly `base.size`, the write is the old base followed by the requested source slice. -/
theorem write_end_eq_from (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    src.write srcAddr base base.size len =
      base ++ src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (srcAddr ≥ src.size) from by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min len (src.size - srcAddr) = len := by omega
  have hsp : min base.size (base.size + len) - (base.size + len) = 0 :=
    Nat.sub_eq_zero_of_le (Nat.min_le_right _ _)
  have hdp : base.size - base.size = 0 := by omega
  have hz0 : ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize) = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.add_zero, show base.data.size = base.size from rfl]
  have hprefix : base.data.extract 0 base.size = base.data :=
    Array.extract_eq_self_of_le (by rfl)
  have htail : base.data.extract (base.size + len) base.size = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  rw [hprefix, htail, Array.append_empty]

/-- Size of an end-append write from an arbitrary source window. -/
theorem write_end_size_from (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    (src.write srcAddr base base.size len).size = base.size + len := by
  rw [write_end_eq_from src base srcAddr len hlen hsrc, ByteArray.size_append,
    ByteArray.size_extract]
  omega

theorem write_end_extract_tail_from (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    (src.write srcAddr base base.size len).extract base.size (base.size + len) =
      src.extract srcAddr (srcAddr + len) := by
  rw [write_end_eq_from src base srcAddr len hlen hsrc]
  exact extract_append_right'
    base (src.extract srcAddr (srcAddr + len)) base.size (base.size + len)
    rfl
    (by
      rw [ByteArray.size_extract]
      omega)

/-- Data shape of a write to destination offset `0` that may extend the destination. -/
theorem write0_data (src base : ByteArray) (len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) :
    (src.write 0 base 0 len).data = src.data.extract 0 len ++ base.data.extract len base.data.size := by
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (0 ≥ src.size) from by omega)]
  simp only [show min len (src.size - 0) = len from by omega,
    show min base.size (0 + len) - (0 + len) = 0 from by omega,
    show 0 - base.size = 0 from by omega]
  have hz : (ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize)).data = (#[] : Array UInt8) := by
    rw [zeroes_zero (n := ⟨↑(0:ℕ)⟩) (by rfl)]
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
  have hz : (ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize)).data = (#[] : Array UInt8) := by
    rw [zeroes_zero (n := ⟨↑(0:ℕ)⟩) (by rfl)]
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
  rw [show (ffi.ByteArray.zeroes { toBitVec := ↑len - ↑((src.write 0 base 0 len).extract 0 len).size }).data
      = (#[] : Array UInt8) from by
    rw [show { toBitVec := ↑len - ↑((src.write 0 base 0 len).extract 0 len).size } = (⟨↑(0:ℕ)⟩ : USize) from by
      rw [hextract_size]
      apply congrArg USize.ofBitVec
      exact BitVec.sub_self _]
    rw [zeroes_zero (n := ⟨↑(0:ℕ)⟩) (by rfl)]
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
  rw [show (ffi.ByteArray.zeroes { toBitVec := ↑len - ↑((src.write srcAddr base 0 len).extract 0 len).size }).data
      = (#[] : Array UInt8) from by
    rw [show { toBitVec := ↑len - ↑((src.write srcAddr base 0 len).extract 0 len).size }
        = (⟨↑(0:ℕ)⟩ : USize) from by
      rw [hextract_size]
      apply congrArg USize.ofBitVec
      exact BitVec.sub_self _]
    rw [zeroes_zero (n := ⟨↑(0:ℕ)⟩) (by rfl)]
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

/-- **Read below an end-append write.**  A 32-byte read that fits in the original `base` is
    unaffected by appending bytes at `base.size`. -/
theorem write_read_below_end_from (src base : ByteArray) (srcAddr len readAddr : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbelow : readAddr + 32 ≤ base.size) :
    (src.write srcAddr base base.size len).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  rw [write_end_eq_from src base srcAddr len hlen hsrc,
      readWithPadding_eq_extract _ readAddr
        (by rw [ByteArray.size_append]; omega),
      extract_append_left _ _ _ _ hbelow,
      ← readWithPadding_eq_extract _ readAddr hbelow]

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

/-! ## 5. `RETURN`/ABI encoding: `UInt256.toByteArray` as the big-endian word list -/

/-- **`toByteArray` is the 32-byte big-endian list.**  `UInt256.toByteArray v` (the EVM
    `MSTORE`/`RETURN` word, with the opaque `ffi.zeroes` leading pad) equals the *concrete*
    `EVM.Word.toBytesBE v` (`List.replicate`-padded), as `ByteArray`s.  The bridge between the
    opaque-memory and the pure-ABI worlds; the only opacity (`ffi.zeroes`) cancels. -/
theorem toByteArray_eq_toBytesBE (v : UInt256) :
    UInt256.toByteArray v = ⟨(EVM.Word.toBytesBE v).toArray⟩ := by
  have hb : (BE v.toNat).size ≤ 32 := by
    apply BE_le; have := v.val.isLt; simp [UInt256.size, UInt256.toNat]
  have h32 : 32 < USize.size := by
    rcases System.Platform.numBits_eq with h | h <;> rw [USize.size, h] <;> norm_num
  have h32' : (OfNat.ofNat 32 : USize).toNat = 32 :=
    USize.toNat_ofNat_of_le_of_lt (n := 32) (i := 32) h32 le_rfl
  have hbsize : (OfNat.ofNat (BE v.toNat).size : USize).toNat = (BE v.toNat).size :=
    USize.toNat_ofNat_of_le_of_lt (n := 32) (i := (BE v.toNat).size) h32 hb
  apply ByteArray.ext; apply Array.toList_inj.mp
  rw [show (((EVM.Word.toBytesBE v).toArray).toList) = EVM.Word.toBytesBE v from by simp]
  unfold UInt256.toByteArray EVM.Word.toBytesBE
  rw [ByteArray.data_append, Array.toList_append, byteArray_zeroes_toList,
      show ((BE v.toNat).data.toList) = toBytesBigEndian v.toNat from by simp [BE]]
  have hz : (⟨32 - (BE v.toNat).size⟩ : USize).toNat = 32 - (BE v.toNat).size := by
    rw [show (⟨32 - (BE v.toNat).size⟩ : USize)
          = (OfNat.ofNat 32 : USize) - (OfNat.ofNat (BE v.toNat).size : USize) from rfl,
        USize.toNat_sub_of_le]
    · rw [h32', hbsize]
    · rw [USize.le_iff_toNat_le, h32', hbsize]; exact hb
  rw [hz, show (BE v.toNat).size = (toBytesBigEndian v.toNat).length from by simp [BE]]
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

/-! ## 6. `CALLDATALOAD`/`SHR` selector extraction (reusable byte arithmetic) -/

/-- `fromBytes'` (little-endian) of an append splits at the byte boundary. -/
theorem fromBytes'_append (a b : List UInt8) :
    fromBytes' (a ++ b) = fromBytes' a + 2 ^ (8 * a.length) * fromBytes' b := by
  induction a with
  | nil => simp [fromBytes']
  | cons x xs ih =>
    simp only [List.cons_append, fromBytes', ih, List.length_cons]
    rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length from by ring, pow_add]; ring

/-- Big-endian division drops the low `|l2|` bytes. -/
theorem fromBytesBigEndian_append_div (l1 l2 : List UInt8) :
    fromBytesBigEndian (l1 ++ l2) / 2 ^ (8 * l2.length) = fromBytesBigEndian l1 := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, fromBytes'_append, List.length_reverse]
  have hlt : fromBytes' l2.reverse < 2 ^ (8 * l2.length) := by
    have := fromBytes'_le (bs := l2.reverse); rwa [List.length_reverse] at this
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

/-- The `ffi.zeroes` right-pad size of `readBytes _ _ 32` (`32 - read.size`), as a `Nat`. -/
theorem pad_toNat (m : ℕ) (hm : m ≤ 32) : (⟨↑32 - ↑m⟩ : USize).toNat = 32 - m := by
  have hb : m < 2 ^ 32 := lt_of_le_of_lt hm (by norm_num)
  show ((USize.ofNat 32) - (USize.ofNat m)).toNat = 32 - m
  rw [USize.toNat_sub_of_le,
      USize.toNat_ofNat_of_le_of_lt (n:=32) (i:=32) (lt_usize 32 (by norm_num)) le_rfl,
      USize.toNat_ofNat_of_le_of_lt (n:=32) (i:=m) (lt_usize 32 (by norm_num)) hm]
  rw [USize.le_iff_toNat_le, USize.toNat_ofNat_of_le_of_lt (n:=32) (i:=32) (lt_usize 32 (by norm_num)) le_rfl,
      USize.toNat_ofNat_of_le_of_lt (n:=32) (i:=m) (lt_usize 32 (by norm_num)) hm]; exact hm

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
  congr 2
  exact pad_toNat (min 32 cd.size) (min_le_left _ _)

theorem readBytes32_len (cd : ByteArray) :
    (ByteArray.readBytes cd 0 32).data.toList.length = 32 := by
  rw [readBytes32_toList, List.length_append, List.length_take, List.length_replicate]
  have : min 32 cd.data.toList.length = min 32 cd.size := by rw [Array.length_toList]; rfl
  omega

/-- **EVM selector extraction.**  `(uInt256OfByteArray (readBytes cd 0 32)) >>> 224` — the EVM's
    `CALLDATALOAD; PUSH 0xe0; SHR` — equals the big-endian number of `cd`'s first four bytes
    (for `4 ≤ cd.size`).  Fully proved; nothing opaque. -/
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

/-! ## Generic `MLOAD` word-value helper -/

/-- Simplify the value pushed by `MLOAD` when the 32-byte memory read is known. -/
theorem mloadWordValue_of_readWithPadding {mem : ByteArray} {aw off v : UInt256}
    (hmem : off.toNat < mem.size)
    (haw : ¬ off ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding off.toNat 32 = UInt256.toByteArray v) :
    (if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))) = v := by
  rw [if_neg (not_or.mpr ⟨by omega, haw⟩), hread, fromByteArrayBigEndian_toByteArray,
    u256_ofNat_toNat]

/-! ## ABI calldata decode coupling (shared by every contract with arguments) -/

/-- `uInt256OfByteArray` is the big-endian decode then `ofNat`. -/
theorem uInt256OfByteArray_eq (arr : ByteArray) :
    uInt256OfByteArray arr = UInt256.ofNat (fromByteArrayBigEndian arr) := by
  unfold uInt256OfByteArray fromByteArrayBigEndian fromBytesBigEndian
  rw [byteArray_toList_eq]; rfl

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
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hoff, by decide⟩),
      ByteArray.toList_data_append, hcl, byteArray_zeroes_toList, hcsize]
  simp

/-- The Solm decoder's word at byte offset `off` equals the EVM's `uInt256OfByteArray (readBytes off)`. -/
theorem decode_word_at_eq (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size) (hoff : off < 2 ^ 64) :
    ABI.bytesToWord ((cd.toList.drop off).take 32)
      = uInt256OfByteArray (cd.readBytes off 32) := by
  rw [uInt256OfByteArray_eq]
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 2
  rw [byteArray_toList_eq (cd.readBytes off 32), readBytes_at_toList _ _ hsz hoff]
  simp [byteArray_toList_eq]

/-! ## Mapping storage-slot and load coupling

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

/-- **Nested-mapping slot.**  For `mapping[k₁][k₂]` at base `baseSlot`: the inner slot is the
    single-mapping slot for `k₁`, and the outer `KECCAK256` over `k₂ ‖ innerSlot` yields the Solm
    layout slot — matching `uInt256OfByteArray (KEC (k₂ ‖ KEC(k₁ ‖ baseSlot)))`. -/
theorem mappingSlot_nested (k₁ k₂ baseSlot : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (k₂.toByteArray
          ++ (uInt256OfByteArray (ffi.KEC (k₁.toByteArray ++ baseSlot.toByteArray))).toByteArray)))
      = uInt256OfByteArray (ffi.KEC (k₂.toByteArray
          ++ (uInt256OfByteArray (ffi.KEC (k₁.toByteArray ++ baseSlot.toByteArray))).toByteArray)) :=
  keccakSlot_eq _

/-- **Load coupling.**  The word `RD.sload` pushes (storage of `codeOwner` at `slot`, read from the
    carried `accountMap`) is exactly the Solm-level `storageLoad` of the same account/slot — so a
    mapping `SLOAD` at the keccak slot reads the same word the Solm spec's `storageLocLoad` decodes. -/
theorem sloadVal_eq_storageLoad (self : EVM.State) (slot : UInt256) :
    (self.accountMap.find? self.executionEnv.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD slot ⟨0⟩))
      = Solm.EVM.storageLoad self self.executionEnv.codeOwner slot :=
  rfl


end Reasoning.Theory

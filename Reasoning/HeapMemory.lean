import Reasoning.Solc
import Reasoning.MemCascade

/-!
# Heap memory invariants

Free-memory cursors, allocated-prefix preservation, and bounded memory growth for symbolic
Solidity memory operations. The bounds are explicit hypotheses of the original helper lemmas.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

namespace Reasoning.Theory

set_option autoImplicit false

structure MemoryPrefix (before after : ByteArray) (limit : Nat) : Prop where
  size : before.size ≤ after.size
  read : ∀ off, 96 ≤ off → off + 32 ≤ limit → off + 32 ≤ before.size →
    after.readWithPadding off 32 = before.readWithPadding off 32

theorem MemoryPrefix.refl (mem : ByteArray) (limit : Nat) : MemoryPrefix mem mem limit :=
  ⟨le_refl _, fun _ _ _ _ => rfl⟩

theorem MemoryPrefix.trans {a b c : ByteArray} {limit : Nat}
    (hab : MemoryPrefix a b limit) (hbc : MemoryPrefix b c limit) :
    MemoryPrefix a c limit := by
  refine ⟨le_trans hab.size hbc.size, fun off hlo hhi hin => ?_⟩
  rw [hbc.read off hlo hhi (le_trans hin hab.size), hab.read off hlo hhi hin]

theorem MemoryPrefix.mono {a b : ByteArray} {lo hi : Nat}
    (h : MemoryPrefix a b hi) (hle : lo ≤ hi) : MemoryPrefix a b lo :=
  ⟨h.size, fun off hlo hhi hin => h.read off hlo (le_trans hhi hle) hin⟩

theorem memoryPrefix_writeWord (mem : ByteArray) (off limit : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size) (hdisj : limit ≤ off ∨ off + 32 ≤ 96) :
    MemoryPrefix mem (writeWord mem off word) limit := by
  refine ⟨?_, fun read hlo hhi hin => ?_⟩
  · rw [writeWord_size mem off word hgap]
    exact Nat.le_max_left _ _
  · apply writeWord_read_preserved mem off read word hgap
    rcases hdisj with hb | ha
    · exact Or.inl ⟨le_trans hhi hb, hin⟩
    · exact Or.inr ⟨le_trans ha hlo, hin⟩

def ActiveWords (aw : UInt256) : Prop := 3 ≤ aw.toNat ∧ aw.toNat ≤ 2 ^ 200

structure HeapMemory (mem : ByteArray) (aw ptr : UInt256) : Prop where
  size : 96 ≤ mem.size
  free : mem.readWithPadding 64 32 = ptr.toByteArray
  lower : 128 ≤ ptr.toNat
  gap : ptr.toNat ≤ mem.size + 32
  active : ActiveWords aw

theorem activeWords_mul32 {aw : UInt256} (h : ActiveWords aw) :
    (aw * ⟨32⟩).toNat = aw.toNat * 32 := by
  change (aw.toNat * 32) % UInt256.size = _
  apply Nat.mod_eq_of_lt
  have hb := h.2
  change aw.toNat * 32 < 2 ^ 256
  omega

theorem expandedWords32_toNat {aw off : UInt256} (ha : ActiveWords aw)
    (hoff : off.toNat + 32 ≤ 2 ^ 200) :
    (expandedWords aw off ⟨32⟩).toNat = max aw.toNat ((off.toNat + 63) / 32) := by
  change max aw.toNat ((off.toNat + 32 + 31) / 32) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (by
    have hb := ha.2
    change max aw.toNat ((off.toNat + 32 + 31) / 32) < 2 ^ 256
    omega)]

theorem activeWords_expand32 {aw off : UInt256} (ha : ActiveWords aw)
    (hoff : off.toNat + 32 ≤ 2 ^ 200) : ActiveWords (expandedWords aw off ⟨32⟩) := by
  unfold ActiveWords
  rw [expandedWords32_toNat ha hoff]
  have hlo := ha.1
  have hhi := ha.2
  constructor <;> omega

theorem expandedWords32_cover {aw off : UInt256} (ha : ActiveWords aw)
    (hoff : off.toNat + 32 ≤ 2 ^ 200) :
    off.toNat < (expandedWords aw off ⟨32⟩).toNat * 32 := by
  rw [expandedWords32_toNat ha hoff]
  omega

theorem expandedWords64_eq {aw : UInt256} (ha : ActiveWords aw) :
    expandedWords aw ⟨64⟩ ⟨32⟩ = aw := by
  apply u256_inj
  rw [expandedWords32_toNat ha (by decide)]
  have hlo := ha.1
  change max aw.toNat 3 = aw.toNat
  exact max_eq_left hlo

theorem HeapMemory.load64 {mem aw ptr} (h : HeapMemory mem aw ptr) :
    loadedWord mem ⟨64⟩ = ptr := by
  apply loadedWord_of_read
  · have h64 : (⟨64⟩ : UInt256).toNat = 64 := by u256_toNat
    rw [h64]
    exact le_trans (by norm_num) h.size
  · exact h.free

theorem HeapMemory.writeAbove {mem aw ptr} (h : HeapMemory mem aw ptr)
    (off word : UInt256) (hlo : ptr.toNat ≤ off.toNat)
    (hgap : off.toNat ≤ mem.size + 32) (hbound : off.toNat + 32 ≤ 2 ^ 200) :
    HeapMemory (writeWord mem off.toNat word) (expandedWords aw off ⟨32⟩) ptr := by
  have hg : off.toNat - mem.size < USize.size := by
    have h32 : 32 < USize.size := lt_usize 32 (by decide)
    omega
  have hs := writeWord_size mem off.toNat word hg
  refine ⟨by have hm := h.size; omega, ?_, h.lower, ?_,
    activeWords_expand32 h.active hbound⟩
  · rw [writeWord_read_preserved mem off.toNat 64 word hg (Or.inl
      ⟨by have hp := h.lower; omega, h.size⟩), h.free]
  · have hp := h.gap
    omega

theorem HeapMemory.setFree {mem aw ptr} (h : HeapMemory mem aw ptr) (next : UInt256)
    (hlo : 128 ≤ next.toNat) (hgap : next.toNat ≤ mem.size + 32) :
    HeapMemory (writeWord mem 64 next) aw next := by
  have hg : 64 - mem.size < USize.size := by
    have hm := h.size
    have hz : 0 < USize.size := lt_usize 0 (by decide)
    omega
  have hs := writeWord_size mem 64 next hg
  refine ⟨by have hm := h.size; omega, writeWord_read_back mem 64 next hg,
    hlo, ?_, h.active⟩
  omega

theorem freshHeapMemory : HeapMemory solcFreePtrMem ⟨3⟩ ⟨128⟩ := by
  exact ⟨by rw [solcFreePtrMem_size], solcFreePtrMem_read64, by decide,
    by rw [solcFreePtrMem_size]; decide, by constructor <;> decide⟩

theorem memoryPrefix_writeBytes (src mem : ByteArray) (off limit : Nat)
    (hpos : src.size ≠ 0) (hin : off ≤ mem.size) (hbelow : limit ≤ off) :
    MemoryPrefix mem (src.write 0 mem off src.size) limit := by
  refine ⟨?_, fun read _ hhi _ => ?_⟩
  · rw [writeBytes_size src mem off hpos hin]
    exact Nat.le_max_left _ _
  · exact write_read_below_gen_extend src mem off src.size read hpos (le_refl _) hin
      (le_trans hhi hbelow)

theorem activeWords_expand {aw off size : UInt256} (ha : ActiveWords aw)
    (hb : off.toNat + size.toNat ≤ 2 ^ 200) : ActiveWords (expandedWords aw off size) := by
  have hM : aw.toNat ≤ MachineState.M aw.toNat off.toNat size.toNat ∧
      MachineState.M aw.toNat off.toNat size.toNat ≤ 2 ^ 200 := by
    have hhi := ha.2
    unfold MachineState.M
    cases hs : size.toNat with
    | zero => exact ⟨le_refl _, hhi⟩
    | succ n => simp only [hs] at hb; split <;> omega
  have hv : (expandedWords aw off size).toNat =
      MachineState.M aw.toNat off.toNat size.toNat := by
    change _ % UInt256.size = _
    apply Nat.mod_eq_of_lt
    change _ < 2 ^ 256
    omega
  unfold ActiveWords
  rw [hv]
  exact ⟨le_trans ha.1 hM.1, hM.2⟩

def bytesAllocSize (size : Nat) : UInt256 :=
  UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.add (UInt256.ofNat size) ⟨63⟩)

def bytesAllocPtr (ptr : UInt256) (size : Nat) : UInt256 :=
  UInt256.add ptr (bytesAllocSize size)

theorem bytesAllocSize_toNat {size : Nat} (hb : size + 63 < UInt256.size) :
    (bytesAllocSize size).toNat = (size + 63) / 32 * 32 := by
  have hn : (UInt256.ofNat size).toNat = size := ulit_toNat' size (by omega)
  have ha := addWord_toNat (UInt256.ofNat size) ⟨63⟩ (by rw [hn]; exact hb)
  change (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 5)) _).toNat = _
  rw [u256_land_high_mask_toNat _ 5 (by decide), ha, hn]
  rfl

theorem bytesAllocPtr_toNat {ptr : UInt256} {size : Nat}
    (hb : ptr.toNat + size + 63 ≤ 2 ^ 200) :
    (bytesAllocPtr ptr size).toNat = ptr.toNat + (size + 63) / 32 * 32 := by
  have hs : size + 63 < UInt256.size := by change size + 63 < 2 ^ 256; omega
  unfold bytesAllocPtr
  rw [addWord_toNat ptr (bytesAllocSize size) (by
    rw [bytesAllocSize_toNat hs]
    change _ < 2 ^ 256
    omega), bytesAllocSize_toNat hs]

def bytesAllocMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  out.write 0
    (writeWord (writeWord mem 64 (bytesAllocPtr ptr out.size)) ptr.toNat
      (UInt256.ofNat out.size))
    (ptr.toNat + 32) out.size

def bytesAllocWords (aw ptr : UInt256) (size : Nat) : UInt256 :=
  expandedWords (expandedWords aw ptr ⟨32⟩) (UInt256.add ptr ⟨32⟩) (UInt256.ofNat size)

theorem bytesAlloc_heap {mem aw ptr} (h : HeapMemory mem aw ptr) (out : ByteArray)
    (hpos : out.size ≠ 0) (hb : ptr.toNat + out.size + 63 ≤ 2 ^ 200) :
    HeapMemory (bytesAllocMem mem out ptr) (bytesAllocWords aw ptr out.size)
      (bytesAllocPtr ptr out.size) := by
  have h64 : 64 - mem.size < USize.size := by
    have hm := h.size
    have hu := lt_usize 0 (by decide)
    omega
  have hs0 : (writeWord mem 64 (bytesAllocPtr ptr out.size)).size = mem.size := by
    rw [writeWord_size _ _ _ h64]
    have hm := h.size
    omega
  have hg : ptr.toNat - (writeWord mem 64 (bytesAllocPtr ptr out.size)).size < USize.size := by
    rw [hs0]
    have hp := h.gap
    have hu := lt_usize 32 (by decide)
    omega
  have hs1 := writeWord_size (writeWord mem 64 (bytesAllocPtr ptr out.size)) ptr.toNat
    (UInt256.ofNat out.size) hg
  have hs2 := writeBytes_size out
    (writeWord (writeWord mem 64 (bytesAllocPtr ptr out.size)) ptr.toNat
      (UInt256.ofNat out.size)) (ptr.toNat + 32) hpos (by omega)
  have hp := bytesAllocPtr_toNat hb
  have hn : (UInt256.ofNat out.size).toNat = out.size :=
    ulit_toNat' _ (by change out.size < 2 ^ 256; omega)
  have hadd : (UInt256.add ptr ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 96 ≤ (out.write 0 _ (ptr.toNat + 32) out.size).size
    have hm := h.size
    omega
  · unfold bytesAllocMem
    rw [write_read_below_gen_extend out _ (ptr.toNat + 32) out.size 64
      hpos (le_refl _) (by omega) (by have hlo := h.lower; omega)]
    rw [writeWord_read_preserved _ ptr.toNat 64 (UInt256.ofNat out.size) hg
      (Or.inl ⟨by have hlo := h.lower; omega, by rw [hs0]; exact h.size⟩),
      writeWord_read_back mem 64 (bytesAllocPtr ptr out.size) h64]
  · have hlo := h.lower
    omega
  · change (bytesAllocPtr ptr out.size).toNat ≤ (out.write 0 _ _ _).size + 32
    omega
  · apply activeWords_expand (activeWords_expand32 h.active (by omega))
    rw [hadd, hn]
    omega

theorem bytesAlloc_prefix {mem aw ptr} (h : HeapMemory mem aw ptr) (out : ByteArray)
    (hpos : out.size ≠ 0) : MemoryPrefix mem (bytesAllocMem mem out ptr) ptr.toNat := by
  have h64 : 64 - mem.size < USize.size := by
    have hm := h.size
    have hu := lt_usize 0 (by decide)
    omega
  have hs0 : (writeWord mem 64 (bytesAllocPtr ptr out.size)).size = mem.size := by
    rw [writeWord_size _ _ _ h64]
    have hm := h.size
    omega
  have hg : ptr.toNat - (writeWord mem 64 (bytesAllocPtr ptr out.size)).size < USize.size := by
    rw [hs0]
    have hp := h.gap
    have hu := lt_usize 32 (by decide)
    omega
  have hs1 := writeWord_size (writeWord mem 64 (bytesAllocPtr ptr out.size)) ptr.toNat
    (UInt256.ofNat out.size) hg
  exact (memoryPrefix_writeWord mem 64 ptr.toNat (bytesAllocPtr ptr out.size) h64
    (Or.inr (by decide))).trans
    ((memoryPrefix_writeWord _ ptr.toNat ptr.toNat (UInt256.ofNat out.size) hg
      (Or.inl (le_refl _))).trans
      (memoryPrefix_writeBytes out _ (ptr.toNat + 32) ptr.toNat hpos (by omega) (by omega)))

/-- The free cursor can reserve more space than has been copied into memory. -/
structure MemoryCursor (mem : ByteArray) (aw ptr : UInt256) : Prop where
  size : 96 ≤ mem.size
  free : mem.readWithPadding 64 32 = ptr.toByteArray
  lower : 128 ≤ ptr.toNat
  active : ActiveWords aw

theorem HeapMemory.cursor {mem aw ptr} (h : HeapMemory mem aw ptr) : MemoryCursor mem aw ptr :=
  ⟨h.size, h.free, h.lower, h.active⟩

theorem MemoryCursor.load64 {mem aw ptr} (h : MemoryCursor mem aw ptr) :
    loadedWord mem ⟨64⟩ = ptr :=
  loadedWord_of_read h.size h.free

theorem MemoryCursor.expand32 {mem aw ptr} (h : MemoryCursor mem aw ptr) (off : UInt256)
    (hb : off.toNat + 32 ≤ 2 ^ 200) : MemoryCursor mem (expandedWords aw off ⟨32⟩) ptr :=
  ⟨h.size, h.free, h.lower, activeWords_expand32 h.active hb⟩

def returnReserveSize (size : Nat) : UInt256 :=
  UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat size + ⟨31⟩)

def returnReservePtr (ptr : UInt256) (size : Nat) : UInt256 := ptr + returnReserveSize size

def returnReserveMem (mem : ByteArray) (ptr : UInt256) (size : Nat) : ByteArray :=
  writeWord mem 64 (returnReservePtr ptr size)

theorem returnReserveSize_toNat {size : Nat} (hb : size + 31 < UInt256.size) :
    (returnReserveSize size).toNat = (size + 31) / 32 * 32 := by
  have hn : (UInt256.ofNat size).toNat = size := ulit_toNat' size (by omega)
  have ha : (UInt256.ofNat size + ⟨31⟩).toNat = (UInt256.ofNat size).toNat + 31 :=
    addWord_toNat (UInt256.ofNat size) ⟨31⟩ (by rw [hn]; exact hb)
  change (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 5)) _).toNat = _
  rw [u256_land_high_mask_toNat _ 5 (by decide), ha, hn]
  rfl

theorem returnReservePtr_toNat {ptr : UInt256} {size : Nat}
    (hb : ptr.toNat + size + 31 ≤ 2 ^ 200) :
    (returnReservePtr ptr size).toNat = ptr.toNat + (size + 31) / 32 * 32 := by
  have hs : size + 31 < UInt256.size := by change size + 31 < 2 ^ 256; omega
  unfold returnReservePtr
  change (UInt256.add ptr (returnReserveSize size)).toNat = _
  rw [addWord_toNat ptr (returnReserveSize size) (by
    rw [returnReserveSize_toNat hs]
    change _ < 2 ^ 256
    omega), returnReserveSize_toNat hs]

theorem returnReserveMem_size {mem aw ptr} (h : MemoryCursor mem aw ptr) (size : Nat) :
    (returnReserveMem mem ptr size).size = mem.size := by
  unfold returnReserveMem
  rw [writeWord_size _ _ _ (by have hm := h.size; have hu := lt_usize 0 (by decide); omega)]
  have hm := h.size
  omega

theorem returnReserve_cursor {mem aw ptr} (h : MemoryCursor mem aw ptr) (size : Nat)
    (hb : ptr.toNat + size + 31 ≤ 2 ^ 200) :
    MemoryCursor (returnReserveMem mem ptr size) aw (returnReservePtr ptr size) := by
  refine ⟨?_, ?_, ?_, h.active⟩
  · rw [returnReserveMem_size h size]
    exact h.size
  · exact writeWord_read_back mem 64 (returnReservePtr ptr size)
      (by have hm := h.size; have hu := lt_usize 0 (by decide); omega)
  · rw [returnReservePtr_toNat hb]
    have hlo := h.lower
    omega

theorem returnReserve_prefix {mem aw ptr} (h : MemoryCursor mem aw ptr) (size : Nat) :
    MemoryPrefix mem (returnReserveMem mem ptr size) ptr.toNat :=
  memoryPrefix_writeWord mem 64 ptr.toNat (returnReservePtr ptr size)
    (by have hm := h.size; have hu := lt_usize 0 (by decide); omega) (Or.inr (by decide))

theorem returnReserve_read_word {mem aw ptr} (h : MemoryCursor mem aw ptr) (size : Nat)
    (hin : ptr.toNat + 32 ≤ mem.size) :
    (returnReserveMem mem ptr size).readWithPadding ptr.toNat 32 =
      mem.readWithPadding ptr.toNat 32 :=
  writeWord_read_preserved mem 64 ptr.toNat (returnReservePtr ptr size)
    (by have hm := h.size; have hu := lt_usize 0 (by decide); omega)
    (Or.inr ⟨by have hlo := h.lower; omega, hin⟩)

theorem writeWord_sparse_eq (mem : ByteArray) (off : Nat) (word : UInt256)
    (hoff : mem.size ≤ off) :
    writeWord mem off word = mem ++ ByteArray.zeroes (off - mem.size) ++ word.toByteArray := by
  have hsz : word.toByteArray.data.size = 32 := word.toByteArrayWithSizeProof.2
  have hpz : (ByteArray.zeroes (off - mem.size)).data.size = off - mem.size :=
    ByteArray_zeroes_size _
  apply ByteArray.ext
  unfold Reasoning.Theory.writeWord ByteArray.write
  rw [if_neg (by decide : ¬ ((32 : Nat) = 0)),
    if_neg (show ¬ (0 ≥ word.toByteArray.size) from by rw [toByteArray_size]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hdsz : (mem.data ++ (ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]
    change mem.size + (off - mem.size) = off
    omega
  rw [toByteArray_size, show min 32 (32 - 0) = 32 from rfl,
    show min mem.size (off + 32) - (off + 32) = 0 by omega,
    show (ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
      rw [zeroes_zero (n := 0) rfl]
      rfl, Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hdsz]),
    Array.extract_eq_self_of_le (show word.toByteArray.data.size ≤ 0 + (32 + 0) by rw [hsz]),
    Array.extract_eq_empty_of_le (by rw [hdsz]; omega), Array.append_empty]

theorem writeWord_sparse_size (mem : ByteArray) (off : Nat) (word : UInt256) :
    (writeWord mem off word).size = max mem.size (off + 32) := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_size mem off word (by have hu := lt_usize 0 (by decide); omega)
  · rw [writeWord_sparse_eq mem off word (by omega), ByteArray.size_append,
      ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    omega

theorem writeWord_sparse_read_preserved (mem : ByteArray) (off read : Nat) (word : UInt256)
    (hdisj : (read + 32 ≤ off ∧ read + 32 ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + 32 ≤ mem.size)) :
    (writeWord mem off word).readWithPadding read 32 = mem.readWithPadding read 32 := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_read_preserved mem off read word
      (by have hu := lt_usize 0 (by decide); omega) hdisj
  · have hread : read + 32 ≤ mem.size := hdisj.elim And.right And.right
    rw [writeWord_sparse_eq mem off word (by omega)]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega), extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract _ read hread).symm

theorem writeWord_sparse_read_window (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen : len < 2 ^ 64) :
    (writeWord mem off word).readWithPadding (off + start) len =
      word.toByteArray.extract start (start + len) := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_read_window mem off start len word hwithin hpos hlen
      (by have hu := lt_usize 0 (by decide); omega)
  · rw [writeWord_sparse_eq mem off word (by omega)]
    have hprefix : (mem ++ ByteArray.zeroes (off - mem.size)).size = off := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen (by
      rw [ByteArray.size_append, hprefix, toByteArray_size]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    congr 1 <;> omega

theorem writeWord_sparse_read_back (mem : ByteArray) (off : Nat) (word : UInt256) :
    (writeWord mem off word).readWithPadding off 32 = word.toByteArray := by
  have h := writeWord_sparse_read_window mem off 0 32 word (by decide) (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add,
    show word.toByteArray.extract 0 32 = word.toByteArray from by
      rw [← toByteArray_size word]
      exact byteArray_extract_self _] using h

theorem memoryPrefix_sparse_writeWord (mem : ByteArray) (off limit : Nat) (word : UInt256)
    (hdisj : limit ≤ off ∨ off + 32 ≤ 96) :
    MemoryPrefix mem (writeWord mem off word) limit := by
  refine ⟨by rw [writeWord_sparse_size]; exact Nat.le_max_left _ _, fun read hlo hhi hin ↦ ?_⟩
  apply writeWord_sparse_read_preserved
  rcases hdisj with hb | ha
  · exact Or.inl ⟨le_trans hhi hb, hin⟩
  · exact Or.inr ⟨le_trans ha hlo, hin⟩

theorem MemoryCursor.writeAbove {mem aw ptr} (h : MemoryCursor mem aw ptr)
    (off word : UInt256) (hlo : ptr.toNat ≤ off.toNat) (hb : off.toNat + 32 ≤ 2 ^ 200) :
    HeapMemory (writeWord mem off.toNat word) (expandedWords aw off ⟨32⟩) ptr := by
  have hs := writeWord_sparse_size mem off.toNat word
  refine ⟨by have hm := h.size; omega, ?_, h.lower, by omega,
    activeWords_expand32 h.active hb⟩
  rw [writeWord_sparse_read_preserved mem off.toNat 64 word
    (Or.inl ⟨by have hp := h.lower; omega, h.size⟩), h.free]

theorem callOutput32_size (mem out : ByteArray) (ptr : UInt256)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size) :
    (callOutputMem mem out ptr ⟨32⟩).size = mem.size := by
  unfold callOutputMem
  rw [callOutputLen32 hb]
  by_cases hz : min 32 out.size = 0
  · rw [hz, byteArray_write_len_zero]
  · rw [write_eq_gen out mem ptr.toNat (min 32 out.size) hz (Nat.min_le_right _ _)
      (by omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

theorem callOutput32_read_below (mem out : ByteArray) (ptr : UInt256) (off : Nat)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size)
    (hbelow : off + 32 ≤ ptr.toNat) :
    (callOutputMem mem out ptr ⟨32⟩).readWithPadding off 32 =
      mem.readWithPadding off 32 := by
  unfold callOutputMem
  rw [callOutputLen32 hb]
  by_cases hz : min 32 out.size = 0
  · rw [hz, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out mem ptr.toNat (min 32 out.size) off hz
      (Nat.min_le_right _ _) (by omega) hbelow

theorem callOutput32_prefix (mem out : ByteArray) (ptr : UInt256)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size) :
    MemoryPrefix mem (callOutputMem mem out ptr ⟨32⟩) ptr.toNat :=
  ⟨(callOutput32_size mem out ptr hb hin).ge,
    fun off _ hbelow _ => callOutput32_read_below mem out ptr off hb hin hbelow⟩

theorem callOutput32_heap {mem aw ptr} (h : HeapMemory mem aw ptr) (out : ByteArray)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size) :
    HeapMemory (callOutputMem mem out ptr ⟨32⟩) aw ptr := by
  have hs := callOutput32_size mem out ptr hb hin
  exact ⟨by rw [hs]; exact h.size,
    (callOutput32_read_below mem out ptr 64 hb hin (by have hp := h.lower; omega)).trans h.free,
    h.lower, by rw [hs]; exact h.gap, h.active⟩

theorem callOutput32_read_word (mem out : ByteArray) (ptr : UInt256)
    (hb : out.size < UInt256.size) (hs : 32 ≤ out.size) (hin : ptr.toNat ≤ mem.size) :
    (callOutputMem mem out ptr ⟨32⟩).readWithPadding ptr.toNat 32 =
      (calldataWord out 0).toByteArray := by
  unfold callOutputMem
  rw [callOutputLen32 hb, Nat.min_eq_left hs, write32_read_back out mem ptr.toNat hs hin,
    calldataWord_bytes hs]

theorem callActiveWords_toNat {aw inOff inSize outOff outSize : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200)
    (ho : outOff.toNat + outSize.toNat ≤ 2 ^ 200) :
    (callActiveWords aw inOff inSize outOff outSize).toNat =
      MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
        outOff.toNat outSize.toNat := by
  have hm1 := memoryWords_bounds aw.toNat inOff.toNat inSize.toNat ha.2 hi
  have hm2 := memoryWords_bounds (MachineState.M aw.toNat inOff.toNat inSize.toNat)
    outOff.toNat outSize.toNat hm1.2 ho
  apply ulit_toNat'
  change _ < 2 ^ 256
  omega

theorem callActiveWords_active {aw inOff inSize outOff outSize : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200)
    (ho : outOff.toNat + outSize.toNat ≤ 2 ^ 200) :
    ActiveWords (callActiveWords aw inOff inSize outOff outSize) := by
  have hm1 := memoryWords_bounds aw.toNat inOff.toNat inSize.toNat ha.2 hi
  have hm2 := memoryWords_bounds (MachineState.M aw.toNat inOff.toNat inSize.toNat)
    outOff.toNat outSize.toNat hm1.2 ho
  unfold ActiveWords
  rw [callActiveWords_toNat ha hi ho]
  exact ⟨le_trans (le_trans ha.1 hm1.1) hm2.1, hm2.2⟩

theorem callActiveWords_cover32 {aw inOff inSize outOff : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200) (ho : outOff.toNat + 32 ≤ 2 ^ 200) :
    outOff.toNat < (callActiveWords aw inOff inSize outOff ⟨32⟩).toNat * 32 := by
  rw [callActiveWords_toNat ha hi ho]
  change outOff.toNat < max _ ((outOff.toNat + 32 + 31) / 32) * 32
  omega

theorem expandedWords_mono {aw off size : UInt256} (ha : ActiveWords aw)
    (hb : off.toNat + size.toNat ≤ 2 ^ 200) : aw.toNat ≤ (expandedWords aw off size).toNat := by
  have hm := memoryWords_bounds aw.toNat off.toNat size.toNat ha.2 hb
  change aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat size.toNat)).toNat
  rw [ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
  exact hm.1

theorem callActiveWords_mono {aw inOff inSize outOff outSize : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200)
    (ho : outOff.toNat + outSize.toNat ≤ 2 ^ 200) :
    aw.toNat ≤ (callActiveWords aw inOff inSize outOff outSize).toNat := by
  have hm1 := memoryWords_bounds aw.toNat inOff.toNat inSize.toNat ha.2 hi
  have hm2 := memoryWords_bounds (MachineState.M aw.toNat inOff.toNat inSize.toNat)
    outOff.toNat outSize.toNat hm1.2 ho
  rw [callActiveWords_toNat ha hi ho]
  exact le_trans hm1.1 hm2.1

theorem expandedWords32_eq_of_cover {aw off : UInt256} (ha : ActiveWords aw)
    (hb : off.toNat + 32 ≤ 2 ^ 200) (hc : off.toNat + 32 ≤ aw.toNat * 32) :
    expandedWords aw off ⟨32⟩ = aw := by
  apply u256_inj
  rw [expandedWords32_toNat ha hb]
  exact max_eq_left (by omega)

theorem expandedWords32_chain {aw off1 off2 : UInt256} (ha : ActiveWords aw)
    (hle : off1.toNat ≤ off2.toNat) (hb : off2.toNat + 32 ≤ 2 ^ 200) :
    expandedWords (expandedWords aw off1 ⟨32⟩) off2 ⟨32⟩ = expandedWords aw off2 ⟨32⟩ := by
  apply u256_inj
  have hb1 : off1.toNat + 32 ≤ 2 ^ 200 := by omega
  rw [expandedWords32_toNat (activeWords_expand32 ha hb1) hb,
    expandedWords32_toNat ha hb1, expandedWords32_toNat ha hb]
  omega

theorem HeapMemory.expand32 {mem aw ptr} (hm : HeapMemory mem aw ptr) (off : UInt256)
    (hb : off.toNat + 32 ≤ 2 ^ 200) : HeapMemory mem (expandedWords aw off ⟨32⟩) ptr :=
  ⟨hm.size, hm.free, hm.lower, hm.gap, activeWords_expand32 hm.active hb⟩

theorem copyWindow_prefix (src mem : ByteArray) (srcOff dest len limit : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hdisj : limit ≤ dest ∨ dest + len ≤ 96) :
    MemoryPrefix mem (src.write srcOff mem dest len) limit := by
  refine ⟨?_, fun read hlo hhi hin ↦ ?_⟩
  · rw [copyWindow_size src mem srcOff dest len hpos hsrc hdest]
    exact Nat.le_max_left _ _
  · exact copyWindow_read_preserved src mem srcOff dest len read hpos hsrc hdest hin
      (hdisj.elim (fun hd ↦ Or.inl (by omega)) (fun hd ↦ Or.inr (by omega)))

def pairEventMem (mem : ByteArray) (ptr first second : UInt256) : ByteArray :=
  writeWord (writeWord mem ptr.toNat first) (ptr.toNat + 32) second

def pairEventWords (aw ptr : UInt256) : UInt256 :=
  expandedWords (expandedWords (expandedWords aw ptr ⟨32⟩) (ptr + ⟨32⟩) ⟨32⟩) ptr ⟨64⟩

theorem pairEventHeap {mem aw ptr first second} (hm : MemoryCursor mem aw ptr)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    HeapMemory (pairEventMem mem ptr first second) (pairEventWords aw ptr) ptr := by
  have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  have h1 := hm.writeAbove ptr first (le_refl _) (by omega)
  have h2 := h1.cursor.writeAbove (ptr + ⟨32⟩) second (by omega) (by omega)
  rw [hp] at h2
  exact ⟨h2.size, h2.free, h2.lower, h2.gap, activeWords_expand h2.active hb⟩

theorem pairEventPrefix (mem : ByteArray) (ptr first second : UInt256) :
    MemoryPrefix mem (pairEventMem mem ptr first second) ptr.toNat :=
  (memoryPrefix_sparse_writeWord mem ptr.toNat ptr.toNat first (Or.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ (ptr.toNat + 32) ptr.toNat second (Or.inl (by omega)))

theorem pairEventGrowth {aw ptr} (ha : ActiveWords aw) (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    aw.toNat ≤ (pairEventWords aw ptr).toNat := by
  have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  have hb32 : ptr.toNat + 32 ≤ 2 ^ 200 := by omega
  have hb2 : (ptr + ⟨32⟩).toNat + 32 ≤ 2 ^ 200 := by omega
  have ha1 := activeWords_expand32 ha hb32
  have ha2 := activeWords_expand32 ha1 hb2
  exact le_trans (le_trans (expandedWords_mono ha hb32) (expandedWords_mono ha1 hb2))
    (expandedWords_mono ha2 hb)

def errorOffset (out : ByteArray) : UInt256 := calldataWord out 4

def errorLength (out : ByteArray) : UInt256 := calldataWord out (4 + (errorOffset out).toNat)

def errorPayloadMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  out.write 4 mem ptr.toNat (out.size - 4)

def errorPayloadWords (aw ptr : UInt256) (out : ByteArray) : UInt256 :=
  expandedWords aw ptr (UInt256.ofNat (out.size - 4))

theorem expandedWords_cover {aw off size : UInt256} (ha : ActiveWords aw)
    (hb : off.toNat + size.toNat ≤ 2 ^ 200) (hz : size.toNat ≠ 0) :
    off.toNat + size.toNat ≤ (expandedWords aw off size).toNat * 32 := by
  have hm := memoryWords_bounds aw.toNat off.toNat size.toNat ha.2 hb
  have hn : (expandedWords aw off size).toNat =
      MachineState.M aw.toNat off.toNat size.toNat := by
    apply ulit_toNat'
    change _ < 2 ^ 256
    omega
  rw [hn]
  unfold MachineState.M
  cases hs : size.toNat with
  | zero => exact False.elim (hz hs)
  | succ n =>
    change off.toNat + (n + 1) ≤ max aw.toNat ((off.toNat + (n + 1) + 31) / 32) * 32
    omega

theorem errorPayload_size {mem aw ptr out} (_hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size) :
    (errorPayloadMem mem out ptr).size = max mem.size (ptr.toNat + out.size - 4) := by
  have hs := copyWindow_size out mem 4 ptr.toNat (out.size - 4) (by omega) (by omega) hin
  simpa only [errorPayloadMem, Nat.add_sub_assoc (show 4 ≤ out.size by omega)] using hs

theorem errorPayloadHeap {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) :
    HeapMemory (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) ptr := by
  have hn : (UInt256.ofNat (out.size - 4)).toNat = out.size - 4 :=
    ulit_toNat' _ (by change out.size - 4 < 2 ^ 256; omega)
  have hsz := errorPayload_size hm hin hl
  refine ⟨by have hs := hm.size; omega, ?_, hm.lower, by have hg := hm.gap; omega, ?_⟩
  · rw [errorPayloadMem, copyWindow_read_preserved out mem 4 ptr.toNat (out.size - 4) 64
      (by omega) (by omega) hin hm.size (Or.inl (by have hp := hm.lower; omega)), hm.free]
  · apply activeWords_expand hm.active
    rw [hn]
    omega

theorem errorPayloadCover {aw ptr out} (ha : ActiveWords aw) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) :
    ptr.toNat + out.size - 4 ≤ (errorPayloadWords aw ptr out).toNat * 32 := by
  have hn : (UInt256.ofNat (out.size - 4)).toNat = out.size - 4 :=
    ulit_toNat' _ (by change out.size - 4 < 2 ^ 256; omega)
  have hc := expandedWords_cover (off := ptr) (size := UInt256.ofNat (out.size - 4)) ha
    (by rw [hn]; omega) (by rw [hn]; omega)
  simpa only [errorPayloadWords, hn, Nat.add_sub_assoc (show 4 ≤ out.size by omega)] using hc

theorem errorPayload_load {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) (off : UInt256)
    (hoff : off.toNat + 36 ≤ out.size) :
    loadedWord (errorPayloadMem mem out ptr) (ptr + off) =
      calldataWord out (4 + off.toNat) := by
  have hp : (ptr + off).toNat = ptr.toNat + off.toNat :=
    addWord_toNat ptr off (by change ptr.toNat + off.toNat < 2 ^ 256; omega)
  have hsz := errorPayload_size hm hin hl
  have hc := errorPayloadCover hm.active hl hb
  have hh := errorPayloadHeap hm hin hl hb
  apply loadedWord_of_read (by omega)
  rw [hp, errorPayloadMem, copyWindow_read_word out mem 4 ptr.toNat (out.size - 4) off.toNat
      (by omega) (by omega) hin (by omega),
    readWithPadding_eq_extract _ _ (by omega), calldataWord_bytes_at (by omega)]

theorem errorPayload_expand {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) (off : UInt256)
    (hoff : off.toNat + 36 ≤ out.size) :
    expandedWords (errorPayloadWords aw ptr out) (ptr + off) ⟨32⟩ =
      errorPayloadWords aw ptr out := by
  have hp : (ptr + off).toNat = ptr.toNat + off.toNat :=
    addWord_toNat ptr off (by change ptr.toNat + off.toNat < 2 ^ 256; omega)
  have hc := errorPayloadCover hm.active hl hb
  have hh := errorPayloadHeap hm hin hl hb
  exact expandedWords32_eq_of_cover hh.active (by omega) (by omega)

theorem bytesAllocSize_eq_returnReserveSize {size : Nat} (hb : size + 63 < UInt256.size) :
    bytesAllocSize size = returnReserveSize (size + 32) := by
  apply u256_inj
  rw [bytesAllocSize_toNat hb, returnReserveSize_toNat (by omega)]

end Reasoning.Theory

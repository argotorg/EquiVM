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

/-! ## Dynamic payload layouts and prefix preservation -/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

def pairDynamicMem0 (mem : ByteArray) (ptr word0 : UInt256) : ByteArray :=
  word0.toByteArray.write 0 mem ptr.toNat 32

def pairDynamicMem (mem : ByteArray) (ptr word0 word1 : UInt256) : ByteArray :=
  word1.toByteArray.write 0 (pairDynamicMem0 mem ptr word0) (ptr + ⟨32⟩).toNat 32

abbrev pairDynamicWords0 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords aw ptr

abbrev pairDynamicWords (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩)

theorem pairDynamicMem_sizes {mem : ByteArray} (ptr word0 word1 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem0 mem ptr word0).size = max mem.size (ptr.toNat + 32) ∧
    (pairDynamicMem mem ptr word0 word1).size = max mem.size (ptr.toNat + 64) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs0 : (pairDynamicMem0 mem ptr word0).size = max mem.size (ptr.toNat + 32) :=
    writeWord_size mem ptr.toNat word0 hgap
  have hs1 :=
    toByteArray_write32_size_of_le (pairDynamicMem0 mem ptr word0) word1 (ptr + ⟨32⟩).toNat
    (max mem.size (ptr.toNat + 32)) (max mem.size (ptr.toNat + 64)) hs0
    (by rw [h32]; rw [hs0]; omega) (by rw [h32]; omega)
  exact ⟨hs0, hs1⟩

theorem pairDynamicMem_read_below {mem : ByteArray} (ptr word0 word1 : UInt256) (off : Nat)
    (hin : off + 32 ≤ mem.size) (hlo : off + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem mem ptr word0 word1).readWithPadding off 32 = mem.readWithPadding off 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  unfold pairDynamicMem pairDynamicMem0
  rw [h32]
  change (writeCascade mem [(ptr.toNat, word0), (ptr.toNat + 32, word1)]).readWithPadding off 32 = _
  apply writeCascade_read_preserved
  simp only [WindowDisjointFromWrites]
  refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

theorem pairDynamicWords_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 95 < UInt256.size) :
    (pairDynamicWords aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 64 ≤ (pairDynamicWords aw ptr).toNat * 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hb0 := UInt256_ofNat_M_mul32_lt aw ptr haw (by omega)
  have hb1 :=
    UInt256_ofNat_M_mul32_lt (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩) hb0 (by rw [h32]; omega)
  have hc1 :=
    UInt256_ofNat_M_covers (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩) hb0 (by rw [h32]; omega)
  refine ⟨hb1, ?_⟩
  change (ptr + ⟨32⟩).toNat + 32 ≤ (pairDynamicWords aw ptr).toNat * 32 at hc1
  rw [h32] at hc1
  omega

theorem pairDynamicMem_mload64 {mem : ByteArray} (aw ptr word0 word1 : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 95 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (pairDynamicMem mem ptr word0 word1) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (pairDynamicWords aw ptr) ⟨64⟩ = pairDynamicWords aw ptr := by
  obtain ⟨hb, hc⟩ := pairDynamicWords_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (pairDynamicWords aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [(pairDynamicMem_sizes ptr word0 word1 hgap (by omega)).2]; omega
  · exact (pairDynamicMem_read_below ptr word0 word1 64 hin hlo hgap (by omega)).trans hread

def quadDynamicMem (mem : ByteArray) (ptr word0 word1 word2 word3 : UInt256) : ByteArray :=
  pairDynamicMem (pairDynamicMem mem ptr word0 word1) (ptr + ⟨64⟩) word2 word3

abbrev quadDynamicWords (aw ptr : UInt256) : UInt256 :=
  pairDynamicWords (pairDynamicWords aw ptr) (ptr + ⟨64⟩)

theorem quadDynamicMem_size {mem : ByteArray} (ptr word0 word1 word2 word3 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 96 < UInt256.size) :
    (quadDynamicMem mem ptr word0 word1 word2 word3).size = max mem.size (ptr.toNat + 128) := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hs := (pairDynamicMem_sizes ptr word0 word1 hgap (by omega)).2
  have hg : (ptr + ⟨64⟩).toNat - (pairDynamicMem mem ptr word0 word1).size < USize.size := by
    rw [h64, hs, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by omega)
  rw [quadDynamicMem, (pairDynamicMem_sizes (ptr + ⟨64⟩) word2 word3 hg (by rw [h64]; omega)).2,
    h64, hs]
  omega

theorem quadDynamicMem_read_below {mem : ByteArray} (ptr word0 word1 word2 word3 : UInt256)
    (off : Nat)
    (hin : off + 32 ≤ mem.size) (hlo : off + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 96 < UInt256.size) :
    (quadDynamicMem mem ptr word0 word1 word2 word3).readWithPadding off 32 = mem.readWithPadding
      off 32 := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hs := (pairDynamicMem_sizes ptr word0 word1 hgap (by omega)).2
  have hg : (ptr + ⟨64⟩).toNat - (pairDynamicMem mem ptr word0 word1).size < USize.size := by
    rw [h64, hs, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by omega)
  unfold quadDynamicMem
  rw [pairDynamicMem_read_below (ptr + ⟨64⟩) word2 word3 off (by rw [hs]; omega)
    (by rw [h64]; omega) hg (by rw [h64]; omega)]
  exact pairDynamicMem_read_below ptr word0 word1 off hin hlo hgap (by omega)

theorem quadDynamicWords_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 159 < UInt256.size) :
    (quadDynamicWords aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 128 ≤ (quadDynamicWords aw ptr).toNat * 32 := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  obtain ⟨hb, _⟩ := pairDynamicWords_bounds aw ptr haw (by omega)
  obtain ⟨hb', hc'⟩ := pairDynamicWords_bounds (pairDynamicWords aw ptr) (ptr + ⟨64⟩) hb
    (by rw [h64]; omega)
  refine ⟨hb', ?_⟩
  change (ptr + ⟨64⟩).toNat + 64 ≤ (quadDynamicWords aw ptr).toNat * 32 at hc'
  rw [h64] at hc'
  omega

theorem quadDynamicMem_mload64 {mem : ByteArray} (aw ptr word0 word1 word2 word3 : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 159 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (quadDynamicMem mem ptr word0 word1 word2 word3) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (quadDynamicWords aw ptr) ⟨64⟩ = quadDynamicWords aw ptr := by
  obtain ⟨hb, hc⟩ := quadDynamicWords_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (quadDynamicWords aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [quadDynamicMem_size ptr word0 word1 word2 word3 hgap (by omega)]; omega
  · exact (quadDynamicMem_read_below ptr word0 word1 word2 word3 64 hin hlo hgap (by omega)).trans
      hread

theorem pairDynamicMem_read_ptr {mem : ByteArray} (ptr word0 word1 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem mem ptr word0 word1).readWithPadding ptr.toNat 64 = word0.toByteArray ++
      word1.toByteArray := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  obtain ⟨hs0, hs⟩ := pairDynamicMem_sizes ptr word0 word1 hgap hfit
  have hr0 : (pairDynamicMem mem ptr word0 word1).readWithPadding ptr.toNat 32 = word0.toByteArray
    := by
    unfold pairDynamicMem
    rw [write32_read_below _ _ (ptr + ⟨32⟩).toNat ptr.toNat (by rw [toByteArray_size])
      (by rw [h32, hs0]; omega) (by rw [h32])]
    exact writeWord_read_back mem ptr.toNat word0 hgap
  have hoff32 : (ptr + ⟨32⟩).toNat ≤ (pairDynamicMem0 mem ptr word0).size := by rw [h32, hs0]; omega
  have hr1 :=
    toByteArray_write32_read_back (pairDynamicMem0 mem ptr word0) word1 (ptr + ⟨32⟩).toNat hoff32
  change (pairDynamicMem mem ptr word0 word1).readWithPadding (ptr + ⟨32⟩).toNat 32 =
    word1.toByteArray at hr1
  rw [h32] at hr1
  rw [byteArray_readWithPadding_split _ ptr.toNat 32 32 (by decide) (by decide) (by decide)
    (by decide)
    (by decide) (by rw [hs]; omega), hr0, hr1]

theorem byteArray_write_prefix32 (src base : ByteArray) (dest : Nat)
    (hsrc : 32 ≤ src.size) (hdest : dest ≤ base.size) :
    (src.write 0 base dest src.size).readWithPadding dest 32 = src.extract 0 32 := by
  have hne : src.size ≠ 0 := by omega
  have hprefix : (base.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  by_cases hin : dest + src.size ≤ base.size
  · rw [write_eq_gen src base dest src.size hne le_rfl hin]
    rw [readWithPadding_eq_extract _ dest (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ dest (dest + 32) (by
      rw [ByteArray.size_append, hprefix, ByteArray.size_extract]
      omega)]
    rw [extract_append_right_window _ _ dest (dest + 32) (by rw [hprefix])]
    rw [hprefix, Nat.sub_self, Nat.add_sub_cancel_left, extract_extract_BA]
    simp only [Nat.zero_add, Nat.min_eq_left hsrc]
  · rw [write_eq_gen_extend src base dest src.size hne le_rfl hdest (by omega)]
    rw [readWithPadding_eq_extract _ dest (by
      rw [ByteArray.size_append, hprefix, ByteArray.size_extract]
      omega)]
    rw [extract_append_right_window _ _ dest (dest + 32) (by rw [hprefix])]
    rw [hprefix, Nat.sub_self, Nat.add_sub_cancel_left, extract_extract_BA]
    simp only [Nat.zero_add, Nat.min_eq_left hsrc]

theorem byteArray_write_all_size (src base : ByteArray) (dest : Nat) (hdest : dest ≤ base.size) :
    (src.write 0 base dest src.size).size = max base.size (dest + src.size) := by
  by_cases hz : src.size = 0
  · rw [hz, byteArray_write_len_zero, Nat.add_zero, Nat.max_eq_left hdest]
  · by_cases hin : dest + src.size ≤ base.size
    · rw [write_eq_gen src base dest src.size hz le_rfl hin,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · rw [write_eq_gen_extend src base dest src.size hz le_rfl hdest (by omega),
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

def solcReturnDataPtrMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toByteArray.write 0 mem
    64 32

def solcReturnDataSizeMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.ofNat out.size).toByteArray.write 0 (solcReturnDataPtrMem mem ptr out) ptr.toNat 32

def solcReturnDataMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat out.size

abbrev solcReturnDataActiveWords (aw ptr : UInt256) (out : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)

theorem solcReturnDataPtrMem_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) : (solcReturnDataPtrMem mem ptr out).size = mem.size := by
  have h := toByteArray_write32_size_of_le mem
    (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)) 64 mem.size mem.size
    rfl (by omega) (by omega)
  exact h

theorem solcReturnDataSizeMem_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) :
    (solcReturnDataSizeMem mem ptr out).size = mem.size := by
  have hs := solcReturnDataPtrMem_size ptr out hin
  have h :=
    toByteArray_write32_size_of_le (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
    ptr.toNat mem.size mem.size hs (by rw [hs]; omega) (by omega)
  exact h

theorem solcReturnDataMem_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
      :
    (solcReturnDataMem mem ptr out).size = max mem.size (ptr.toNat + 32 + out.size) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have h := byteArray_write_all_size out (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat
    (by rw [h32, hs]; omega)
  change (solcReturnDataMem mem ptr out).size = _ at h
  rw [h32, hs] at h
  exact h

theorem solcReturnDataMem_read_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
      :
    (solcReturnDataMem mem ptr out).readWithPadding ptr.toNat 32 =
      (UInt256.ofNat out.size).toByteArray := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have hsPtr := solcReturnDataPtrMem_size ptr out hin
  unfold solcReturnDataMem
  by_cases hz : out.size = 0
  · rw [hz, byteArray_write_len_zero]
    unfold solcReturnDataSizeMem
    have h :=
      toByteArray_write32_read_back (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
      ptr.toNat (by rw [hsPtr]; omega)
    exact h.trans (congrArg (fun n => (UInt256.ofNat n).toByteArray) hz)
  · rw [write_read_below_gen_extend out _ (ptr + ⟨32⟩).toNat out.size ptr.toNat hz le_rfl
      (by rw [h32, hs]; omega) (by rw [h32])]
    unfold solcReturnDataSizeMem
    have h :=
      toByteArray_write32_read_back (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
      ptr.toNat (by rw [hsPtr]; omega)
    exact h

theorem solcReturnDataMem_read_word {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hout : 32 ≤ out.size) :
    (solcReturnDataMem mem ptr out).readWithPadding (ptr + ⟨32⟩).toNat 32 = out.extract 0 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have h :=
    byteArray_write_prefix32 out (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat hout
      (by rw [h32, hs]; omega)
  exact h

theorem solcReturnDataActiveWords_bounds (aw ptr : UInt256) (out : ByteArray)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size) :
    (solcReturnDataActiveWords aw ptr out).toNat * 32 < UInt256.size ∧
      aw.toNat ≤ (solcReturnDataActiveWords aw ptr out).toNat := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hM :=
    MachineState_M_mul32_lt_of_bounds haw
      (show (ptr + ⟨32⟩).toNat + out.size + 31 < UInt256.size by rw [h32]; omega)
  have hMlt : MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size < UInt256.size := by omega
  change (UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)).toNat * 32 <
    UInt256.size ∧
    aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)).toNat
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact ⟨hM, MachineState_M_ge_left _ _ _⟩

theorem solcReturnDataMem_mload_size {mem : ByteArray} (aw ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size) :
    memoryWordLoad (solcReturnDataMem mem ptr out) ptr = UInt256.ofNat out.size ∧
    memoryWordActiveWords (solcReturnDataActiveWords aw ptr out) ptr = solcReturnDataActiveWords aw
      ptr out := by
  obtain ⟨hb, hge⟩ := solcReturnDataActiveWords_bounds aw ptr out haw hfit
  have hc : ptr.toNat + 32 ≤ (solcReturnDataActiveWords aw ptr out).toNat * 32 := by omega
  constructor
  · apply mloadWordValue_of_readWithPadding
    · rw [solcReturnDataMem_size ptr out hin hptr (by omega)]
      omega
    · exact solcReturnDataMem_read_size ptr out hin hptr (by omega)
  · exact UInt256_M_same_of_cover _ _ hb hc

theorem solcReturnDataMem_mload_word {mem : ByteArray} (aw ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size)
    (hout : 32 ≤ out.size) :
    memoryWordLoad (solcReturnDataMem mem ptr out) (ptr + ⟨32⟩) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ∧
    memoryWordActiveWords (solcReturnDataActiveWords aw ptr out) (ptr + ⟨32⟩) =
      solcReturnDataActiveWords aw ptr out := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  obtain ⟨hb, hge⟩ := solcReturnDataActiveWords_bounds aw ptr out haw hfit
  have hc : (ptr + ⟨32⟩).toNat + 32 ≤ (solcReturnDataActiveWords aw ptr out).toNat * 32 := by
    rw [h32]; omega
  constructor
  · have hm := mloadValue_eq_readWithPadding_of_lt_size (solcReturnDataMem mem ptr out)
      (ptr + ⟨32⟩) _
      (solcReturnDataMem_size ptr out hin hptr (by omega)) (by rw [h32]; omega)
    exact hm.trans (congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes))
      (solcReturnDataMem_read_word ptr out hin hptr (by omega) hout))
  · exact UInt256_M_same_of_cover _ _ hb hc

theorem solcReturnDataRounded_toNat (size : Nat) (hfit : size + 63 < UInt256.size) :
    (UInt256.land (UInt256.ofNat size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toNat = (size + 63) / 32 * 32 :=
      by
  rw [u256_land_comm]
  rw [show UInt256.lnot ⟨31⟩ = UInt256.ofNat (2 ^ 256 - 2 ^ 5) by decide,
    u256_land_high_mask_toNat _ 5 (by omega)]
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega)]
  change ((size + 63) % UInt256.size) / 32 * 32 = (size + 63) / 32 * 32
  rw [Nat.mod_eq_of_lt hfit]

theorem solcReturnDataMem_read_below_ptr {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (read : Nat)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hread : read + 32 ≤ ptr.toNat) :
    (solcReturnDataMem mem ptr out).readWithPadding read 32 =
      (solcReturnDataPtrMem mem ptr out).readWithPadding read 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hsSize := solcReturnDataSizeMem_size ptr out hin hptr
  have hsPtr := solcReturnDataPtrMem_size ptr out hin
  have hcopy : (solcReturnDataMem mem ptr out).readWithPadding read 32 =
      (solcReturnDataSizeMem mem ptr out).readWithPadding read 32 := by
    unfold solcReturnDataMem
    by_cases hz : out.size = 0
    · rw [hz, byteArray_write_len_zero]
    · have h := write_read_below_gen_extend out (solcReturnDataSizeMem mem ptr out)
        (ptr + ⟨32⟩).toNat out.size read hz le_rfl
        (by rw [h32, hsSize]; omega) (by rw [h32]; omega)
      exact h
  rw [hcopy]
  unfold solcReturnDataSizeMem
  exact write32_read_below _ _ ptr.toNat read (by rw [toByteArray_size]) (by rw [hsPtr]; omega)
    hread

theorem solcReturnDataMem_read64 {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hptrLo : 96 ≤ ptr.toNat) :
    (solcReturnDataMem mem ptr out).readWithPadding 64 32 =
      (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toByteArray := by
  rw [solcReturnDataMem_read_below_ptr ptr out 64 hin hptr hfit hptrLo]
  unfold solcReturnDataPtrMem
  have h := toByteArray_write32_read_back mem
    (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)) 64 (by omega)
  exact h

theorem solcReturnDataMem_read96 {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hptrLo : 128 ≤ ptr.toNat) :
    (solcReturnDataMem mem ptr out).readWithPadding 96 32 = mem.readWithPadding 96 32 := by
  rw [solcReturnDataMem_read_below_ptr ptr out 96 hin hptr hfit hptrLo]
  unfold solcReturnDataPtrMem
  exact write32_read_above _ _ 64 96 (by rw [toByteArray_size]) (by omega) (by omega) (by omega)

def solcErrorDynamicMem0 (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  solcErrorStringSelector.toByteArray.write 0 mem ptr.toNat 32

def solcErrorDynamicMem1 (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray.write 0 (solcErrorDynamicMem0 mem ptr) (ptr + ⟨4⟩).toNat 32

def solcErrorDynamicMem2 (mem : ByteArray) (ptr len : UInt256) : ByteArray :=
  len.toByteArray.write 0 (solcErrorDynamicMem1 mem ptr) (ptr + ⟨36⟩).toNat 32

def solcErrorDynamicMem3 (mem : ByteArray) (ptr len word : UInt256) : ByteArray :=
  word.toByteArray.write 0 (solcErrorDynamicMem2 mem ptr len) (ptr + ⟨68⟩).toNat 32

abbrev solcErrorDynamicWords0 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords aw ptr

abbrev solcErrorDynamicWords1 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (solcErrorDynamicWords0 aw ptr) (ptr + ⟨4⟩)

abbrev solcErrorDynamicWords2 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (solcErrorDynamicWords1 aw ptr) (ptr + ⟨36⟩)

abbrev solcErrorDynamicWords3 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩)

theorem solcErrorDynamicMem_sizes {mem : ByteArray} (ptr len word : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 68 < UInt256.size) :
    (solcErrorDynamicMem0 mem ptr).size = max mem.size (ptr.toNat + 32) ∧
    (solcErrorDynamicMem1 mem ptr).size = max mem.size (ptr.toNat + 36) ∧
    (solcErrorDynamicMem2 mem ptr len).size = max mem.size (ptr.toNat + 68) ∧
    (solcErrorDynamicMem3 mem ptr len word).size = max mem.size (ptr.toNat + 100) := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 hfit
  have hs0 : (solcErrorDynamicMem0 mem ptr).size = max mem.size (ptr.toNat + 32) :=
    writeWord_size mem ptr.toNat solcErrorStringSelector hgap
  have hs1 := toByteArray_write32_size_of_le (solcErrorDynamicMem0 mem ptr) ⟨32⟩ (ptr + ⟨4⟩).toNat
    (max mem.size (ptr.toNat + 32)) (max mem.size (ptr.toNat + 36)) hs0
      (by rw [h4]; rw [hs0]; omega) (by rw [h4]; omega)
  change (solcErrorDynamicMem1 mem ptr).size = max mem.size (ptr.toNat + 36) at hs1
  have hs2 := toByteArray_write32_size_of_le (solcErrorDynamicMem1 mem ptr) len (ptr + ⟨36⟩).toNat
    (max mem.size (ptr.toNat + 36)) (max mem.size (ptr.toNat + 68)) hs1
      (by rw [h36]; rw [hs1]; omega) (by rw [h36]; omega)
  change (solcErrorDynamicMem2 mem ptr len).size = max mem.size (ptr.toNat + 68) at hs2
  have hs3 :=
    toByteArray_write32_size_of_le (solcErrorDynamicMem2 mem ptr len) word (ptr + ⟨68⟩).toNat
    (max mem.size (ptr.toNat + 68)) (max mem.size (ptr.toNat + 100)) hs2
      (by rw [h68]; rw [hs2]; omega) (by rw [h68]; omega)
  exact ⟨hs0, hs1, hs2, hs3⟩

theorem solcErrorDynamicMem3_read64 {mem : ByteArray} (ptr len word : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 68 < UInt256.size) :
    (solcErrorDynamicMem3 mem ptr len word).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 hfit
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  unfold solcErrorDynamicMem3 solcErrorDynamicMem2 solcErrorDynamicMem1 solcErrorDynamicMem0
  rw [h4, h36, h68]
  change (writeCascade mem [(ptr.toNat, solcErrorStringSelector), (ptr.toNat + 4, ⟨32⟩),
    (ptr.toNat + 36, len), (ptr.toNat + 68, word)]).readWithPadding 64 32 = _
  apply writeCascade_read_preserved
  simp only [WindowDisjointFromWrites]
  refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
    ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

theorem solcErrorDynamicWords3_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 131 < UInt256.size) :
    (solcErrorDynamicWords3 aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 100 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 (by omega)
  have hb0 := UInt256_ofNat_M_mul32_lt aw ptr haw (by omega)
  have hb1 :=
    UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords0 aw ptr) (ptr + ⟨4⟩) hb0 (by rw [h4]; omega)
  have hb2 :=
    UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords1 aw ptr) (ptr + ⟨36⟩) hb1 (by rw [h36]; omega)
  have hb3 :=
    UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩) hb2 (by rw [h68]; omega)
  have hc3 :=
    UInt256_ofNat_M_covers (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩) hb2 (by rw [h68]; omega)
  refine ⟨hb3, ?_⟩
  change (ptr + ⟨68⟩).toNat + 32 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 at hc3
  rw [h68] at hc3
  omega

theorem solcErrorDynamicMem3_mload64 {mem : ByteArray} (aw ptr len word : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (solcErrorDynamicMem3 mem ptr len word) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (solcErrorDynamicWords3 aw ptr) ⟨64⟩ = solcErrorDynamicWords3 aw ptr := by
  obtain ⟨hb, hc⟩ := solcErrorDynamicWords3_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [(solcErrorDynamicMem_sizes ptr len word hgap (by omega)).2.2.2]; omega
  · exact (solcErrorDynamicMem3_read64 ptr len word hin hlo hgap (by omega)).trans hread

def wordBytes : List UInt256 → ByteArray
  | [] => ByteArray.empty
  | w :: ws => UInt256.toByteArray w ++ wordBytes ws

theorem wordBytes_size (ws : List UInt256) : (wordBytes ws).size = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [wordBytes, ByteArray.size_append, toByteArray_size,
      ih, List.length_cons]; omega

theorem wordBytes_append (xs ys : List UInt256) :
    wordBytes (xs ++ ys) = wordBytes xs ++ wordBytes ys := by
  induction xs with
  | nil => simp [wordBytes]
  | cons w ws ih => simp only [List.cons_append, wordBytes, ih, ByteArray.append_assoc]

theorem wordBytes_eq_list (ws : List UInt256) :
    wordBytes ws = (ws.flatMap EVM.Word.toBytesBE).toByteArray := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordBytes, List.flatMap_cons, list_toByteArray_append,
      word_toBytesBE_toByteArray_eq_toByteArray, ih]

def returnMem (ws : List UInt256) : ByteArray :=
  (solcFreePtrMem ++ ByteArray.zeroes 32) ++ wordBytes ws

theorem returnMem_size (ws : List UInt256) : (returnMem ws).size = 128 + 32 * ws.length := by
  rw [returnMem, ByteArray.size_append, solcFreePtrMem_pad_size, wordBytes_size]

theorem returnMem_single (w : UInt256) : solcReturnMem w = returnMem [w] := by
  simpa only [returnMem, wordBytes, ByteArray.append_empty] using solcReturnMem_eq w

theorem returnMem_write (ws : List UInt256) (w : UInt256) :
    (UInt256.toByteArray w).write 0 (returnMem ws) (128 + 32 * ws.length) 32 =
      returnMem (ws ++ [w]) := by
  rw [← returnMem_size ws, write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size]),
    toByteArray_extract_all]
  simp only [returnMem, wordBytes_append, wordBytes, ByteArray.append_empty,
    ByteArray.append_assoc]

theorem returnMem_read64 (ws : List UInt256) :
    (returnMem ws).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by rw [returnMem_size]; omega), returnMem,
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_pad_size]; omega),
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size]),
    ← readWithPadding_eq_extract _ _ (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem returnMem_read128 (ws : List UInt256) (hpos : 0 < ws.length)
    (hsize : 32 * ws.length < 2 ^ 64) :
    (returnMem ws).readWithPadding 128 (32 * ws.length) = wordBytes ws := by
  rw [readWithPadding_eq_extract' _ _ _ (by omega) hsize (by rw [returnMem_size])]
  exact extract_append_right' _ _ _ _ (by rw [solcFreePtrMem_pad_size])
    (by rw [solcFreePtrMem_pad_size, wordBytes_size])

def errorStringMem4 (len first second : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray second).write 0 (solcErrorStringMem3 len first mem) 228 32

theorem errorStringMem4_size (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) : (errorStringMem4 len first second mem).size = 260 := by
  exact toByteArray_write32_size_of_ge _ second 228 228 260
    (solcErrorStringMem3_size len first hmem) (by decide)
    (lt_usize _ (by norm_num)) (by decide)

theorem errorStringMem4_read64 (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (errorStringMem4 len first second mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold errorStringMem4
  rw [toByteArray_write_read_below_of_gap second _ 228 64
    (by rw [solcErrorStringMem3_size len first hmem]; decide) (by decide)
    (by rw [solcErrorStringMem3_size len first hmem]; exact lt_usize _ (by norm_num))]
  exact solcErrorStringMem3_read64 len first hmem hread

theorem errorStringMem4_mload64 (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (errorStringMem4 len first second mem).size then ⟨0⟩ else
      UInt256.ofNat (fromByteArrayBigEndian
        ((errorStringMem4 len first second mem).readWithPadding 64 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [errorStringMem4_size len first second hmem]; decide)
    (errorStringMem4_read64 len first second hmem hread)

theorem memoryPrefix_sparse_cascade (mem : ByteArray) (writes : List (Nat × UInt256)) (limit : Nat)
    (hdisj : ∀ write ∈ writes, limit ≤ write.1 ∨ write.1 + 32 ≤ 96) :
    MemoryPrefix mem (writeCascade mem writes) limit := by
  induction writes generalizing mem with
  | nil => exact .refl _ _
  | cons w ws ih =>
    exact (memoryPrefix_sparse_writeWord mem w.1 limit w.2 (hdisj w (by simp))).trans
      (ih _ (fun w hw ↦ hdisj w (List.mem_cons_of_mem _ hw)))

theorem returnReserve_load {mem aw ptr word} (hm : MemoryCursor mem aw ptr) (size : Nat)
    (hin : ptr.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding ptr.toNat 32 = word.toByteArray) :
    loadedWord (returnReserveMem mem ptr size) ptr = word := by
  apply loadedWord_of_read (by rw [returnReserveMem_size hm size]; exact hin)
  rw [returnReserve_read_word hm size hin, hread]

end Reasoning.Theory

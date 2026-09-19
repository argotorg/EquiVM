import Solm.Benchmarks.Auction.BytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- The free cursor can reserve more space than has been copied into memory. -/
structure MemoryCursor (mem : ByteArray) (aw ptr : UInt256) : Prop where
  size : 96 ≤ mem.size
  free : mem.readWithPadding 64 32 = ptr.toByteArray
  lower : 128 ≤ ptr.toNat
  active : ActiveWords aw

theorem HeapMemory.cursor {mem aw ptr} (h : HeapMemory mem aw ptr) : MemoryCursor mem aw ptr :=
  ⟨h.size, h.free, h.lower, h.active⟩

theorem MemoryCursor.load64 {mem aw ptr} (h : MemoryCursor mem aw ptr) :
    loadedWord mem aw ⟨64⟩ = ptr :=
  loadedWord_of_read h.active h.size (by have hlo := h.active.1; change 64 < _; omega) h.free

theorem MemoryCursor.expand32 {mem aw ptr} (h : MemoryCursor mem aw ptr) (off : UInt256)
    (hb : off.toNat + 32 ≤ 2 ^ 200) : MemoryCursor mem (expandedWords aw off ⟨32⟩) ptr :=
  ⟨h.size, h.free, h.lower, activeWords_expand32 h.active hb⟩

def returnReserveSize (size : Nat) : UInt256 :=
  UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat size + ⟨31⟩)

def returnReservePtr (ptr : UInt256) (size : Nat) : UInt256 := ptr + returnReserveSize size

noncomputable def returnReserveMem (mem : ByteArray) (ptr : UInt256) (size : Nat) : ByteArray :=
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

end Auction

import Solm.Benchmarks.Auction.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: copying a complete byte array inside, or across the end of, memory.
theorem writeBytes_size (src mem : ByteArray) (off : Nat)
    (hpos : src.size ≠ 0) (hin : off ≤ mem.size) :
    (src.write 0 mem off src.size).size = max mem.size (off + src.size) := by
  by_cases he : off + src.size ≤ mem.size
  · rw [write_eq_gen src mem off src.size hpos (le_refl _) he]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  · rw [write_eq_gen_extend src mem off src.size hpos (le_refl _) hin (by omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

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

noncomputable def bytesAllocMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
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

end Auction

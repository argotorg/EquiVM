import Benchmarks.Auction.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem encodeEmptyBytes {I g s0 dest src ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨6093⟩ (dest :: src :: ret :: R)
      mem aw rdata acc k C)
    (hzero : loadedWord mem aw src = ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (dest :: R)
      (writeWord mem dest.toNat ⟨0⟩)
      (expandedWords (expandedWords aw src ⟨32⟩) dest ⟨32⟩) rdata acc k' C' := by
  have rd6097 := evm_run h with [jumpdest, push0, dup3,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hzero] at rd6097
  have rd6126 := evm_run rd6097 with [push0, jumpdest, dup2, dup2, lt, iszero,
    push2 ⟨6124⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, push0, swap3, add]
  rw [u256_add_comm dest ⟨0⟩, u256_zero_add] at rd6126
  have rd6132 := evm_run rd6126 with [swap2, dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov), pop, swap2, swap1, pop]
  exact ⟨_, _, evm_run rd6132 with [jump hret]⟩

def nextEmptyPtr (ptr : UInt256) : UInt256 := UInt256.add ptr ⟨32⟩

noncomputable def emptyHeaderMem (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord mem ptr.toNat ⟨0⟩) 64 (nextEmptyPtr ptr)

def emptyHeaderWords (aw ptr : UInt256) : UInt256 := expandedWords aw ptr ⟨32⟩

theorem nextEmptyPtr_toNat {ptr : UInt256} (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    (nextEmptyPtr ptr).toNat = ptr.toNat + 32 := by
  apply addWord_toNat
  change ptr.toNat + 32 < 2 ^ 256
  omega

theorem emptyHeader_heap {mem aw ptr} (h : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    HeapMemory (emptyHeaderMem mem ptr) (emptyHeaderWords aw ptr) (nextEmptyPtr ptr) := by
  have h1 := h.writeAbove ptr ⟨0⟩ (le_refl _) h.gap (by omega)
  have hptr := nextEmptyPtr_toNat hb
  have hg : ptr.toNat - mem.size < USize.size := by
    have hu := lt_usize 32 (by decide)
    have hp := h.gap
    omega
  have hs := writeWord_size mem ptr.toNat ⟨0⟩ hg
  exact h1.setFree (nextEmptyPtr ptr) (by have hlo := h.lower; omega) (by omega)

theorem emptyHeader_zero {mem aw ptr} (h : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    loadedWord (emptyHeaderMem mem ptr) (emptyHeaderWords aw ptr) ptr = ⟨0⟩ := by
  have hg : ptr.toNat - mem.size < USize.size := by
    have hu := lt_usize 32 (by decide)
    have hp := h.gap
    omega
  have hs := writeWord_size mem ptr.toNat ⟨0⟩ hg
  have hh := emptyHeader_heap h hb
  have hs' := writeWord_size (writeWord mem ptr.toNat ⟨0⟩) 64 (nextEmptyPtr ptr)
    (by have hu := lt_usize 0 (by decide); have hp := h.lower; omega)
  apply loadedWord_of_read hh.active (by
    change ptr.toNat + 32 ≤ (writeWord (writeWord mem ptr.toNat ⟨0⟩) 64 _).size
    omega)
    (expandedWords32_cover h.active (by omega))
  unfold emptyHeaderMem
  rw [writeWord_read_preserved _ 64 ptr.toNat (nextEmptyPtr ptr)
    (by have hu := lt_usize 0 (by decide); have hp := h.lower; omega)
    (Or.inr ⟨by have hp := h.lower; omega, by omega⟩),
    writeWord_read_back mem ptr.toNat ⟨0⟩ hg]

theorem emptyHeader_prefix {mem aw ptr} (h : HeapMemory mem aw ptr) :
    MemoryPrefix mem (emptyHeaderMem mem ptr) ptr.toNat := by
  have hg : ptr.toNat - mem.size < USize.size := by
    have hu := lt_usize 32 (by decide)
    have hp := h.gap
    omega
  have hs := writeWord_size mem ptr.toNat ⟨0⟩ hg
  exact (memoryPrefix_writeWord mem ptr.toNat ptr.toNat ⟨0⟩ hg (Or.inl (le_refl _))).trans
    (memoryPrefix_writeWord _ 64 ptr.toNat (nextEmptyPtr ptr)
      (by have hu := lt_usize 0 (by decide); have hp := h.lower; omega)
      (Or.inr (by decide)))

noncomputable def emptyEncodedMem (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (emptyHeaderMem mem ptr) (nextEmptyPtr ptr).toNat ⟨0⟩

def emptyEncodedWords (aw ptr : UInt256) : UInt256 :=
  expandedWords (expandedWords (emptyHeaderWords aw ptr) ptr ⟨32⟩) (nextEmptyPtr ptr) ⟨32⟩

theorem emptyEncoded_heap {mem aw ptr} (h : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    HeapMemory (emptyEncodedMem mem ptr) (emptyEncodedWords aw ptr) (nextEmptyPtr ptr) := by
  have hh := emptyHeader_heap h hb
  have he : HeapMemory (emptyHeaderMem mem ptr)
      (expandedWords (emptyHeaderWords aw ptr) ptr ⟨32⟩) (nextEmptyPtr ptr) :=
    ⟨hh.size, hh.free, hh.lower, hh.gap, activeWords_expand32 hh.active (by omega)⟩
  exact he.writeAbove (nextEmptyPtr ptr) ⟨0⟩ (le_refl _) he.gap
    (by rw [nextEmptyPtr_toNat hb]; omega)

theorem emptyEncoded_prefix {mem aw ptr} (h : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    MemoryPrefix mem (emptyEncodedMem mem ptr) ptr.toNat := by
  have hh := emptyHeader_heap h hb
  have hp := nextEmptyPtr_toNat hb
  exact (emptyHeader_prefix h).trans
    (memoryPrefix_writeWord _ (nextEmptyPtr ptr).toNat ptr.toNat ⟨0⟩
      (by have hu := lt_usize 32 (by decide); have hg := hh.gap; omega)
      (Or.inl (by omega)))

end Auction

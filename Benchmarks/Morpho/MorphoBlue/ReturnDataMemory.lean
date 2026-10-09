import Benchmarks.Morpho.MorphoBlue.ReturnData
import Benchmarks.Morpho.MorphoBlue.AccrueHeap

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- GENERALIZES Reasoning.Theory.solcReturnDataMem reads to a header beyond existing memory.
theorem bytesAllocMem_properties_of_gap {mem out : ByteArray} {ptr : UInt256}
    (hm : 96 ≤ mem.size) (hl : 96 ≤ ptr.toNat)
    (hg : ptr.toNat - mem.size < USize.size) (hn : out.size ≠ 0)
    (hb : ptr.toNat + 32 < UInt256.size) :
    (bytesAllocMem mem out ptr).size = max mem.size (ptr.toNat + 32 + out.size) ∧
    memLoad (UInt256.ofNat 64) (bytesAllocMem mem out ptr) = bytesAllocPtr ptr out.size ∧
    memLoad ptr (bytesAllocMem mem out ptr) = UInt256.ofNat out.size ∧
    (32 ≤ out.size → memLoad (ptr + UInt256.ofNat 32) (bytesAllocMem mem out ptr) =
      calldataWord out 0) := by
  let mem0 := writeWord mem 64 (bytesAllocPtr ptr out.size)
  let mem1 := writeWord mem0 ptr.toNat (UInt256.ofNat out.size)
  have h64 : 64 - mem.size < USize.size := by have hu := USize.size_pos; omega
  have hs0 : mem0.size = mem.size := by
    dsimp only [mem0]
    rw [writeWord_size _ _ _ h64]
    omega
  have hg1 : ptr.toNat - mem0.size < USize.size := by rw [hs0]; exact hg
  have hs1 : mem1.size = max mem.size (ptr.toNat + 32) := by
    dsimp only [mem1]
    rw [writeWord_size _ _ _ hg1, hs0]
  have hs : (bytesAllocMem mem out ptr).size = max mem.size (ptr.toNat + 32 + out.size) := by
    change (out.write 0 mem1 (ptr.toNat + 32) out.size).size = _
    rw [writeBytes_size _ _ _ hn (by rw [hs1]; omega), hs1]
    omega
  have hread (off : Nat) (ho : off + 32 ≤ ptr.toNat + 32) :
      (bytesAllocMem mem out ptr).readWithPadding off 32 = mem1.readWithPadding off 32 :=
    write_read_below_gen_extend out mem1 (ptr.toNat + 32) out.size off hn le_rfl
      (by rw [hs1]; omega) ho
  refine ⟨hs, ?_, ?_, ?_⟩
  · apply mloadWordValue_of_readWithPadding
    · change 64 < _; rw [hs]; omega
    · change (bytesAllocMem mem out ptr).readWithPadding 64 32 = _
      rw [hread 64 (by omega)]
      dsimp only [mem1]
      rw [writeWord_read_preserved _ ptr.toNat 64 _ hg1
        (Or.inl ⟨by omega, by rw [hs0]; exact hm⟩)]
      exact writeWord_read_back mem 64 _ h64
  · apply mloadWordValue_of_readWithPadding (by rw [hs]; omega)
    rw [hread ptr.toNat le_rfl]
    exact writeWord_read_back mem0 ptr.toNat _ hg1
  · intro hw
    have hp := uadd_word_ofNat_toNat ptr 32 hb
    apply mloadWordValue_of_readWithPadding (by rw [hs, hp]; omega)
    rw [hp, calldataWord_bytes hw]
    exact byteArray_write_prefix32 out mem1 (ptr.toNat + 32) hw (by rw [hs1]; omega)

-- GENERALIZES Reasoning.Theory.bytesAlloc_prefix to arbitrary finite allocation gaps.
theorem bytesAllocMem_prefix_of_gap {mem out : ByteArray} {ptr : UInt256}
    (hm : 96 ≤ mem.size) (hg : ptr.toNat - mem.size < USize.size) (hn : out.size ≠ 0) :
    MemoryPrefix mem (bytesAllocMem mem out ptr) ptr.toNat := by
  have h64 : 64 - mem.size < USize.size := by have hu := USize.size_pos; omega
  have hs0 : (writeWord mem 64 (bytesAllocPtr ptr out.size)).size = mem.size := by
    rw [writeWord_size _ _ _ h64]; omega
  have hg1 : ptr.toNat - (writeWord mem 64 (bytesAllocPtr ptr out.size)).size < USize.size := by
    rw [hs0]; exact hg
  have hs1 := writeWord_size (writeWord mem 64 (bytesAllocPtr ptr out.size)) ptr.toNat
    (UInt256.ofNat out.size) hg1
  exact (memoryPrefix_writeWord mem 64 ptr.toNat _ h64 (Or.inr (by decide))).trans
    ((memoryPrefix_writeWord _ ptr.toNat ptr.toNat _ hg1 (Or.inl le_rfl)).trans
      (memoryPrefix_writeBytes out _ (ptr.toNat + 32) ptr.toNat hn
        (by rw [hs1]; omega) (by omega)))

theorem MorphoHeap.returnData {mem out : ByteArray} {ptr : UInt256} {spare : Nat}
    (h : MorphoHeap mem ptr 0) (hn : out.size ≠ 0)
    (hfit : ptr.toNat + (out.size + 63) / 32 * 32 + spare < 2 ^ 64)
    (hgap : 31 + spare < USize.size) :
    MorphoHeap (bytesAllocMem mem out ptr) (bytesAllocPtr ptr out.size) spare := by
  have hg := h.gap
  have hb := h.space
  have hp := bytesAllocPtr_toNat (ptr := ptr) (size := out.size) (by omega)
  have hs := bytesAllocMem_properties_of_gap h.size h.lower (by omega) hn
    (by change _ < 2 ^ 256; omega)
  refine ⟨by rw [hs.1]; have hm := h.size; omega, hs.2.1, ?_, ?_, ?_⟩
  · rw [hp]; have hl := h.lower; omega
  · rw [hp, hs.1]; omega
  · rw [hp]; omega

-- LIBRARY CANDIDATE: allocated strings preserve all earlier words outside the free pointer.
theorem morphoErrorMem_prefix {mem : ByteArray} {ptr : UInt256} (length payload : UInt256)
    (hm : 96 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hg : ptr.toNat - mem.size < USize.size) (hb : ptr.toNat + 32 < UInt256.size) :
    MemoryPrefix mem (morphoErrorMem length payload mem) ptr.toNat := by
  have h64 : 64 - mem.size < USize.size := by have hu := USize.size_pos; omega
  have hs0 : (writeWord mem 64 (ptr + UInt256.ofNat 64)).size = mem.size := by
    rw [writeWord_size _ _ _ h64]; omega
  have hg1 : ptr.toNat - (writeWord mem 64 (ptr + UInt256.ofNat 64)).size < USize.size := by
    rw [hs0]; exact hg
  have hs1 := writeWord_size (writeWord mem 64 (ptr + UInt256.ofNat 64)) ptr.toNat length hg1
  have hg2 : ptr.toNat + 32 -
      (writeWord (writeWord mem 64 (ptr + UInt256.ofNat 64)) ptr.toNat length).size < USize.size := by
    rw [hs1]; have hu := USize.size_pos; omega
  have hp := uadd_word_ofNat_toNat ptr 32 hb
  unfold morphoErrorMem
  rw [hfree]
  dsimp only
  rw [hp]
  exact (memoryPrefix_writeWord mem 64 ptr.toNat _ h64 (Or.inr (by decide))).trans
    ((memoryPrefix_writeWord _ ptr.toNat ptr.toNat length hg1 (Or.inl le_rfl)).trans
      (memoryPrefix_writeWord _ (ptr.toNat + 32) ptr.toNat payload hg2 (Or.inl (by omega))))

-- LIBRARY CANDIDATE: transport an in-bounds word load across preserved allocated memory.
theorem memoryPrefix_memLoad {before after : ByteArray} {limit : Nat}
    (h : MemoryPrefix before after limit) (off : UInt256)
    (hl : 96 ≤ off.toNat) (hb : off.toNat + 32 ≤ limit)
    (hin : off.toNat + 32 ≤ before.size) : memLoad off after = memLoad off before := by
  unfold memLoad
  have hs := h.size
  rw [if_neg (show ¬ off.toNat ≥ after.size by omega),
    if_neg (show ¬ off.toNat ≥ before.size by omega), h.read off.toNat hl hb hin]

theorem MorphoHeap.errorMessage {mem : ByteArray} {ptr : UInt256}
    (h : MorphoHeap mem ptr 0) (length payload : UInt256)
    (hfit : ptr.toNat + 64 < 2 ^ 64) :
    MorphoHeap (morphoErrorMem length payload mem) (ptr + UInt256.ofNat 64) 0 := by
  have hs := morphoErrorMem_properties_general length payload ptr mem h.lower h.free h.size
    (by have hg := h.gap; omega) (by change _ < 2 ^ 256; omega)
  have hp := uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  refine ⟨by rw [hs.1]; have hm := h.size; omega, hs.2.1, ?_, ?_, ?_⟩
  · rw [hp]; have hl := h.lower; omega
  · rw [hp, hs.1]; have hu := USize.size_pos; omega
  · rw [hp]; omega

end Benchmarks.Morpho.MorphoBlue

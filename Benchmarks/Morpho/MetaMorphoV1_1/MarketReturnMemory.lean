import Benchmarks.Morpho.MetaMorphoV1_1.MarketCall
import Benchmarks.Morpho.MetaMorphoV1_1.MarketReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory

/-! Memory representation of the six decoded market words. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem marketOutputMem_size {mem out : ByteArray} {ptr : UInt256}
    (hin : ptr.toNat ≤ mem.size) (hl : 192 ≤ out.size) (hh : out.size < UInt256.size) :
    (marketOutputMem mem ptr out).size = max mem.size (ptr.toNat + 192) :=
  fixedReturnBuffer_size (by decide) hin hl hh

theorem marketOutputMem_load {mem out : ByteArray} {ptr : UInt256} {off : Nat}
    (hin : ptr.toNat ≤ mem.size) (hl : 192 ≤ out.size) (hh : out.size < UInt256.size)
    (hp : ptr.toNat + 192 < UInt256.size) (hoff : off + 32 ≤ 192) :
    memLoad (ptr + UInt256.ofNat off) (marketOutputMem mem ptr out) =
      calldataWord out off :=
  fixedReturnBuffer_load hin hl hh hp hoff

theorem marketReservedMem_size (mem : ByteArray) (ptr : UInt256) :
    (marketReservedMem mem ptr).size = max mem.size 96 := by
  simp only [marketReservedMem, writeWord_sparse_size, max_self, max_assoc]

theorem marketReservedMem_free (mem : ByteArray) (ptr : UInt256) :
    memLoad ⟨64⟩ (marketReservedMem mem ptr) =
      nextCursor (nextCursor ptr ⟨192⟩) ⟨192⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem marketReservedMem_load {mem out : ByteArray} {ptr : UInt256} {off : Nat}
    (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat + 192 ≤ mem.size)
    (hp : ptr.toNat + 192 < UInt256.size) (hoff : off + 32 ≤ 192)
    (hread : memLoad (ptr + UInt256.ofNat off) mem = calldataWord out off) :
    memLoad (ptr + UInt256.ofNat off) (marketReservedMem mem ptr) =
      calldataWord out off := by
  rw [marketReservedMem,
    wordWindowRead_freeWrite _ hlo (by rw [writeWord_sparse_size]; omega) hp hoff,
    wordWindowRead_freeWrite _ hlo hmem hp hoff]
  exact hread

def marketCopyMem (mem : ByteArray) (dst : Nat) (out : ByteArray) : ByteArray :=
  structReturnMemory mem dst out 6

theorem marketCopyMem_size (mem : ByteArray) (dst : Nat) (out : ByteArray) :
    (marketCopyMem mem dst out).size = max mem.size (dst + 192) :=
  structReturnMemory_size mem dst out (by decide)

theorem marketCopyMem_free {mem out : ByteArray} {dst : Nat}
    (hmem : 96 ≤ mem.size) (hdst : 96 ≤ dst) :
    memLoad ⟨64⟩ (marketCopyMem mem dst out) = memLoad ⟨64⟩ mem :=
  structReturnMemory_free hmem hdst

theorem marketCopyMem_field (mem : ByteArray) (dst : Nat) (out : ByteArray)
    (i : Nat) (hi : i < 6) (hfit : dst + 192 < UInt256.size) :
    memLoad (UInt256.ofNat (dst + 32 * i)) (marketCopyMem mem dst out) =
      calldataWord out (32 * i) :=
  structReturnMemory_field mem dst out i hi hfit

def marketReadMemory (mem : ByteArray) (ptr : UInt256) (id : UInt256)
    (out : ByteArray) : ByteArray :=
  marketCopyMem
    (marketReservedMem (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out) ptr)
    (nextCursor ptr ⟨192⟩).toNat out

theorem nextCursor_192_twice (ptr : UInt256) :
    nextCursor (nextCursor ptr ⟨192⟩) ⟨192⟩ = nextCursor ptr ⟨384⟩ := by
  change (ptr + (⟨192⟩ : UInt256)) + (⟨192⟩ : UInt256) = ptr + (⟨384⟩ : UInt256)
  rw [u256_add_assoc]
  rfl

theorem marketReadMemory_prefix (mem : ByteArray) (ptr id : UInt256) (out : ByteArray)
    (hfit : allocationFits ptr ⟨384⟩) (hl : 192 ≤ out.size)
    (hh : out.size < UInt256.size) :
    MemoryPrefix mem (marketReadMemory mem ptr id out) ptr.toNat := by
  have hp := (allocationFits_aligned ptr ⟨384⟩ (by decide +kernel)).mp hfit
  have hn : (nextCursor ptr ⟨192⟩).toNat = ptr.toNat + 192 :=
    uadd_word_ofNat_toNat ptr 192 (by change _ < 2 ^ 256; omega)
  have hcall : MemoryPrefix mem (marketCallMem mem ptr.toNat id) ptr.toNat := by
    apply memoryPrefix_sparse_cascade
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro write (rfl | rfl) <;> exact .inl (by simp only; omega)
  have hout : MemoryPrefix (marketCallMem mem ptr.toNat id)
      (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out) ptr.toNat := by
    change MemoryPrefix _ (fixedReturnBuffer _ _ _ 192) _
    rw [fixedReturnBuffer_long _ _ _ hl hh]
    exact copyWindow_prefix _ _ _ _ _ _ (by decide) (by omega)
      (by rw [marketCallMem_size]; omega) (.inl (le_refl _))
  have hreserved : MemoryPrefix
      (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out)
      (marketReservedMem (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out) ptr)
      ptr.toNat :=
    (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide)))
  exact hcall.trans (hout.trans (hreserved.trans
    ((wordSequenceMemory_prefix _ _ _).mono (by rw [hn]; omega))))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

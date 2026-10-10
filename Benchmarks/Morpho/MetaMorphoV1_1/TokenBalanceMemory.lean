import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceReturn
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotAllocation

/-! The returned token balance, advanced cursor, and preserved allocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem tokenBalanceCallMem_prefix (mem : ByteArray) (ptr : Nat) (owner : AccountAddress) :
    MemoryPrefix mem (tokenBalanceCallMem mem ptr owner) ptr :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega)))

def tokenBalanceReadMemory (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (out : ByteArray) : ByteArray :=
  writeWord (fixedReturnBuffer (tokenBalanceCallMem mem ptr.toNat owner) ptr out 32)
    64 (nextCursor ptr ⟨32⟩)

theorem tokenBalanceReadMemory_size (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (out : ByteArray) (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) :
    (tokenBalanceReadMemory mem ptr owner out).size =
      max (max mem.size (ptr.toNat + 36)) 96 := by
  rw [tokenBalanceReadMemory, writeWord_sparse_size,
    fixedReturnBuffer_size (by decide) (by rw [tokenBalanceCallMem_size]; omega) hl hh,
    tokenBalanceCallMem_size]
  omega

theorem tokenBalanceReadMemory_free (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (out : ByteArray) :
    memLoad ⟨64⟩ (tokenBalanceReadMemory mem ptr owner out) = nextCursor ptr ⟨32⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem tokenBalanceReadMemory_load (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (out : ByteArray) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) :
    memLoad ptr (tokenBalanceReadMemory mem ptr owner out) = calldataWord out 0 := by
  have hin : ptr.toNat ≤ (tokenBalanceCallMem mem ptr.toNat owner).size := by
    rw [tokenBalanceCallMem_size]; omega
  have hp : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
  have hw := wordWindowRead_freeWrite (nextCursor ptr ⟨32⟩) hlo
    (by rw [fixedReturnBuffer_size (by decide) hin hl hh]; omega) hp (by decide : 0 + 32 ≤ 32)
  have hr := fixedReturnBuffer_load hin hl hh hp (by decide : 0 + 32 ≤ 32)
  simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using hw.trans hr

theorem tokenBalanceReadMemory_prefix (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (out : ByteArray) (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) :
    MemoryPrefix mem (tokenBalanceReadMemory mem ptr owner out) ptr.toNat := by
  have hout : MemoryPrefix (tokenBalanceCallMem mem ptr.toNat owner)
      (fixedReturnBuffer (tokenBalanceCallMem mem ptr.toNat owner) ptr out 32) ptr.toNat := by
    rw [fixedReturnBuffer_long _ _ _ hl hh]
    exact copyWindow_prefix _ _ _ _ _ _ (by decide) (by omega)
      (by rw [tokenBalanceCallMem_size]; omega) (.inl (le_refl _))
  exact (tokenBalanceCallMem_prefix mem ptr.toNat owner).trans
    (hout.trans (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))))

theorem tokenBalanceReadMemory_cursor_bound (mem : ByteArray) (ptr : UInt256)
    (owner : AccountAddress) (out : ByteArray)
    (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) (hfit : allocationFits ptr ⟨32⟩) :
    (nextCursor ptr ⟨32⟩).toNat ≤ (tokenBalanceReadMemory mem ptr owner out).size := by
  have hp := (allocationFits_aligned ptr ⟨32⟩ (by decide +kernel)).mp hfit
  have hn : (nextCursor ptr ⟨32⟩).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  rw [hn, tokenBalanceReadMemory_size mem ptr owner out hl hh]
  omega

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

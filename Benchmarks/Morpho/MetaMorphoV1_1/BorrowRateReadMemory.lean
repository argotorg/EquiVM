import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateReturn
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotAllocation

/-! The returned rate word, advanced cursor, and preserved allocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def borrowRateReadMemory (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData)
    (market out : ByteArray) : ByteArray :=
  writeWord (fixedReturnBuffer (borrowRateCallMem mem ptr.toNat p market) ptr out 32)
    64 (nextCursor ptr ⟨32⟩)

theorem borrowRateReadMemory_size (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData)
    (market out : ByteArray) (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) :
    (borrowRateReadMemory mem ptr p market out).size = max mem.size (ptr.toNat + 356) := by
  rw [borrowRateReadMemory, writeWord_sparse_size,
    fixedReturnBuffer_size (by decide) (by rw [borrowRateCallMem_size]; omega) hl hh,
    borrowRateCallMem_size]
  omega

theorem borrowRateReadMemory_free (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData)
    (market out : ByteArray) :
    memLoad ⟨64⟩ (borrowRateReadMemory mem ptr p market out) = nextCursor ptr ⟨32⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem borrowRateReadMemory_load (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData)
    (market out : ByteArray) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) :
    memLoad ptr (borrowRateReadMemory mem ptr p market out) = calldataWord out 0 := by
  have hin : ptr.toNat ≤ (borrowRateCallMem mem ptr.toNat p market).size := by
    rw [borrowRateCallMem_size]; omega
  have hp : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
  have hw := wordWindowRead_freeWrite (nextCursor ptr ⟨32⟩) hlo
    (by rw [fixedReturnBuffer_size (by decide) hin hl hh]; omega) hp (by decide : 0 + 32 ≤ 32)
  have hr := fixedReturnBuffer_load hin hl hh hp (by decide : 0 + 32 ≤ 32)
  simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using hw.trans hr

theorem borrowRateReadMemory_prefix (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData)
    (market out : ByteArray) (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) :
    MemoryPrefix mem (borrowRateReadMemory mem ptr p market out) ptr.toNat := by
  have hout : MemoryPrefix (borrowRateCallMem mem ptr.toNat p market)
      (fixedReturnBuffer (borrowRateCallMem mem ptr.toNat p market) ptr out 32) ptr.toNat := by
    rw [fixedReturnBuffer_long _ _ _ hl hh]
    exact copyWindow_prefix _ _ _ _ _ _ (by decide) (by omega)
      (by rw [borrowRateCallMem_size]; omega) (.inl (le_refl _))
  exact (borrowRateCallMem_prefix mem ptr.toNat p market).trans
    (hout.trans (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))))

theorem borrowRateReadMemory_cursor_bound (mem : ByteArray) (ptr : UInt256)
    (p : MarketParamsData) (market out : ByteArray)
    (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) (hfit : allocationFits ptr ⟨32⟩) :
    (nextCursor ptr ⟨32⟩).toNat ≤ (borrowRateReadMemory mem ptr p market out).size := by
  have hp := (allocationFits_aligned ptr ⟨32⟩ (by decide +kernel)).mp hfit
  have hn : (nextCursor ptr ⟨32⟩).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  rw [hn, borrowRateReadMemory_size mem ptr p market out hl hh]
  omega

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

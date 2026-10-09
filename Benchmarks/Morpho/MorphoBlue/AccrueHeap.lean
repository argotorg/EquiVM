import Benchmarks.Morpho.MorphoBlue.AccrueCall
import Benchmarks.Morpho.MorphoBlue.AccruePrepareCall
import Benchmarks.Morpho.MorphoBlue.AccrueFinish
import Benchmarks.Morpho.MorphoBlue.NarrowingRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- Memory may extend beyond the free pointer because call and event buffers are reused.
-- The spare bound tracks the finite allocations still required by this routine.
structure MorphoHeap (mem : ByteArray) (fp : UInt256) (spare : Nat) : Prop where
  size : 96 ≤ mem.size
  free : memLoad (UInt256.ofNat 64) mem = fp
  lower : 96 ≤ fp.toNat
  gap : fp.toNat + spare - mem.size < USize.size
  space : fp.toNat + spare ≤ 2 ^ 64 - 1

theorem MorphoHeap.hash {mem fp spare} (h : MorphoHeap mem fp spare) (key slot : UInt256) :
    MorphoHeap (twoWordHashMem key slot mem) fp spare := by
  have hs := twoWordHashMem_size_of_ge_64' (mem := mem) key slot (by have hh := h.size; omega)
  refine ⟨by rw [hs]; exact h.size, ?_, h.lower, by rw [hs]; exact h.gap, h.space⟩
  rw [twoWordHashMem_memLoad_above64 key slot (UInt256.ofNat 64) (by decide) h.size, h.free]

theorem MorphoHeap.alloc64Guard {mem fp spare} (h : MorphoHeap mem fp spare) (hs : 64 ≤ spare) :
    UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
      (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (memLoad (UInt256.ofNat 64) mem)) = UInt256.ofNat 0 := by
  have hb := h.space
  have hadd : (fp + UInt256.ofNat 64).toNat = fp.toNat + 64 :=
    uadd_word_ofNat_toNat fp 64 (by change _ < 2 ^ 256; omega)
  rw [h.free, ugt_zero (by rw [hadd]; change _ ≤ 18446744073709551615; omega),
    ult_zero (by rw [hadd]; omega)]
  rfl

theorem MorphoHeap.narrowProperties {mem fp spare} (h : MorphoHeap mem fp spare) :
    (uint128ErrorMem mem).size = max mem.size (fp.toNat + 64) ∧
    memLoad (UInt256.ofNat 64) (uint128ErrorMem mem) = fp + UInt256.ofNat 64 := by
  have hp := morphoErrorMem_properties_general (UInt256.ofNat 20)
    (UInt256.ofNat 49474313745504357941522707766437553544126227675921007535886519822381247102976)
    fp mem h.lower h.free h.size (by have hg := h.gap; omega)
    (by have hb := h.space; change _ < 2 ^ 256; omega)
  exact ⟨hp.1, hp.2.1⟩

theorem MorphoHeap.narrow {mem fp spare} (h : MorphoHeap mem fp spare) (hs : 64 ≤ spare) :
    MorphoHeap (uint128ErrorMem mem) (fp + UInt256.ofNat 64) (spare - 64) := by
  have hp := h.narrowProperties
  have hb := h.space
  have hadd : (fp + UInt256.ofNat 64).toNat = fp.toNat + 64 :=
    uadd_word_ofNat_toNat fp 64 (by change _ < 2 ^ 256; omega)
  refine ⟨by rw [hp.1]; have hh := h.size; omega, hp.2, ?_, ?_, ?_⟩
  · rw [hadd]; have hl := h.lower; omega
  · rw [hadd, hp.1]; have hg := h.gap; omega
  · rw [hadd]; omega

theorem MorphoHeap.callData {mem fp spare} (h : MorphoHeap mem fp spare)
    (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv) :
    MorphoHeap (accrueCallDataMem p σ I mem fp) fp spare := by
  have hg : fp.toNat - mem.size < USize.size := by have hg := h.gap; omega
  have hs := accrueCallDataMem_size p σ I mem fp (by have hh := h.size; omega) hg
  refine ⟨by rw [hs]; have hh := h.size; omega, ?_, h.lower, ?_, h.space⟩
  · rw [accrueCallDataMem_freePtr p σ I mem fp h.size h.lower hg, h.free]
  · rw [hs]; have hg := h.gap; omega

theorem MorphoHeap.callReturn {mem fp spare} (h : MorphoHeap mem fp spare)
    (out : ByteArray) (hb : out.size < UInt256.size) (hin : fp.toNat + 32 ≤ mem.size)
    (hs : 32 ≤ spare) :
    MorphoHeap (accrueCallMem mem out fp) (fp + UInt256.ofNat 32) (spare - 32) := by
  have hcs : (callOutputMem mem out fp (UInt256.ofNat 32)).size = mem.size := callOutput32_size mem out fp hb hin
  have hreserve : returnReservePtr fp 32 = fp + UInt256.ofNat 32 := by
    unfold returnReservePtr
    congr 1
  have hshape : accrueCallMem mem out fp = writeWord (callOutputMem mem out fp (UInt256.ofNat 32)) 64
      (fp + UInt256.ofNat 32) := by rw [accrueCallMem, returnReserveMem, hreserve]
  have hg : 64 - (callOutputMem mem out fp (UInt256.ofNat 32)).size < USize.size := by
    rw [hcs]; have hm := h.size; have hu := USize.size_pos; omega
  have hms : (accrueCallMem mem out fp).size = mem.size := by
    rw [hshape, writeWord_size _ _ _ hg, hcs]
    have hm := h.size; omega
  have hf : memLoad (UInt256.ofNat 64) (accrueCallMem mem out fp) = fp + UInt256.ofNat 32 := by
    rw [hshape]
    exact memLoad_writeWord_self_of_offset _ _ _ _ hg rfl
  have hh := h.space
  have hadd : (fp + UInt256.ofNat 32).toNat = fp.toNat + 32 :=
    uadd_word_ofNat_toNat fp 32 (by change _ < 2 ^ 256; omega)
  refine ⟨by rw [hms]; exact h.size, hf, ?_, ?_, ?_⟩
  · rw [hadd]; have hl := h.lower; omega
  · rw [hadd, hms]; have hg := h.gap; omega
  · rw [hadd]; omega

theorem MorphoHeap.errorGap {mem fp spare} (h : MorphoHeap mem fp spare) :
    (memLoad (UInt256.ofNat 64) mem).toNat - mem.size < USize.size := by
  rw [h.free]; have hg := h.gap; omega

theorem MorphoHeap.errorHi {mem fp spare} (h : MorphoHeap mem fp spare) :
    (memLoad (UInt256.ofNat 64) mem).toNat + 100 < UInt256.size := by
  rw [h.free]; have hs := h.space; change _ < 2 ^ 256; omega

theorem MorphoHeap.event {mem fp spare} (h : MorphoHeap mem fp spare)
    (rate interest shares : UInt256) :
    MorphoHeap (accrueEventMem mem rate interest shares) fp spare := by
  have hb := h.space
  have h32 := uadd_word_ofNat_toNat fp 32 (by change _ < 2 ^ 256; omega)
  have h64 := uadd_word_ofNat_toNat fp 64 (by change _ < 2 ^ 256; omega)
  have hs := h.size
  have hl := h.lower
  have hg := h.gap
  have hm : accrueEventMem mem rate interest shares =
      writeWord (writeWord (writeWord mem fp.toNat rate) (fp.toNat + 32) interest)
        (fp.toNat + 64) shares := by rw [accrueEventMem, h.free, h32, h64]
  have h0 := writeWord_size mem fp.toNat rate (by omega)
  have h1 := writeWord_size (writeWord mem fp.toNat rate) (fp.toNat + 32) interest
    (by rw [h0]; have hu := USize.size_pos; omega)
  have h2 := writeWord_size (writeWord (writeWord mem fp.toNat rate) (fp.toNat + 32) interest)
    (fp.toNat + 64) shares (by rw [h1, h0]; have hu := USize.size_pos; omega)
  refine ⟨by rw [hm, h2, h1, h0]; omega, ?_, h.lower, ?_, h.space⟩
  · rw [hm, memLoad_writeWord_disjoint _ _ _ _ (by rw [h1, h0]; have hu := USize.size_pos; omega)
      (by change 64 + 32 ≤ _; rw [h1, h0]; omega) (Or.inl (by change 64 + 32 ≤ _; omega)),
      memLoad_writeWord_disjoint _ _ _ _ (by rw [h0]; have hu := USize.size_pos; omega)
        (by change 64 + 32 ≤ _; rw [h0]; omega) (Or.inl (by change 64 + 32 ≤ _; omega)),
      memLoad_writeWord_disjoint _ _ _ _ (by omega)
        (by change 64 + 32 ≤ _; omega) (Or.inl (by change 64 + 32 ≤ _; omega)), h.free]
  · rw [hm, h2, h1, h0]; omega

end Benchmarks.Morpho.MorphoBlue

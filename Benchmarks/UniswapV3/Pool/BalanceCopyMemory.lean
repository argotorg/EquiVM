import Benchmarks.UniswapV3.Pool.BalanceMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def balanceCopyMem1 (mem : ByteArray) (p : UInt256) : ByteArray :=
  writeWord mem (p.toNat + 68) (memLoad (p + ⟨32⟩) mem)

def balanceCopyMem2 (mem : ByteArray) (p : UInt256) : ByteArray :=
  writeWord (balanceCopyMem1 mem p) (p.toNat + 100)
    (spliceWord4 (memLoad (p + ⟨64⟩) (balanceCopyMem1 mem p))
      (memLoad (p + ⟨100⟩) (balanceCopyMem1 mem p)))

theorem balanceCopyMem1_size (mem : ByteArray) (p : UInt256) :
    (balanceCopyMem1 mem p).size = max mem.size (p.toNat + 100) := by
  simp only [balanceCopyMem1, writeWord_sparse_size]

theorem balanceCopyMem2_size (mem : ByteArray) (p : UInt256) :
    (balanceCopyMem2 mem p).size = max mem.size (p.toNat + 132) := by
  simp only [balanceCopyMem2, writeWord_sparse_size, balanceCopyMem1_size]
  omega

theorem balanceCopyMem2_prefix (mem : ByteArray) (p : UInt256) :
    MemoryPrefix mem (balanceCopyMem2 mem p) (p.toNat + 68) := by
  unfold balanceCopyMem2 balanceCopyMem1
  refine (memoryPrefix_sparse_writeWord mem (p.toNat + 68) (p.toNat + 68)
    (memLoad (p + ⟨32⟩) mem) (Or.inl (le_refl _))).trans ?_
  exact memoryPrefix_sparse_writeWord _ (p.toNat + 100) (p.toNat + 68) _ (Or.inl (by omega))

theorem balanceCopyMem2_read (mem : ByteArray) (p : UInt256)
    (hin : p.toNat + 68 ≤ mem.size) (hb : p.toNat + 132 < UInt256.size) :
    (balanceCopyMem2 mem p).readWithPadding (p.toNat + 68) 36 =
      mem.readWithPadding (p.toNat + 32) 36 := by
  have h32 : (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 := uadd_word_ofNat_toNat p 32 (by omega)
  have h64 : (p + (⟨64⟩ : UInt256)).toNat = p.toNat + 64 := uadd_word_ofNat_toNat p 64 (by omega)
  have hread1 : (balanceCopyMem2 mem p).readWithPadding (p.toNat + 68) 32 =
      mem.readWithPadding (p.toNat + 32) 32 := by
    unfold balanceCopyMem2
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
      rw [balanceCopyMem1_size]; omega⟩)]
    unfold balanceCopyMem1
    rw [writeWord_sparse_read_back, memLoad_toByteArray _ _ (by rw [h32]; omega), h32]
  have hread2 : (balanceCopyMem2 mem p).readWithPadding (p.toNat + 100) 4 =
      mem.readWithPadding (p.toNat + 64) 4 := by
    unfold balanceCopyMem2
    change (Reasoning.Theory.writeWord _ (p.toNat + 100) _).readWithPadding
      ((p.toNat + 100) + 0) 4 = _
    rw [writeWord_sparse_read_window _ _ 0 4 _ (by decide) (by decide) (by decide),
      spliceWord4_prefix, memLoad_toByteArray_window _ _ 0 4 (by
        rw [h64, balanceCopyMem1_size]; omega) (by decide) (by decide), h64, Nat.add_zero]
    unfold balanceCopyMem1
    exact writeWord_sparse_read_preserved_len _ _ _ 4 _ (Or.inl ⟨by omega, by omega⟩)
      (by decide) (by decide)
  rw [show 36 = 32 + 4 from rfl, byteArray_readWithPadding_split _ _ 32 4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by
        rw [balanceCopyMem2_size]; omega),
    byteArray_readWithPadding_split mem _ 32 4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega), hread1]
  rw [show p.toNat + 68 + 32 = p.toNat + 100 by omega,
    show p.toNat + 32 + 32 = p.toNat + 64 by omega, hread2]

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.SafeTransferMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def transferCopyMem1 (mem : ByteArray) (p : UInt256) : ByteArray :=
  writeWord mem (p.toNat + 100) (memLoad (p + ⟨32⟩) mem)

def transferCopyMem2 (mem : ByteArray) (p : UInt256) : ByteArray :=
  writeWord (transferCopyMem1 mem p) (p.toNat + 132)
    (memLoad (p + ⟨64⟩) (transferCopyMem1 mem p))

def transferCopyMem3 (mem : ByteArray) (p : UInt256) : ByteArray :=
  writeWord (transferCopyMem2 mem p) (p.toNat + 164)
    (spliceWord4 (memLoad (p + ⟨96⟩) (transferCopyMem2 mem p))
      (memLoad (p + ⟨164⟩) (transferCopyMem2 mem p)))

theorem transferCopyMem1_size (mem : ByteArray) (p : UInt256) :
    (transferCopyMem1 mem p).size = max mem.size (p.toNat + 132) := by
  simp only [transferCopyMem1, writeWord_sparse_size]

theorem transferCopyMem2_size (mem : ByteArray) (p : UInt256) :
    (transferCopyMem2 mem p).size = max mem.size (p.toNat + 164) := by
  simp only [transferCopyMem2, writeWord_sparse_size, transferCopyMem1_size]
  omega

theorem transferCopyMem3_size (mem : ByteArray) (p : UInt256) :
    (transferCopyMem3 mem p).size = max mem.size (p.toNat + 196) := by
  simp only [transferCopyMem3, writeWord_sparse_size, transferCopyMem2_size]
  omega

theorem transferCopyMem3_prefix (mem : ByteArray) (p : UInt256) :
    MemoryPrefix mem (transferCopyMem3 mem p) (p.toNat + 100) := by
  unfold transferCopyMem3 transferCopyMem2 transferCopyMem1
  refine (memoryPrefix_sparse_writeWord mem (p.toNat + 100) (p.toNat + 100)
    (memLoad (p + ⟨32⟩) mem) (Or.inl (le_refl _))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ (p.toNat + 132) (p.toNat + 100)
    (memLoad (p + ⟨64⟩) (transferCopyMem1 mem p)) (Or.inl (by omega))).trans ?_
  exact memoryPrefix_sparse_writeWord _ (p.toNat + 164) (p.toNat + 100) _ (Or.inl (by omega))

theorem transferCopyMem3_read (mem : ByteArray) (p : UInt256)
    (hin : p.toNat + 100 ≤ mem.size) (hbound : p.toNat + 196 < UInt256.size) :
    (transferCopyMem3 mem p).readWithPadding (p.toNat + 100) 68 =
      mem.readWithPadding (p.toNat + 32) 68 := by
  have hoff (n : Nat) (hn : n ≤ 196) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by omega)
  have h32 : (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 := hoff 32 (by decide)
  have h64 : (p + (⟨64⟩ : UInt256)).toNat = p.toNat + 64 := hoff 64 (by decide)
  have h96 : (p + (⟨96⟩ : UInt256)).toNat = p.toNat + 96 := hoff 96 (by decide)
  have hread1 : (transferCopyMem3 mem p).readWithPadding (p.toNat + 100) 32 =
      mem.readWithPadding (p.toNat + 32) 32 := by
    unfold transferCopyMem3
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
      rw [transferCopyMem2_size]; omega⟩)]
    unfold transferCopyMem2
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
      rw [transferCopyMem1_size]; omega⟩)]
    unfold transferCopyMem1
    rw [writeWord_sparse_read_back, memLoad_toByteArray _ _ (by rw [h32]; omega)]
    rw [show (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 from hoff 32 (by decide)]
  have hread2 : (transferCopyMem3 mem p).readWithPadding (p.toNat + 132) 32 =
      mem.readWithPadding (p.toNat + 64) 32 := by
    unfold transferCopyMem3
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
      rw [transferCopyMem2_size]; omega⟩)]
    unfold transferCopyMem2
    rw [writeWord_sparse_read_back, memLoad_toByteArray _ _ (by
      rw [h64, transferCopyMem1_size]; omega)]
    rw [show (p + (⟨64⟩ : UInt256)).toNat = p.toNat + 64 from hoff 64 (by decide)]
    unfold transferCopyMem1
    exact writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by omega⟩)
  have hread3 : (transferCopyMem3 mem p).readWithPadding (p.toNat + 164) 4 =
      mem.readWithPadding (p.toNat + 96) 4 := by
    unfold transferCopyMem3
    change (Reasoning.Theory.writeWord _ (p.toNat + 164) _).readWithPadding ((p.toNat + 164) + 0) 4 = _
    rw [writeWord_sparse_read_window _ _ 0 4 _ (by decide) (by decide) (by decide),
      spliceWord4_prefix, memLoad_toByteArray_window _ _ 0 4 (by
        rw [h96, transferCopyMem2_size]; omega) (by decide) (by decide)]
    rw [show (p + (⟨96⟩ : UInt256)).toNat + 0 = p.toNat + 96 from by
      rw [h96]]
    unfold transferCopyMem2
    rw [writeWord_sparse_read_preserved_len _ _ _ 4 _ (Or.inl ⟨by omega, by
      rw [transferCopyMem1_size]; omega⟩) (by decide) (by decide)]
    unfold transferCopyMem1
    exact writeWord_sparse_read_preserved_len _ _ _ 4 _ (Or.inl ⟨by omega, by omega⟩)
      (by decide) (by decide)
  rw [show 68 = 32 + 36 from rfl, byteArray_readWithPadding_split _ _ 32 36
      (by decide) (by decide) (by decide) (by decide) (by decide) (by
        rw [transferCopyMem3_size]; omega),
    byteArray_readWithPadding_split mem _ 32 36
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega), hread1]
  rw [show p.toNat + 100 + 32 = p.toNat + 132 by omega,
    show p.toNat + 32 + 32 = p.toNat + 64 by omega]
  rw [show 36 = 32 + 4 from rfl, byteArray_readWithPadding_split _ _ 32 4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by
        rw [transferCopyMem3_size]; omega),
    byteArray_readWithPadding_split mem _ 32 4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega), hread2]
  rw [show p.toNat + 132 + 32 = p.toNat + 164 by omega,
    show p.toNat + 64 + 32 = p.toNat + 96 by omega, hread3]

end Benchmarks.UniswapV3.Pool

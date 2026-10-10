import Benchmarks.UniswapV4PoolManager.TickResultMemory
import Benchmarks.UniswapV4PoolManager.TickUpperStoreTrace
import Benchmarks.UniswapV4PoolManager.WordStoreMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickLowerResultMemory_span (mem : ByteArray) (ptr gross flipped : UInt256)
    (hf : ptr.toNat+32 < UInt256.size) :
    ptr.toNat+64 ≤ (tickLowerResultMemory mem ptr gross flipped).size := by
  have h32 : (ptr+(⟨32⟩ : UInt256)).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hf
  simp only [tickLowerResultMemory, writeWord_sparse_size, h32]
  omega

theorem tickLowerResultMemory_flipped (mem : ByteArray) (ptr gross flipped : UInt256) :
    memLoad ptr (tickLowerResultMemory mem ptr gross flipped) = flipped :=
  writeWord_sparse_load_back _ _ _

theorem tickLowerResultMemory_gross (mem : ByteArray) (ptr gross flipped : UInt256)
    (hf : ptr.toNat+32 < UInt256.size) :
    memLoad (ptr+UInt256.ofNat 32) (tickLowerResultMemory mem ptr gross flipped) = gross := by
  change memLoad (ptr+⟨32⟩) _ = gross
  have h32 : (ptr+(⟨32⟩ : UInt256)).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hf
  rw [tickLowerResultMemory, writeWord_sparse_load_disjoint _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (.inr (by rw [h32]))]
  exact writeWord_sparse_load_back _ _ _

theorem tickUpperResultMemory_size_ge (mem : ByteArray) (ptr gross flipped : UInt256) :
    mem.size ≤ (tickUpperResultMemory mem ptr gross flipped).size := by
  simp only [tickUpperResultMemory, writeWord_sparse_size]
  omega

theorem tickUpperResultMemory_span (mem : ByteArray) (ptr gross flipped : UInt256)
    (hf : ptr.toNat+96 < UInt256.size) :
    ptr.toNat+128 ≤ (tickUpperResultMemory mem ptr gross flipped).size := by
  have h96 : (ptr+(⟨96⟩ : UInt256)).toNat = ptr.toNat+96 := uadd_word_ofNat_toNat ptr 96 hf
  simp only [tickUpperResultMemory, writeWord_sparse_size, h96]
  omega

theorem tickUpperResultMemory_load_before (mem : ByteArray) (ptr gross flipped read : UInt256)
    (hin : read.toNat+32 ≤ mem.size) (hbefore : read.toNat+32 ≤ ptr.toNat+64)
    (hf : ptr.toNat+96 < UInt256.size) :
    memLoad read (tickUpperResultMemory mem ptr gross flipped) = memLoad read mem := by
  have h64 : (ptr+(⟨64⟩ : UInt256)).toNat = ptr.toNat+64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 : (ptr+(⟨96⟩ : UInt256)).toNat = ptr.toNat+96 := uadd_word_ofNat_toNat ptr 96 hf
  rw [tickUpperResultMemory,
    writeWord_sparse_load_before _ _ _ read (by rw [writeWord_sparse_size]; omega) (by rw [h64]; omega),
    writeWord_sparse_load_before _ _ _ read hin (by rw [h96]; omega)]

theorem tickUpperResultMemory_flipped (mem : ByteArray) (ptr gross flipped : UInt256) :
    memLoad (ptr+UInt256.ofNat 64) (tickUpperResultMemory mem ptr gross flipped) = flipped :=
  writeWord_sparse_load_back _ _ _

theorem tickUpperResultMemory_gross (mem : ByteArray) (ptr gross flipped : UInt256)
    (hf : ptr.toNat+96 < UInt256.size) :
    memLoad (ptr+UInt256.ofNat 96) (tickUpperResultMemory mem ptr gross flipped) = gross := by
  change memLoad (ptr+⟨96⟩) _ = gross
  have h64 : (ptr+(⟨64⟩ : UInt256)).toNat = ptr.toNat+64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 : (ptr+(⟨96⟩ : UInt256)).toNat = ptr.toNat+96 := uadd_word_ofNat_toNat ptr 96 hf
  rw [tickUpperResultMemory, writeWord_sparse_load_disjoint _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (.inr (by rw [h64, h96]))]
  exact writeWord_sparse_load_back _ _ _

end Benchmarks.UniswapV4PoolManager

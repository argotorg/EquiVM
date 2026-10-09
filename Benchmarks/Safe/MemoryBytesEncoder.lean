import Benchmarks.Safe.WordBufferCopy
import Benchmarks.Safe.ByteBufferMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def memoryBytesEncodedMemory (mem : ByteArray) (dst len : Nat) (words : List UInt256) :
    ByteArray :=
  writeWord (writeWord mem dst (UInt256.ofNat len) ++ wordBytes words) (dst + 32 + len) ⟨0⟩

-- GENERALIZES memoryBytesEncodedMemory to encoding over a populated memory suffix.
def memoryBytesEncodedInto (mem : ByteArray) (dst len : Nat) (words : List UInt256) :
    ByteArray :=
  writeWord (writeWords (writeWord mem dst (UInt256.ofNat len)) (dst + 32) words)
    (dst + 32 + len) ⟨0⟩

set_option maxRecDepth 100000 in
theorem safeMemoryBytesEncodeInto (words : List UInt256)
    {I g s0 σ k C aw mem rdata src dst len} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9767⟩
      (UInt256.ofNat src :: UInt256.ofNat dst :: ret :: R) mem aw rdata σ k C)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hsrcEnd : src + 32 + 32 * words.length ≤ dst) (hin : src + 32 + 32 * words.length ≤ mem.size)
    (hb : dst + 32 + 32 * words.length + 32 < UInt256.size)
    (hov : R.length + 13 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat (dst + 32 + 32 * words.length) :: R)
      (memoryBytesEncodedInto mem dst len words) aw' rdata σ k' C' := by
  have hlen : len ≤ 32 * words.length := by rw [hn]; omega
  have hsrc : UInt256.ofNat src + UInt256.ofNat 32 = UInt256.ofNat (src + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat src
  have hdst : UInt256.ofNat dst + UInt256.ofNat 32 = UInt256.ofNat (dst + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat dst
  have hd : (UInt256.ofNat dst).toNat = dst := ulit_toNat' _ (by omega)
  have h₁ := safeRuntime_block_9767 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_9767_stack, safeRuntime_block_9767_memory, hl, hsrc, hdst, hd] at h₁
  have h₂ := safeRuntime_block_9733 (by simp; omega) h₁
  have hw' := hw.writeAfter mem (src + 32) words hin dst (UInt256.ofNat len) (by omega)
  have hs : dst + 32 ≤ (writeWord mem dst (UInt256.ofNat len)).size := by
    rw [writeWord_sparse_size]; omega
  obtain ⟨aw', k', C', h₃⟩ := safeByteBufferCopyLoopInto words
    (i := 0) (src := src + 32) (dst := dst + 32) (len := len) h₂ (by simp; omega)
    (by simpa only [Nat.add_zero] using hw') (by simpa only [Nat.add_zero] using hs)
    (by omega) (by simpa only [Nat.zero_add] using hlen)
    (by intro hne; have hp := List.length_pos_iff.mpr hne; rw [hn] at hp ⊢; omega)
    (by omega)
  have h₄ := safeRuntime_block_9759 (by simp; omega) (by jump_dest) h₃
  have hwrite : (UInt256.ofNat len + UInt256.ofNat (dst + 32)).toNat = dst + 32 + len := by
    simpa only [Nat.add_comm] using
      (uadd_ofNat_toNat (a := len) (b := dst + 32) (by omega) (by omega) (by omega))
  simp only [safeRuntime_block_9759_stack, safeRuntime_block_9759_memory, hwrite] at h₄
  have h₅ := safeRuntime_block_9790 (by simp; omega) hret h₄
  have hmask : UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (UInt256.ofNat 31 + UInt256.ofNat len) = UInt256.ofNat (32 * words.length) := by
    rw [u256_add_comm]
    apply u256_inj
    change (returnReserveSize len).toNat = _
    rw [returnReserveSize_toNat (by omega), ulit_toNat' _ (by omega), hn]
    omega
  have hend : UInt256.ofNat 32 + (UInt256.ofNat (32 * words.length) + UInt256.ofNat dst) =
      UInt256.ofNat (dst + 32 + 32 * words.length) := by
    apply u256_inj
    rw [← u256_add_assoc,
      uadd3_ofNat_toNat (by omega) (by omega) (by omega) (by omega) (by omega),
      ulit_toNat' _ (by omega)]
    omega
  simp only [safeRuntime_block_9790_stack, hmask, hend] at h₅
  exact ⟨_, _, _, h₅⟩

set_option maxRecDepth 100000 in
theorem safeMemoryBytesEncode (words : List UInt256)
    {I g s0 σ k C aw mem rdata src dst len} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9767⟩
      (UInt256.ofNat src :: UInt256.ofNat dst :: ret :: R) mem aw rdata σ k C)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hm : mem.size ≤ dst) (hin : src + 32 + 32 * words.length ≤ mem.size)
    (hb : dst + 32 + 32 * words.length + 32 < UInt256.size)
    (hov : R.length + 13 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat (dst + 32 + 32 * words.length) :: R)
      (memoryBytesEncodedMemory mem dst len words) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeMemoryBytesEncodeInto words h hl hw hn (by omega)
    hin hb hov hret
  have hs : (writeWord mem dst (UInt256.ofNat len)).size = dst + 32 := by
    rw [writeWord_sparse_size]; omega
  refine ⟨aw', k', C', ?_⟩
  simpa only [memoryBytesEncodedInto, writeWords_atEnd _ _ _ hs,
    memoryBytesEncodedMemory] using hr

end Benchmarks.Safe

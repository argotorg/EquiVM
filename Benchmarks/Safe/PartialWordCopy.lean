import Benchmarks.Safe.WordBufferCopy
import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: only the final load's discarded bytes may overlap the destination.
def forwardCopyWords (mem : ByteArray) (src dst len : Nat) : List UInt256 :=
  let first := memLoad (UInt256.ofNat src) mem
  first :: memoryWords (writeWord mem dst first) (src + 32) ((len + 31) / 32 - 1)

theorem forwardCopyWords_length (mem : ByteArray) (src dst len : Nat) (hl : 32 ≤ len) :
    (forwardCopyWords mem src dst len).length = (len + 31) / 32 := by
  simp only [forwardCopyWords, List.length_cons, memoryWords_length]
  omega

theorem forwardCopyWords_payload (mem : ByteArray) (src dst len : Nat)
    (hl : 32 ≤ len) (hi : src + len ≤ mem.size) (ha : src + len ≤ dst)
    (hb : src < UInt256.size) :
    (wordBytes (forwardCopyWords mem src dst len)).extract 0 len =
      mem.readWithPadding src len := by
  let first := memLoad (UInt256.ofNat src) mem
  let m := writeWord mem dst first
  have hf : first.toByteArray = mem.readWithPadding src 32 := by
    dsimp [first]
    rw [memLoadReadWord, ulit_toNat' src hb]
    exact toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize mem src 32)
  have ht := memoryWords_prefix m (src + 32) (len - 32) ((len + 31) / 32 - 1)
    (by dsimp [m]; rw [writeWord_sparse_size]; omega) (by omega)
  rw [show wordBytes (forwardCopyWords mem src dst len) = first.toByteArray ++
      wordBytes (memoryWords m (src + 32) ((len + 31) / 32 - 1)) from rfl,
    extract_append_span _ _ 0 len (Nat.zero_le _) (by rw [toByteArray_size]; exact hl),
    byteArray_extract_self, toByteArray_size, ht,
    show m = writeWord mem dst first from rfl,
    writeWordReadBelow mem dst (src + 32) (len - 32) first (by omega) (by omega), hf]
  by_cases he : len = 32
  · simp only [he, Nat.sub_self, byteArray_readWithPadding_zero, ByteArray.append_empty]
  · rw [← byteArray_readWithPadding_split_unbounded _ _ 32 (len - 32) (by decide)
      (by omega) (by omega), Nat.add_sub_of_le hl]

def forwardCopyMemory (mem : ByteArray) (src dst len : Nat) : ByteArray :=
  writeWord (writeWords mem dst (forwardCopyWords mem src dst len)) (dst + len) ⟨0⟩

theorem forwardCopyMemory_size (mem : ByteArray) (src dst len : Nat) (hl : 32 ≤ len) :
    (forwardCopyMemory mem src dst len).size = max mem.size (dst + len + 32) := by
  rw [forwardCopyMemory, writeWord_sparse_size, writeWords_size_nonempty _ _ _ (by
    simp [forwardCopyWords]), forwardCopyWords_length _ _ _ _ hl]
  omega

theorem forwardCopyMemory_preserved (mem : ByteArray) (src dst len off count : Nat)
    (hin : off + count ≤ mem.size) (ha : off + count ≤ dst) :
    (forwardCopyMemory mem src dst len).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [forwardCopyMemory, writeWordReadBelow _ _ _ _ _ (by
      rw [writeWords_size_nonempty _ _ _ (by simp [forwardCopyWords])]; omega) (by omega),
    writeWords_readBelow _ _ _ _ _ hin ha]

theorem forwardCopyMemory_payload (mem : ByteArray) (src dst len : Nat)
    (hl : 32 ≤ len) (hi : src + len ≤ mem.size) (ha : src + len ≤ dst)
    (hb : src < UInt256.size) :
    (forwardCopyMemory mem src dst len).readWithPadding dst len =
      mem.readWithPadding src len := by
  have hlen := forwardCopyWords_length mem src dst len hl
  have hin : dst + 32 * (forwardCopyWords mem src dst len).length ≤
      (writeWords mem dst (forwardCopyWords mem src dst len)).size := by
    rw [writeWords_size_nonempty _ _ _ (by simp [forwardCopyWords])]
    omega
  rw [forwardCopyMemory, writeWordReadBelow _ _ _ _ _ (by rw [hlen] at hin; omega)
      (by omega), ← paddedReadPrefix _ _ _ (32 * (forwardCopyWords mem src dst len).length)
      hin (by rw [hlen]; omega), writeWords_read, forwardCopyWords_payload _ _ _ _ hl hi ha hb]

set_option maxRecDepth 100000 in
theorem safeForwardBytesCopy {I g s0 σ k C aw mem rdata src dst len}
    {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9733⟩
      (UInt256.ofNat src :: UInt256.ofNat dst :: UInt256.ofNat len :: ret :: R)
      mem aw rdata σ k C)
    (hl : 32 ≤ len) (hm : dst ≤ mem.size) (ha : src + len ≤ dst)
    (hb : dst + len + 64 < UInt256.size)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret R (forwardCopyMemory mem src dst len)
      aw' rdata σ k' C' := by
  let first := memLoad (UInt256.ofNat src) mem
  let m := writeWord mem dst first
  let words := memoryWords m (src + 32) ((len + 31) / 32 - 1)
  have hwords : words.length = (len + 31) / 32 - 1 := memoryWords_length _ _ _
  have h₀ := safeRuntime_block_9733 (by simp; omega) h
  have hlt : UInt256.lt ⟨0⟩ (UInt256.ofNat len) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' len (by omega)]; change 0 < len; omega)
  have h₁ := safeRuntime_block_9735_fallthrough (by simp; omega) (by rw [hlt]; decide) h₀
  obtain ⟨_, _, _, h₂⟩ := safeRuntime_block_9744_packed (by simp; omega) (by jump_dest) h₁
  simp only [safeRuntime_block_9744_stack, safeRuntime_block_9744_memory,
    u256_zero_add, ulit_toNat' dst (by omega)] at h₂
  change RD safeBytecode I g s0 ⟨9735⟩
    (UInt256.ofNat 32 :: UInt256.ofNat src :: UInt256.ofNat dst :: UInt256.ofNat len :: ret :: R)
    m _ rdata σ _ _ at h₂
  obtain ⟨_, _, _, h₃⟩ := safeByteBufferCopyLoopAfter words h₂ (by simp; omega)
    (memoryWords_view _ _ _) (by dsimp [m]; rw [writeWord_sparse_size]; omega)
    (by rw [hwords]; omega) (by rw [hwords]; omega)
    (by intro hn; have hh := List.length_pos_iff.mpr hn; rw [hwords] at hh ⊢; omega)
    (by rw [hwords]; omega)
  have h₄ := safeRuntime_block_9759 (by omega) hret h₃
  have hadd : (UInt256.ofNat len + UInt256.ofNat dst).toNat = dst + len := by
    simpa only [Nat.add_comm] using (uadd_ofNat_toNat (a := len) (b := dst)
      (by omega) (by omega) (by omega))
  simp only [safeRuntime_block_9759_stack, safeRuntime_block_9759_memory, hadd] at h₄
  exact ⟨_, _, _, h₄⟩

end Benchmarks.Safe

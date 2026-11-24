import Benchmarks.Safe.ViaIR.WordBufferCopy
import Benchmarks.Safe.ViaIR.MemoryBytesDecoded

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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

-- The IR copy loop uses bytes-object bases and returns the end of the padded destination.
set_option maxRecDepth 100000 in
theorem safeForwardBytesCopy {I g s0 σ k C aw mem rdata src dst len}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7384⟩
      (⟨0⟩ :: UInt256.ofNat src :: UInt256.ofNat dst :: ret :: UInt256.ofNat len :: R)
      mem aw rdata σ k C)
    (hl : 32 ≤ len) (hm : dst + 32 ≤ mem.size) (ha : src + len ≤ dst)
    (hb : dst + len + 96 < UInt256.size)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      (UInt256.ofNat (dst + 32 + 32 * ((len + 31) / 32)) :: R)
      (forwardCopyMemory mem (src + 32) (dst + 32) len) aw' rdata σ k' C' := by
  let first := memLoad (UInt256.ofNat (src + 32)) mem
  let m := writeWord mem (dst + 32) first
  let words := memoryWords m (src + 32 + 32) ((len + 31) / 32 - 1)
  have hwords : words.length = (len + 31) / 32 - 1 := memoryWords_length _ _ _
  have hlt : UInt256.lt ⟨0⟩ (UInt256.ofNat len) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' len (by omega)]; change 0 < len; omega)
  have h₁ := safeRuntime_block_7384_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h
  obtain ⟨_, _, _, h₂⟩ := safeRuntime_block_7416_packed (by simp; omega) (by jump_dest) h₁
  have hs : UInt256.ofNat src + UInt256.ofNat 32 = UInt256.ofNat (src + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat src
  have hd : (UInt256.ofNat dst + UInt256.ofNat 32).toNat = dst + 32 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [safeRuntime_block_7416_stack, safeRuntime_block_7416_memory,
    u256_add_zero, u256_zero_add, hs, hd] at h₂
  change RD fork safeBytecode I g s0 ⟨7384⟩
    (UInt256.ofNat 32 :: UInt256.ofNat src :: UInt256.ofNat dst :: ret :: UInt256.ofNat len :: R)
    m _ rdata σ _ _ at h₂
  obtain ⟨_, _, _, h₃⟩ := safeByteBufferCopyLoopAfter words h₂ (by simp; omega)
    (memoryWords_view _ _ _) (by dsimp [m]; rw [writeWord_sparse_size]; omega)
    (by rw [hwords]; omega) (by rw [hwords]; omega)
    (by intro hn; have hh := List.length_pos_iff.mpr hn; rw [hwords] at hh ⊢; omega)
    (by rw [hwords]; omega)
  obtain ⟨_, _, _, h₄⟩ := safeRuntime_block_7392_packed (by omega) hret h₃
  have hwrite : ((UInt256.ofNat dst + UInt256.ofNat len) + UInt256.ofNat 32).toNat =
      dst + 32 + len := by
    rw [uadd3_ofNat_toNat (by omega) (by omega) (by decide) (by omega) (by omega)]
    omega
  have hmask : UInt256.land (UInt256.ofNat len + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31)) = UInt256.ofNat (32 * ((len + 31) / 32)) := by
    rw [u256_land_comm]
    apply u256_inj
    change (returnReserveSize len).toNat = _
    rw [returnReserveSize_toNat (by omega), ulit_toNat' _ (by omega)]
    exact Nat.mul_comm _ _
  have hend : (UInt256.ofNat (32 * ((len + 31) / 32)) + UInt256.ofNat dst) +
      UInt256.ofNat 32 = UInt256.ofNat (dst + 32 + 32 * ((len + 31) / 32)) := by
    apply u256_inj
    rw [uadd3_ofNat_toNat (by omega) (by omega) (by decide) (by omega) (by omega),
      ulit_toNat' _ (by omega)]
    omega
  simp only [safeRuntime_block_7392_stack, safeRuntime_block_7392_memory,
    hmask, hend, hwrite] at h₄
  exact ⟨_, _, _, h₄⟩

end Benchmarks.Safe.ViaIR

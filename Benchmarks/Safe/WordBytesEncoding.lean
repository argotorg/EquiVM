import Benchmarks.Safe.MemoryBytesEncodingInto
import Benchmarks.Safe.MemoryBytesDecoded
import Benchmarks.Safe.Blocks.Runtime_051
import Benchmarks.Safe.Blocks.Runtime_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: the ABI tuple consisting of a static word and dynamic bytes.
def wordBytesArgsMemory (mem : ByteArray) (base len : Nat) (word : UInt256)
    (words : List UInt256) : ByteArray :=
  memoryBytesEncodedInto (writeWords mem base [word, ⟨64⟩]) (base + 64) len words

theorem wordBytesArgsMemory_size (mem : ByteArray) (base len : Nat) (word : UInt256)
    (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (wordBytesArgsMemory mem base len word words).size = max mem.size (base + 128 + len) := by
  rw [wordBytesArgsMemory, memoryBytesEncodedInto_size _ _ _ _ hn,
    writeWords_size_nonempty _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil]
  omega

theorem wordBytesArgsMemory_preserved (mem : ByteArray) (base len off count : Nat)
    (word : UInt256) (words : List UInt256)
    (hin : off + count ≤ mem.size) (ha : off + count ≤ base) :
    (wordBytesArgsMemory mem base len word words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [wordBytesArgsMemory, memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by
    rw [writeWords_size_nonempty _ _ _ (by simp)]; omega) (by omega),
    writeWords_readBelow _ _ _ _ _ hin ha]

theorem wordBytesArgsMemory_read (mem : ByteArray) (base len : Nat) (word : UInt256)
    (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (wordBytesArgsMemory mem base len word words).readWithPadding base
      (96 + 32 * words.length) =
      wordBytes [word, ⟨64⟩, UInt256.ofNat len] ++ (wordBytes words).extract 0 len ++
        ByteArray.zeroes (32 * words.length - len) := by
  have hh : (wordBytesArgsMemory mem base len word words).readWithPadding base 64 =
      wordBytes [word, ⟨64⟩] := by
    rw [wordBytesArgsMemory, memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by
      rw [writeWords_size_nonempty _ _ _ (by simp)]; simp) (by omega)]
    exact writeWords_read mem base [word, ⟨64⟩]
  have ht : (wordBytesArgsMemory mem base len word words).readWithPadding (base + 64)
      (32 + 32 * words.length) =
      (UInt256.ofNat len).toByteArray ++ (wordBytes words).extract 0 len ++
        ByteArray.zeroes (32 * words.length - len) :=
    memoryBytesEncodedInto_read _ _ _ _ hn
  rw [show 96 + 32 * words.length = 64 + (32 + 32 * words.length) by omega,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [wordBytesArgsMemory_size _ _ _ _ _ hn, hn]; omega), hh, ht]
  simp only [wordBytes, ByteArray.append_empty, ByteArray.append_assoc]

set_option maxRecDepth 100000 in
theorem safeWordBytesEncode (words : List UInt256)
    {I g s0 σ k C aw mem rdata base src len} {word ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11810⟩
      (UInt256.ofNat base :: UInt256.ofNat src :: word :: ret :: R) mem aw rdata σ k C)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ base)
    (hb : base + 128 + 32 * words.length < UInt256.size)
    (hov : R.length + 19 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat (base + 96 + 32 * words.length) :: R)
      (wordBytesArgsMemory mem base len word words) aw' rdata σ k' C' := by
  have hadd (n : Nat) (hh : base + n < UInt256.size) :
      UInt256.ofNat base + UInt256.ofNat n = UInt256.ofNat (base + n) := by
    apply u256_inj
    rw [ulit_toNat' _ hh]
    exact uadd_ofNat_toNat (by omega) (by omega) hh
  let head := writeWords mem base [word, ⟨64⟩]
  have hm : safeRuntime_block_11810_memory (mem := mem) (x0 := UInt256.ofNat base)
      (x2 := word) = head := by
    simp only [safeRuntime_block_11810_memory, hadd 32 (by omega),
      ulit_toNat' base (by omega), ulit_toNat' (base + 32) (by omega),
      head, writeWords, Reasoning.Theory.writeWord]
    rfl
  have hload : memLoad (UInt256.ofNat src) head = UInt256.ofNat len := by
    rw [memLoadReadWord, ulit_toNat' src (by omega),
      writeWords_readBelow _ _ src 32 _ (by omega) (by omega),
      ← ulit_toNat' src (by omega), ← memLoadReadWord]
    exact hl
  have hwords : WordArrayMemory head (src + 32) words := by
    intro i hi
    rw [writeWords_readBelow _ _ _ _ _ (by omega) (by omega)]
    exact hw i hi
  have h₁ := safeRuntime_block_11810 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_11810_stack, hm, hadd 64 (by omega)] at h₁
  obtain ⟨_, _, _, h₂⟩ := safeMemoryBytesEncodeInto words h₁ hload hwords hn (by omega)
    (by dsimp [head]; rw [writeWords_size_nonempty _ _ _ (by simp)]; omega)
    (by omega) (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_9836 (by omega) hret h₂
  simp only [safeRuntime_block_9836_stack] at h₃
  rw [show base + 64 + 32 + 32 * words.length = base + 96 + 32 * words.length by omega] at h₃
  exact ⟨_, _, _, h₃⟩

end Benchmarks.Safe

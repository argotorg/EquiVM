import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.MemoryPrefix
import Benchmarks.Midnight.RuntimeBlocks_090

/-! Allocation of the fixed eleven-byte SSTORE2 initialization prefix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def sstore2PrefixWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 116109857984291275695284211) (UInt256.ofNat 168)

def sstore2PrefixMemory (mem : ByteArray) (root : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem 64 (root + UInt256.ofNat 64))
    root.toNat (UInt256.ofNat 11)) (root.toNat + 32) sstore2PrefixWord

theorem sstore2PrefixMemory_prefix (mem : ByteArray) (root : UInt256) :
    MemoryPrefix mem (sstore2PrefixMemory mem root) root.toNat := by
  exact (memoryPrefix_writeWord _ 64 _ _ (Or.inr (by decide))).trans
    ((memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))).trans
      (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))))

theorem sstore2PrefixMemory_size (mem : ByteArray) (root : UInt256) :
    root.toNat + 64 ≤ (sstore2PrefixMemory mem root).size := by
  simp only [sstore2PrefixMemory, writeWord_sparse_size]
  omega

theorem sstore2PrefixMemory_free (mem : ByteArray) {root : UInt256} (hroot : 96 ≤ root.toNat) :
    memLoad (UInt256.ofNat 64) (sstore2PrefixMemory mem root) = root + UInt256.ofNat 64 := by
  rw [sstore2PrefixMemory, memLoad_writeWord_preserved, memLoad_writeWord_preserved]
  · exact memLoad_writeWord mem (UInt256.ofNat 64) _
  · rw [writeWord_sparse_size]; change 64 + 32 ≤ _; omega
  · left; change 64 + 32 ≤ _; omega
  · simp only [writeWord_sparse_size]; change 64 + 32 ≤ _; omega
  · left; change 64 + 32 ≤ _; omega

theorem sstore2PrefixMemory_length (mem : ByteArray) (root : UInt256) :
    memLoad root (sstore2PrefixMemory mem root) = UInt256.ofNat 11 := by
  rw [sstore2PrefixMemory, memLoad_writeWord_preserved]
  · exact memLoad_writeWord _ root _
  · rw [writeWord_sparse_size]; omega
  · exact Or.inl le_rfl

theorem sstore2PrefixMemory_bytes (mem : ByteArray) (root : UInt256) :
    (sstore2PrefixMemory mem root).readWithPadding (root.toNat + 32) 11 =
      Model.sstore2Prefix := by
  change (Reasoning.Theory.writeWord _ (root.toNat + 32) sstore2PrefixWord).readWithPadding
    ((root.toNat + 32) + 0) 11 = _
  rw [writeWord_sparse_read_window _ _ _ _ _ (by decide) (by decide) (by decide)]
  decide +kernel

set_option maxRecDepth 2000000 in
theorem midnightSstore2Prefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {σ : AccountMap} {aw root ret : UInt256} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hbound : root.toNat + 64 < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨24347⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ret (root :: R)
      (sstore2PrefixMemory mem root) aw' rdata σ k' C' := by
  have he : allocationEnd root (UInt256.ofNat 64) = root + UInt256.ofNat 64 := rfl
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat 64)) = ⟨0⟩ :=
    allocationCheck_bounded (by decide) (by simpa using hbound)
  have rd1 := midnightBlocks.midnight_block_24347 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_24347_stack, hfree] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate
    (by simp only [List.length_cons]; omega) hc (by jump_dest) rd1
  have rd3 := midnightBlocks.midnight_block_24362 (by omega) hret rd2
  simp only [midnightBlocks.midnight_block_24362_stack,
    midnightBlocks.midnight_block_24362_memory, he,
    uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega)] at rd3
  exact ⟨_, _, _, rd3⟩

end Benchmarks.Midnight

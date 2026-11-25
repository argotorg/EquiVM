import Benchmarks.Midnight.Sstore2Prefix
import Benchmarks.Midnight.AllocationAccounting

variable {fork : Ethereum.Fork}

/-! Memory accounting for the fixed SSTORE2 initialization prefix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightSstore2Prefix_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {σ : AccountMap} {aw root ret : UInt256} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hbound : root.toNat + 64 < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨24347⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryAccounting (sstore2PrefixMemory mem root) aw' C' ∧
      RD fork midnightBytecode I g s0 ret (root :: R)
      (sstore2PrefixMemory mem root) aw' rdata σ k' C' := by
  have he : allocationEnd root (UInt256.ofNat 64) = root + UInt256.ofNat 64 := rfl
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat 64)) = ⟨0⟩ :=
    allocationCheck_bounded (by decide) (by simpa using hbound)
  have rd1 := midnightBlocks.midnight_block_24347 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_24347_stack, hfree] at rd1
  have ha1 := memoryAccountingAt rd1 (by memory_account ha)
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightAllocate_accounted
    (by simp only [List.length_cons]; omega) hc (by jump_dest) ha1 rd1
  have rd3 := midnightBlocks.midnight_block_24362 (by omega) hret rd2
  have ha3 := memoryAccountingAt rd3 (by
    unfold midnightBlocks.midnight_block_24362_memory
    memory_account ha2)
  have hr := And.intro ha3 rd3
  simp only [midnightBlocks.midnight_block_24362_stack,
    midnightBlocks.midnight_block_24362_memory, he,
    uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega)] at hr
  exact ⟨_, _, _, hr⟩

end Benchmarks.Midnight

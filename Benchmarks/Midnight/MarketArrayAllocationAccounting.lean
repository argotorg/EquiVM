import Benchmarks.Midnight.ToMarketArrayAllocation
import Benchmarks.Midnight.AllocationAccounting

variable {fork : Ethereum.Fork}

/-! Allocating the pointer array used by the calldata market decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataArrayAllocation_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr n header finish : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hptr : ptr.toNat < 2^64) (hn : n.toNat < 2^64) (hheader : header.toNat < 2^128)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18684⟩
      (UInt256.ofNat (pointerArrayAllocation n.toNat) :: n :: header :: finish :: R)
      mem aw rdata σ k C) :
    (¬ ptr.toNat + pointerArrayAllocation n.toNat < 2^64 ∧ RDrev fork midnightBytecode g s0) ∨
    (finish.toNat < header.toNat + 32 + 128 * n.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (ptr.toNat + pointerArrayAllocation n.toNat < 2^64 ∧
      header.toNat + 32 + 128 * n.toNat ≤ finish.toNat ∧
      ∃ aw' k' C', MemoryAccounting (marketArrayMemory mem ptr n) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨18726⟩
        ((ptr + UInt256.ofNat 32) :: finish :: (UInt256.ofNat 32 + header) ::
          UInt256.ofNat (header.toNat + 32 + 128 * n.toNat) :: ptr :: R)
        (marketArrayMemory mem ptr n) aw' rdata σ k' C') := by
  have hend := pointerArrayAllocation_end hn hptr
  have hnext : (ptr + UInt256.ofNat (pointerArrayAllocation n.toNat)).toNat =
      ptr.toNat + pointerArrayAllocation n.toNat :=
    uadd_word_ofNat_toNat _ _ (by change _ + (32 + 32 * n.toNat) < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_18684 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_18684_stack, hfree] at rd1
  have ha1 := memoryAccountingAt rd1 (by memory_account ha)
  by_cases hfit : ptr.toNat + pointerArrayAllocation n.toNat < 2^64
  · have hc : allocationCheck ptr (allocationEnd ptr (UInt256.ofNat (pointerArrayAllocation n.toNat))) =
        ⟨0⟩ := by
      rw [hend]
      exact allocationCheck_ok (by rw [hnext]; exact hfit) (by rw [hnext]; omega)
    obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightAllocate_accounted (by simp only [List.length_cons]; omega)
      hc (by jump_dest) ha1 rd1
    rw [hend] at rd2 ha2
    have hext := collateralEnd_toNat hheader hn
    have hextWord := collateralEnd_eq hheader hn
    by_cases hbound : header.toNat + 32 + 128 * n.toNat ≤ finish.toNat
    · right; right
      refine ⟨hfit, hbound, ?_⟩
      have hg : UInt256.gt ((header + UInt256.shiftLeft n (UInt256.ofNat 7)) + UInt256.ofNat 32)
          finish = ⟨0⟩ := ugt_zero (by rw [hext]; exact hbound)
      have rd3 := midnightBlocks.midnight_block_18698_fallthrough (by omega) hg rd2
      have ha3 := memoryAccountingAt rd3 (by
        unfold midnightBlocks.midnight_block_18698_fallthrough_memory
        memory_account ha2)
      simp only [midnightBlocks.midnight_block_18698_fallthrough_stack,
        midnightBlocks.midnight_block_18698_fallthrough_memory, hextWord] at rd3 ha3
      have rd4 := midnightBlocks.midnight_block_18722 (by simp only [List.length_cons]; omega) rd3
      have ha4 := memoryAccountingAt rd4 (by memory_account ha3)
      exact ⟨_, _, _, ha4, rd4⟩
    · right; left
      refine ⟨by omega, ?_⟩
      have hg : UInt256.gt ((header + UInt256.shiftLeft n (UInt256.ofNat 7)) + UInt256.ofNat 32)
          finish = ⟨1⟩ := ugt_one (by rw [hext]; omega)
      have rd3 := midnightBlocks.midnight_block_18698_taken (by omega)
        (by rw [hg]; decide) (by jump_dest) rd2
      exact midnightBlocks.midnight_block_6350 (by
        simp only [midnightBlocks.midnight_block_18698_taken_stack, List.length_cons]; omega) rd3
  · left
    refine ⟨hfit, ?_⟩
    apply midnightAllocateRevert (by simp only [List.length_cons]; omega) _ rd1
    rw [hend]
    exact allocationCheck_large (by rw [hnext]; omega) (by rw [hnext]; omega)

end Benchmarks.Midnight

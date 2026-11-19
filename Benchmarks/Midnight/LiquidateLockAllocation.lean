import Benchmarks.Midnight.DynamicLockMemory
import Benchmarks.Midnight.AllocationBudget
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.LiquidateLoop

/-! Allocate and encode the transient lock key after liquidation's collateral loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateLockAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root id borrower budgetRoot : UInt256} {credit : Nat}
    {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hcanon : borrower.toNat < EVM.addressModulus)
    (hroot : root.toNat + 128 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5358⟩
      ([x0, x1, x2, x3, x4, x5, x6, x7, borrower] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot credit (dynamicLockMemory mem root id borrower) aw' C' ∧
      RD midnightBytecode I g s0 ⟨5442⟩
        ([root, x0, x1, x2, x3, x4, x5, x6, x7, borrower] ++ R)
        (dynamicLockMemory mem root id borrower) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_5358 (R := R) (by omega) (by jump_dest) rd
  have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_5358_memory
    transfer_budget hb)
  have hmem : midnightBlocks.midnight_block_5358_memory (mem := mem) (x8 := borrower) =
      dynamicLockHashMemory mem root id borrower := by
    simp only [midnightBlocks.midnight_block_5358_memory, hfree, hid,
      addressMask_computed, solcAddrMask_clean hcanon, writeWord_fold,
      dynamicLockHashMemory, writeWordArray]
    rw [uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega),
      uadd_word_ofNat_toNat root 64 (by change _ < 2^256; omega),
      uadd_word_ofNat_toNat root 96 (by change _ < 2^256; omega)]
    rfl
  rw [hmem] at rd1 hb1
  simp only [hfree] at hb1
  simp only [midnightBlocks.midnight_block_5358_stack, hfree] at rd1
  obtain ⟨aw2, k2, C2, hb2, rd2⟩ := midnightAllocate_budget
    (ptr := root) (size := UInt256.ofNat 128) (ret := UInt256.ofNat 5442)
    (R := [root, x0, x1, x2, x3, x4, x5, x6, x7, borrower] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (allocationCheck_bounded (ptr := root) (size := UInt256.ofNat 128)
      (by decide) (by exact hroot)) (by jump_dest) hb1 rd1
  have hend : allocationEnd root (UInt256.ofNat 128) = root + UInt256.ofNat 128 := by
    unfold allocationEnd
    congr 1
  rw [hend] at hb2 rd2
  exact ⟨aw2, k2, C2, hb2, rd2⟩

end Benchmarks.Midnight

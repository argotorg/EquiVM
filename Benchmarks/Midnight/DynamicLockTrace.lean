import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.DynamicLockMemory
import Benchmarks.Midnight.AllocationFunding
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.RuntimeBlocks_086
import Benchmarks.Midnight.RuntimeBlocks_089

variable {fork : Ethereum.Fork}

/-! Read a liquidation lock, optionally clearing it, at an arbitrary allocated heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightDynamicLock {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root id user ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (clear : Bool) (hstack : R.length + 10 ≤ 1024)
    (hcanon : user.toNat < EVM.addressModulus) (hroot : root.toNat + 128 < 2^64)
    (hlo : 96 ≤ root.toNat) (hperm : clear = true → I.perm = true)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 (if clear then ⟨24160⟩ else ⟨23150⟩)
      (id :: user :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (dynamicLockMemory mem root id user) aw' C' ∧
      RD fork midnightBytecode I g s0 ret
        (codeOwnerTransientWord I σ (lockSlot liquidationLockBase id user) :: R)
        (dynamicLockMemory mem root id user) aw' rdata
        (if clear then tstoreAccountMap I.codeOwner σ (lockSlot liquidationLockBase id user) ⟨0⟩
          else σ) k' C' := by
  have hm : midnightBlocks.midnight_block_23150_memory (mem := mem) (x0 := id) (x1 := user) =
      dynamicLockHashMemory mem root id user := by
    simp only [midnightBlocks.midnight_block_23150_memory, hfree,
      addressMask_computed, solcAddrMask_clean hcanon]
    rw [uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega),
      uadd_word_ofNat_toNat root 64 (by change _ < 2^256; omega),
      uadd_word_ofNat_toNat root 96 (by change _ < 2^256; omega)]
    simp only [dynamicLockHashMemory, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]
    rfl
  have head : ∃ aw1 k1 C1, MemoryFunding credit (dynamicLockHashMemory mem root id user) aw1 C1 ∧
      RD fork midnightBytecode I g s0 ⟨18444⟩
        ([root, ⟨128⟩, if clear then ⟨24239⟩ else ⟨23229⟩, root,
          root + UInt256.ofNat 32, ret] ++ R)
        (dynamicLockHashMemory mem root id user) aw1 rdata σ k1 C1 := by
    cases clear with
    | false =>
      have rd1 := midnightBlocks.midnight_block_23150
        (by simp only [List.length_cons]; omega) (by jump_dest) rd
      have ha1 := memoryFundingAt (credit := credit) rd1 (by
        unfold midnightBlocks.midnight_block_23150_memory
        memory_fund ha)
      rw [hm] at rd1 ha1
      simp only [midnightBlocks.midnight_block_23150_stack, hfree] at rd1 ha1
      exact ⟨_, _, _, ha1, rd1⟩
    | true =>
      have rd1 := midnightBlocks.midnight_block_24160
        (by simp only [List.length_cons]; omega) (by jump_dest) rd
      have ha1 := memoryFundingAt (credit := credit) rd1 (by
        unfold midnightBlocks.midnight_block_24160_memory
        memory_fund ha)
      change midnightBlocks.midnight_block_24160_memory (mem := mem) (x0 := id) (x1 := user) = _ at hm
      rw [hm] at rd1 ha1
      simp only [midnightBlocks.midnight_block_24160_stack, hfree] at rd1 ha1
      exact ⟨_, _, _, ha1, rd1⟩
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := head
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightAllocate_funded
    (R := root :: (root + UInt256.ofNat 32) :: ret :: R)
    (by simp only [List.length_cons]; omega)
    (allocationCheck_bounded (by decide) hroot) (by cases clear <;> jump_dest) ha1 rd1
  have he : allocationEnd root (⟨128⟩ : UInt256) = root + UInt256.ofNat 128 := rfl
  rw [he] at rd2 ha2
  change MemoryFunding credit (dynamicLockMemory mem root id user) aw2 C2 at ha2
  change RD fork midnightBytecode I g s0 (if clear then ⟨24239⟩ else ⟨23229⟩)
    (root :: (root + UInt256.ofNat 32) :: ret :: R)
    (dynamicLockMemory mem root id user) aw2 rdata σ k2 C2 at rd2
  have hl := dynamicLockMemory_length mem id user hlo
  have hh := dynamicLockMemory_hash mem id user hlo (by change _ < 2^256; omega)
  cases clear with
  | false =>
    have rd3 := midnightBlocks.midnight_block_23229 (by omega) hret rd2
    have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
    simp only [midnightBlocks.midnight_block_23229_stack, hl, hh] at rd3 ha3
    exact ⟨_, _, _, ha3, rd3⟩
  | true =>
    have rd3 := midnightBlocks.midnight_block_24239 (by omega) (hperm rfl) hret rd2
    have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
    simp only [midnightBlocks.midnight_block_24239_stack, hl, hh] at rd3 ha3
    exact ⟨_, _, _, ha3, rd3⟩

end Benchmarks.Midnight

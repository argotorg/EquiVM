import Benchmarks.Midnight.FlashLoanCallbackDecode

variable {fork : Ethereum.Fork}

/-! The callback magic-value requirement and entry to the repayment loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightFlashLoanCallbackMagic {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw value : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨16380⟩ (value :: flashLoanMagic :: R)
      mem aw out σ k C) :
    (value ≠ flashLoanMagic ∧ RDrev fork midnightBytecode g s0) ∨
    (value = flashLoanMagic ∧ ∃ aw' k' C',
      MemoryFunding credit (flashLoanMagicMemory mem) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨16403⟩ (⟨0⟩ :: R)
        (flashLoanMagicMemory mem) aw' out σ k' C') := by
  have hm : memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32) = flashLoanMagic := by
    rw [flashLoanMagic_copy, flashLoanMagic_load]
  by_cases he : value = flashLoanMagic
  · have rd1 := midnightBlocks.midnight_block_16380_fallthrough hstack
      (by change UInt256.sub value (memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32)) = ⟨0⟩
          rw [hm]; exact u256_sub_eq_zero_iff_eq.mpr he) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnightBlocks.midnight_block_16380_fallthrough_memory
      memory_fund ha)
    have rd2 := midnightBlocks.midnight_block_16402 (by change R.length + 1 ≤ 1024; omega) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    have hf := And.intro ha2 rd2
    simp only [midnightBlocks.midnight_block_16402_stack,
      midnightBlocks.midnight_block_16380_fallthrough_stack,
      midnightBlocks.midnight_block_16380_fallthrough_memory,
      show (UInt256.ofNat 24513).toNat = 24513 from rfl,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, flashLoanMagic_copy] at hf
    exact Or.inr ⟨he, _, _, _, hf⟩
  · have rd1 := midnightBlocks.midnight_block_16380_taken hstack
      (by change UInt256.sub value (memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32)) ≠ ⟨0⟩
          rw [hm]; exact fun h ↦ he (u256_sub_eq_zero_iff_eq.mp h)) (by jump_dest) rd
    exact Or.inl ⟨he, midnightBlocks.midnight_block_16459
      (by change R.length + 2 ≤ 1024; omega) rd1⟩

end Benchmarks.Midnight

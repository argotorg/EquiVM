import Benchmarks.Midnight.RepayCallbackDecode

variable {fork : Ethereum.Fork}

/-! The repayment callback magic-value requirement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayCallbackMagic {budgetRoot : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw value : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (ha : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10237⟩ (value :: flashLoanMagic :: R)
      mem aw out σ k C) :
    (value ≠ flashLoanMagic ∧ RDrev fork midnightBytecode g s0) ∨
    (value = flashLoanMagic ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit (flashLoanMagicMemory mem) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨10259⟩ R
        (flashLoanMagicMemory mem) aw' out σ k' C') := by
  have hm : memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32) = flashLoanMagic := by
    rw [flashLoanMagic_copy, flashLoanMagic_load]
  by_cases he : value = flashLoanMagic
  · have rd1 := midnightBlocks.midnight_block_10237_fallthrough hstack
      (by change UInt256.sub value (memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32)) = ⟨0⟩
          rw [hm]; exact u256_sub_eq_zero_iff_eq.mpr he) rd
    have ha1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1 (by
      unfold midnightBlocks.midnight_block_10237_fallthrough_memory
      transfer_budget ha)
    have hf := And.intro ha1 rd1
    simp only [midnightBlocks.midnight_block_10237_fallthrough_stack,
      midnightBlocks.midnight_block_10237_fallthrough_memory,
      show (UInt256.ofNat 24513).toNat = 24513 from rfl,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, flashLoanMagic_copy] at hf
    exact Or.inr ⟨he, _, _, _, hf⟩
  · have rd1 := midnightBlocks.midnight_block_10237_taken hstack
      (by change UInt256.sub value (memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32)) ≠ ⟨0⟩
          rw [hm]; exact fun h ↦ he (u256_sub_eq_zero_iff_eq.mp h)) (by jump_dest) rd
    exact Or.inl ⟨he, midnightBlocks.midnight_block_10268
      (by change R.length + 2 ≤ 1024; omega) rd1⟩

end Benchmarks.Midnight

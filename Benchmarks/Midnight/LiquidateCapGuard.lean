import Benchmarks.Midnight.LiquidateThresholdTrace

/-! Compare the actual repayment with the cap, reading its reserved memory word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCapGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw repaid cap lif price pos dp dl borrower badDebt receiver mode selector
      root : UInt256} {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : memLoad (UInt256.ofNat 608) mem = repaid)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7134⟩
      ([cap, lif, price, pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
      mem aw rdata σ k C) :
    (cap.toNat < repaid.toNat ∧ ∃ aw' k' C', TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨7188⟩
        ([price, lif, cap, ⟨0⟩, pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
        mem aw' rdata σ k' C') ∨
    (repaid.toNat ≤ cap.toNat ∧ ∃ aw' k' C', TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨6744⟩
        ([selector, selector, selector, selector, pos, dp, dl, borrower, badDebt, receiver,
          mode, selector] ++ R) mem aw' rdata σ k' C') := by
  by_cases hlt : cap.toNat < repaid.toNat
  · have hg : UInt256.gt (memLoad (UInt256.ofNat 608) mem) cap = ⟨1⟩ := by rw [hm]; exact ugt_one hlt
    have rd1 := midnightBlocks.midnight_block_7134_taken
      (R := [pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hg]; decide) (by jump_dest) rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
    simp only [midnightBlocks.midnight_block_7134_taken_stack, hg,
      show UInt256.isZero ⟨1⟩ = (⟨0⟩ : UInt256) from rfl] at rd1
    exact Or.inl ⟨hlt, _, _, _, hb1, rd1⟩
  · have hle : repaid.toNat ≤ cap.toNat := Nat.le_of_not_gt hlt
    have hg : UInt256.gt (memLoad (UInt256.ofNat 608) mem) cap = ⟨0⟩ := by rw [hm]; exact ugt_zero hle
    have rd1 := midnightBlocks.midnight_block_7134_fallthrough
      (R := [pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hg rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
    simp only [midnightBlocks.midnight_block_7134_fallthrough_stack, hg,
      show UInt256.isZero ⟨0⟩ = (⟨1⟩ : UInt256) from rfl] at rd1
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightLiquidateRcfFinish (R := R) (by omega) (by decide) rd1
    exact Or.inr ⟨hle, _, k2, C2, hb1.mono hc2, rd2⟩

end Benchmarks.Midnight

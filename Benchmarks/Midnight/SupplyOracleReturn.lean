import Benchmarks.Midnight.OracleReturnTrace
import Benchmarks.Midnight.AllocationBudget
import Benchmarks.Midnight.RuntimeBlocks_065

variable {fork : Ethereum.Fork}

/-! Oracle return decoding for supply collateral, with the caller's budget retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyOracleReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root base budgetRoot : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (success : Bool)
    (hstack : R.length + 11 ≤ 1024) (hout : out.size < UInt256.size)
    (hroot : root.toNat + 32 < 2^64)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨17264⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: base :: R) mem aw out σ k C) :
    ((success = false ∨ out.size < 32) ∧ RDrev fork midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit (writeWord mem 64 (root + UInt256.ofNat 32)) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨17274⟩ (UInt256.ofNat 255 :: base :: R)
        (writeWord mem 64 (root + UInt256.ofNat 32)) aw' out σ k' C') := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hout
  cases success with
  | false =>
    have rd1 := midnightBlocks.midnight_block_17264_taken
      (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd
    exact Or.inl ⟨Or.inl rfl, midnightBlocks.midnight_block_13748
      (by simp only [List.length_cons]; omega)
      (by rw [hn]; change 0 + out.size ≤ out.size; omega) rd1⟩
  | true =>
    have rd1 := midnightBlocks.midnight_block_17264_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) rd
    have rd2 := midnightBlocks.midnight_block_17270_taken
      (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_17270_taken_stack] at rd2
    by_cases hshort : out.size < 32
    · have rd3 := midnightBlocks.midnight_block_17485_taken
        (by omega)
        (by rw [ugt_one (by rw [hn]; exact hshort)]; decide) (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_17528
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_17498
        (by simp only [List.length_cons]; omega) (by jump_dest) rd4
      obtain ⟨aw6, k6, C6, rd6⟩ := midnightAllocate
        (by simp only [List.length_cons]; omega)
        (allocationCheck_bounded (by rw [hn]; change _ < 2^256; omega)
          (by rw [hn]; omega)) (by jump_dest) rd5
      have hc : UInt256.slt (UInt256.sub (root + UInt256.ofNat out.size) root) ⟨32⟩ ≠ ⟨0⟩ := by
        rw [word_add_sub_left]
        have hlo : ¬ (UInt256.ofNat out.size).toNat ≥ 2^255 := by rw [hn]; omega
        simp only [UInt256.slt, UInt256.sltBool, hlo, if_false,
          show ¬ (⟨32⟩ : UInt256).toNat ≥ 2^255 from by decide]
        have hl : UInt256.ofNat out.size < (⟨32⟩ : UInt256) := by
          change (UInt256.ofNat out.size).toNat < 32
          rw [hn]; exact hshort
        rw [decide_eq_true hl]
        decide
      have rd7 := midnightBlocks.midnight_block_17511_taken
        (by simp only [List.length_cons]; omega) hc (by jump_dest) rd6
      exact Or.inl ⟨Or.inr hshort, midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_17511_taken_stack, List.length_cons]; omega) rd7⟩
    · have h32 : 32 ≤ out.size := by omega
      have rd3 := midnightBlocks.midnight_block_17485_fallthrough
        (by omega)
        (ugt_zero (by rw [hn]; exact h32)) rd2
      have rd4 := midnightBlocks.midnight_block_17498
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have hb4 := transferBudgetAt (root := budgetRoot) (credit := credit) rd4
        (by transfer_budget hb)
      obtain ⟨aw5, k5, C5, hb5, rd5⟩ := midnightAllocate_budget
        (by simp only [List.length_cons]; omega)
        (allocationCheck_bounded (by decide) hroot) (by jump_dest) hb4 rd4
      have he : allocationEnd root (UInt256.ofNat 32) = root + UInt256.ofNat 32 := rfl
      rw [he] at rd5 hb5
      have rd6 := midnightBlocks.midnight_block_17511_fallthrough
        (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left]; decide) rd5
      have rd7 := midnightBlocks.midnight_block_17520
        (by omega) (by jump_dest) rd6
      exact Or.inr ⟨rfl, h32, _, _, _, hb5.mono (by omega), rd7⟩

end Benchmarks.Midnight

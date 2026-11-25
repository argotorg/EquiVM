import Benchmarks.Midnight.AllocationBudget
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.OracleMemory
import Benchmarks.Midnight.RuntimeBlocks_031
import Benchmarks.Midnight.RuntimeBlocks_032

variable {fork : Ethereum.Fork}

/-! Decode the one-word oracle reply used in a liquidation loop iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateOracleReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root maxDebt cp badDebt reverseRep rep budgetRoot : UInt256}
    {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256} (success : Bool)
    (hstack : R.length + 15 ≤ 1024) (hout : out.size < UInt256.size)
    (hroot : root.toNat + 32 < 2^64) (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨7933⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: maxDebt :: cp :: badDebt :: reverseRep :: rep :: root :: R)
      mem aw out σ k C) :
    ((success = false ∨ out.size < 32) ∧ RDrev fork midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit (writeWord mem 64 (root + UInt256.ofNat 32)) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨8252⟩
        (root :: cp :: badDebt :: reverseRep :: rep :: maxDebt :: R)
        (writeWord mem 64 (root + UInt256.ofNat 32)) aw' out σ k' C') := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hout
  cases success with
  | false =>
    have rd1 := midnightBlocks.midnight_block_7933_taken (by omega)
      (by decide) (by jump_dest) rd
    exact Or.inl ⟨Or.inl rfl, midnightBlocks.midnight_block_6362
      (by simp only [midnightBlocks.midnight_block_7933_taken_stack, List.length_cons]; omega)
      (by rw [hz, hn]; change 0 + out.size ≤ out.size; omega) rd1⟩
  | true =>
    have rd1 := midnightBlocks.midnight_block_7933_fallthrough (by omega) (by decide) rd
    have rd2 := midnightBlocks.midnight_block_7940_taken (by omega)
      (by decide) (by jump_dest) rd1
    by_cases hshort : out.size < 32
    · have rd3 := midnightBlocks.midnight_block_8216_taken (by omega)
        (by rw [ugt_one (by rw [hn]; exact hshort)]; decide) (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_8259
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_8230
        (by simp only [List.length_cons]; omega) (by jump_dest) rd4
      obtain ⟨aw6, k6, C6, rd6⟩ := midnightAllocate
        (by simp only [List.length_cons]; omega)
        (allocationCheck_bounded (by rw [hn]; change _ < 2^256; omega)
          (by rw [hn]; omega)) (by jump_dest) rd5
      have hc : UInt256.slt (UInt256.sub (root + UInt256.ofNat out.size) root) ⟨32⟩ ≠ ⟨0⟩ := by
        rw [word_add_sub_left]
        change UInt256.slt (UInt256.ofNat out.size) (UInt256.ofNat 32) ≠ ⟨0⟩
        rw [slt_lit_one_low (m := 32) (by decide) (by rw [hn]; exact hshort)]
        decide
      have rd7 := midnightBlocks.midnight_block_8243_taken
        (by simp only [List.length_cons]; omega) hc (by jump_dest) rd6
      exact Or.inl ⟨Or.inr hshort, midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_8243_taken_stack, List.length_cons]; omega) rd7⟩
    · have h32 : 32 ≤ out.size := by omega
      have rd3 := midnightBlocks.midnight_block_8216_fallthrough (by omega)
        (ugt_zero (by rw [hn]; exact h32)) rd2
      have rd4 := midnightBlocks.midnight_block_8230
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have hb4 := transferBudgetAt (root := budgetRoot) (credit := credit) rd4
        (by transfer_budget hb)
      obtain ⟨aw5, k5, C5, hb5, rd5⟩ := midnightAllocate_budget
        (by simp only [List.length_cons]; omega)
        (allocationCheck_bounded (by decide) hroot) (by jump_dest) hb4 rd4
      have he : allocationEnd root (UInt256.ofNat 32) = root + UInt256.ofNat 32 := rfl
      rw [he] at rd5 hb5
      have rd6 := midnightBlocks.midnight_block_8243_fallthrough
        (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left]; decide) rd5
      exact Or.inr ⟨rfl, h32, _, _, _, hb5.mono (by omega), rd6⟩

end Benchmarks.Midnight

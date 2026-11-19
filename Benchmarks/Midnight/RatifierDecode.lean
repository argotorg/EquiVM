import Benchmarks.Midnight.FlashLoanMagicMemory
import Benchmarks.Midnight.AllocationFunding
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.RuntimeBlocks_043
import Benchmarks.Midnight.RuntimeBlocks_044
import Benchmarks.Midnight.RuntimeBlocks_055

/-! Ratifier call failure and bytes32 decoding before its acknowledgement check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRatifierDecode {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (success : Bool)
    (hstack : R.length + 11 ≤ 1024) (hout : out.size < UInt256.size)
    (hroot : root.toNat + 32 < 2^64) (hlower : 128 ≤ root.toNat)
    (hmem : root.toNat + 32 ≤ mem.size)
    (hread : 32 ≤ out.size → memLoad root mem = calldataWord out 0)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11379⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R) mem aw out σ k C) :
    ((success = false ∨ out.size < 32) ∧ RDrev midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ ∃ aw' k' C',
      MemoryFunding credit
        (flashLoanMagicMemory (writeWord mem 64 (root + UInt256.ofNat 32))) aw' C' ∧
      RD midnightBytecode I g s0 ⟨11391⟩ (calldataWord out 0 :: flashLoanMagic :: R)
        (flashLoanMagicMemory (writeWord mem 64 (root + UInt256.ofNat 32))) aw' out σ k' C') := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hout
  cases success with
  | false =>
    have rd1 := midnightBlocks.midnight_block_11379_taken
      (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd
    exact Or.inl ⟨Or.inl rfl, midnightBlocks.midnight_block_13748
      (by simp only [List.length_cons]; omega)
      (by rw [hn]; change 0 + out.size ≤ out.size; omega) rd1⟩
  | true =>
    have rd1 := midnightBlocks.midnight_block_11379_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) rd
    have rd2 := midnightBlocks.midnight_block_11385_taken
      (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_11385_taken_stack] at rd2
    by_cases hshort : out.size < 32
    · have rd3 := midnightBlocks.midnight_block_14796_taken
        (by omega)
        (by rw [ugt_one (by rw [hn]; exact hshort)]; decide) (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_14851
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_14809
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
      have rd7 := midnightBlocks.midnight_block_14822_taken
        (by simp only [List.length_cons]; omega) hc (by jump_dest) rd6
      exact Or.inl ⟨Or.inr hshort, midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_14822_taken_stack, List.length_cons]; omega) rd7⟩
    · have h32 : 32 ≤ out.size := by omega
      have rd3 := midnightBlocks.midnight_block_14796_fallthrough
        (by omega)
        (ugt_zero (by rw [hn]; exact h32)) rd2
      have rd4 := midnightBlocks.midnight_block_14809
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha)
      obtain ⟨aw5, k5, C5, ha5, rd5⟩ := midnightAllocate_funded
        (by simp only [List.length_cons]; omega)
        (allocationCheck_bounded (by decide) hroot) (by jump_dest) ha4 rd4
      have he : allocationEnd root (UInt256.ofNat 32) = root + UInt256.ofNat 32 := rfl
      rw [he] at rd5 ha5
      have rd6 := midnightBlocks.midnight_block_14822_fallthrough
        (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left]; decide) rd5
      have rd7 := midnightBlocks.midnight_block_14831
        (by omega) (by jump_dest) rd6
      have ha7 := memoryFundingAt (credit := credit) rd7 (by
        unfold midnightBlocks.midnight_block_14831_memory
        memory_fund ha5)
      have hsize : root.toNat + 32 ≤
          (writeWord mem 64 (root + UInt256.ofNat 32)).size := by
        rw [writeWord_sparse_size]; omega
      have hread' : memLoad root
          (flashLoanMagicMemory (writeWord mem 64 (root + UInt256.ofNat 32))) =
          calldataWord out 0 := by
        rw [flashLoanMagicMemory_load _ _ (by omega) hsize,
          memLoad_writeWord_preserved _ _ _ _ hmem (Or.inr (by omega)), hread h32]
      have hf := And.intro ha7 rd7
      simp only [midnightBlocks.midnight_block_14831_stack,
        midnightBlocks.midnight_block_14831_memory,
        show (UInt256.ofNat 24513).toNat = 24513 from rfl,
        show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl] at hf
      simp only [flashLoanMagic_copy, flashLoanMagic_load] at hf
      change MemoryFunding credit
          (flashLoanMagicMemory (writeWord mem 64 (root + UInt256.ofNat 32))) _ _ ∧
        RD _ _ _ _ _
          (memLoad root (flashLoanMagicMemory (writeWord mem 64 (root + UInt256.ofNat 32))) ::
            flashLoanMagic :: R) _ _ _ _ _ _ at hf
      rw [hread'] at hf
      exact Or.inr ⟨rfl, h32, _, _, _, hf⟩

end Benchmarks.Midnight

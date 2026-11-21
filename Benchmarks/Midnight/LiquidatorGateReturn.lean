import Benchmarks.Midnight.AllocationBudget
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.BoolMemoryDecode
import Benchmarks.Midnight.RuntimeBlocks_032
import Benchmarks.Midnight.RuntimeBlocks_033

/-! The liquidator gate's return-data length and Boolean canonicality checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: a memory-only charge preserves a fixed buffer's transfer budget.
theorem TransferBudget.charge {root : UInt256} {credit : Nat} {mem : ByteArray}
    {aw aw' : UInt256} {C C' : Nat} (hb : TransferBudget root credit mem aw C)
    (hc : MemoryCharge 0 aw aw' C C') : TransferBudget root credit mem aw' C' := by
  rcases hb with hsmall | ⟨halign, hf⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨halign, by
      simpa only [Nat.add_zero] using hc.funding hf (hf.covered.mono hc.active_le)⟩

theorem midnightLiquidatorGateReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root budgetRoot : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (success : Bool)
    (hstack : R.length + 10 ≤ 1024) (hout : out.size < UInt256.size)
    (hroot : root.toNat + 32 < 2^64)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hword : 32 ≤ out.size →
      memLoad root (writeWord mem 64 (root + UInt256.ofNat 32)) = calldataWord out 0)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨8342⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R) mem aw out σ k C) :
    ((success = false ∨ ¬ (32 ≤ out.size ∧
        (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩))) ∧
      RDrev midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧
      (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit (writeWord mem 64 (root + UInt256.ofNat 32)) aw' C' ∧
      RD midnightBytecode I g s0 ⟨8398⟩ (calldataWord out 0 :: R)
        (writeWord mem 64 (root + UInt256.ofNat 32)) aw' out σ k' C') := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hout
  cases success with
  | false =>
    have rd1 := midnight_block_8342_taken (by (try simp only [List.length_cons]); omega)
      (by decide) (by jump_dest) rd
    exact Or.inl ⟨Or.inl rfl, midnight_block_6362
      (by simp only [midnight_block_8342_taken_stack, List.length_cons]; omega)
      (by rw [hz, hn]; change 0 + out.size ≤ out.size; omega) rd1⟩
  | true =>
    have rd1 := midnight_block_8342_fallthrough (by (try simp only [List.length_cons]); omega)
      (by decide) rd
    have rd2 := midnight_block_8349_taken (by (try simp only [List.length_cons]); omega)
      (by decide) (by jump_dest) rd1
    by_cases hshort : out.size < 32
    · have rd3 := midnight_block_8364_taken (by (try simp only [List.length_cons]); omega)
        (by rw [ugt_one (by rw [hn]; exact hshort)]; decide) (by jump_dest) rd2
      have rd4 := midnight_block_8404 (by (try simp only [List.length_cons]); omega) (by jump_dest) rd3
      have rd5 := midnight_block_8380 (by (try simp only [List.length_cons]); omega) (by jump_dest) rd4
      obtain ⟨aw6, k6, C6, rd6⟩ := midnightAllocate (by (try simp only [List.length_cons]); omega)
        (allocationCheck_bounded (by rw [hn]; change _ < 2^256; omega)
          (by rw [hn]; omega)) (by jump_dest) rd5
      have rd7 := midnight_block_8390 (by (try simp only [List.length_cons]); omega) (by jump_dest) rd6
      have hlen : UInt256.slt (UInt256.sub (root + UInt256.ofNat out.size) root) ⟨32⟩ ≠ ⟨0⟩ := by
        rw [word_add_sub_left]
        have hlo : ¬ (UInt256.ofNat out.size).toNat ≥ 2^255 := by rw [hn]; omega
        simp only [UInt256.slt, UInt256.sltBool, hlo, if_false,
          show ¬ (⟨32⟩ : UInt256).toNat ≥ 2^255 from by decide]
        have hl : UInt256.ofNat out.size < (⟨32⟩ : UInt256) := by
          change (UInt256.ofNat out.size).toNat < 32
          rw [hn]; exact hshort
        rw [decide_eq_true hl]
        decide
      exact Or.inl ⟨Or.inr (by omega), midnightBoolMemory_short
        (by (try simp only [List.length_cons]); omega) hlen rd7⟩
    · have h32 : 32 ≤ out.size := by omega
      have rd3 := midnight_block_8364_fallthrough (by (try simp only [List.length_cons]); omega)
        (ugt_zero (by rw [hn]; exact h32)) rd2
      have rd4 := midnight_block_8380 (by (try simp only [List.length_cons]); omega) (by jump_dest) rd3
      have hb4 := transferBudgetAt (root := budgetRoot) (credit := credit) rd4
        (by transfer_budget hb)
      obtain ⟨aw5, k5, C5, hb5, rd5⟩ := midnightAllocate_budget
        (by (try simp only [List.length_cons]); omega)
        (allocationCheck_bounded (by decide) hroot) (by jump_dest) hb4 rd4
      have he : allocationEnd root (UInt256.ofNat 32) = root + UInt256.ofNat 32 := rfl
      rw [he] at rd5 hb5
      have rd6 := midnight_block_8390 (by (try simp only [List.length_cons]); omega) (by jump_dest) rd5
      have hlen : UInt256.slt (UInt256.sub (root + UInt256.ofNat 32) root) ⟨32⟩ = ⟨0⟩ := by
        rw [word_add_sub_left]; decide
      by_cases hc : calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩
      · obtain ⟨aw7, k7, C7, hc7, rd7⟩ := midnightBoolMemory_cleanCharge
          (by (try simp only [List.length_cons]); omega) hlen
          (by rw [hword h32]; exact hc) (by jump_dest) rd6
        have hb6 := transferBudgetAt rd6 (hb5.mono (by omega))
        rw [hword h32] at rd7
        exact Or.inr ⟨rfl, h32, hc, _, _, _, hb6.charge hc7, rd7⟩
      · exact Or.inl ⟨Or.inr (by tauto), midnightBoolMemory_dirty
          (by (try simp only [List.length_cons]); omega) hlen
          (by rw [hword h32]; exact hc) rd6⟩

end Benchmarks.Midnight

import Benchmarks.Midnight.CheckedArithmetic

/-! Revert branches of the shared checked arithmetic routines. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem checkedMulGuard_overflow {a b : UInt256} (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul a b) a) b)
      (UInt256.isZero a)) = ⟨1⟩ := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hover
    change UInt256.size ≤ 0 * b.toNat at hover
    have hp : 0 < UInt256.size := by decide
    omega
  have hd : UInt256.div (UInt256.mul a b) a ≠ b := by
    rw [u256_mul_comm a b]
    exact u256_mul_div_right_overflow_ne b a (by simpa only [Nat.mul_comm] using hover)
  rw [u256_eq_of_ne hd, isZero_eq_zero_of_ne ha]
  rfl

theorem midnightCheckedMulRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hover : UInt256.size ≤ a.toNat * b.toNat)
    (rd : RD midnightBytecode I g s0 ⟨20413⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_20413_taken hstack
    (by rw [checkedMulGuard_overflow hover]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_7302 (by
    simp only [midnightBlocks.midnight_block_20413_taken_stack, List.length_cons]; omega) rd1

theorem midnightCheckedAddRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hover : UInt256.size ≤ a.toNat + b.toNat)
    (rd : RD midnightBytecode I g s0 ⟨19536⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have hc : UInt256.gt a (a + b) = ⟨1⟩ := by
    rw [u256_add_comm a b]
    exact u256_gt_add_right_of_overflow a b hover
  have rd1 := midnightBlocks.midnight_block_19536_taken hstack
    (by rw [hc]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_7302 (by
    simp only [midnightBlocks.midnight_block_19536_taken_stack, List.length_cons]; omega) rd1

theorem midnightCheckedDivRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨19391⟩ (a :: ⟨0⟩ :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_19391_taken (by simp only [List.length_cons]; omega)
    (by decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_19401 (by simp only [List.length_cons]; omega) rd1

end Benchmarks.Midnight

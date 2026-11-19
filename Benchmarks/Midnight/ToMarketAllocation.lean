import Benchmarks.Midnight.AllocationArithmetic

/-! Allocation of the decoded market record before its fields are read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr x finish anchor : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hptr : ptr.toNat < 2^64)
    (rd : RD midnightBytecode I g s0 ⟨949⟩ (finish :: x :: anchor :: R) mem aw rdata σ k C) :
    (¬ ptr.toNat + 256 < 2^64 ∧ RDrev midnightBytecode g s0) ∨
    (ptr.toNat + 256 < 2^64 ∧ ∃ aw' k' C', RD midnightBytecode I g s0 ⟨961⟩
      (x :: finish :: ptr :: anchor :: R) (writeWord mem 64 (ptr + UInt256.ofNat 256))
      aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_949
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_949_stack, hfree] at rd1
  have hp : (ptr + UInt256.ofNat 256).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  by_cases hfit : ptr.toNat + 256 < 2^64
  · right
    refine ⟨hfit, ?_⟩
    exact midnightAllocate256 (by simp only [List.length_cons]; omega)
      (allocationCheck_ok (by rw [hp]; exact hfit) (by rw [hp]; omega)) (by jump_dest) rd1
  · left
    refine ⟨hfit, ?_⟩
    exact midnightAllocate256Revert (by simp only [List.length_cons]; omega)
      (allocationCheck_large (by rw [hp]; omega) (by rw [hp]; omega)) rd1

end Benchmarks.Midnight

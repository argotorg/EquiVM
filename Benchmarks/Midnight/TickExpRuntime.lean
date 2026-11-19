import Benchmarks.Midnight.TickExpModel
import Benchmarks.Midnight.RuntimeBlocks_090

/-! Runtime paths of the exponential helper, with cumulative gas costs retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightWExp_nonnegative {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hpos : UInt256.isZero (UInt256.slt x ⟨0⟩) ≠ ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨24388⟩ (x :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ret (wExpPositiveWord x :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_24388_taken
    (by simp only [List.length_cons]; omega) hpos (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_24433 hstack hret rd1
  exact ⟨k + 7 + 31, C + 25 + 108, by omega, by
    simpa only [midnightBlocks.midnight_block_24433_stack, wExpPositiveWord] using rd2⟩

theorem midnightWExp_negative {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (hneg : UInt256.isZero (UInt256.slt x ⟨0⟩) = ⟨0⟩)
    (hpos : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ x) ⟨0⟩) ≠ ⟨0⟩)
    (hnz : wExpPositiveWord (UInt256.sub ⟨0⟩ x) ≠ ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨24388⟩ (x :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ret
        (UInt256.div (UInt256.ofNat 1000000000000000000000000000000000000)
          (wExpPositiveWord (UInt256.sub ⟨0⟩ x)) :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_24388_fallthrough
    (by simp only [List.length_cons]; omega) hneg rd
  have rd2 := midnightBlocks.midnight_block_24397
    (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_24397_stack] at rd2
  obtain ⟨k3, C3, hC3, rd3⟩ := midnightWExp_nonnegative
    (by simp only [List.length_cons]; omega) hpos (by jump_dest) rd2
  have rd4 := midnightBlocks.midnight_block_24407_fallthrough
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) rd3
  have rd5 := midnightBlocks.midnight_block_24414 (by omega) hret rd4
  exact ⟨k3 + 5 + 4, C3 + 20 + 19, by omega, by
    simpa only [midnightBlocks.midnight_block_24414_stack] using rd5⟩

end Benchmarks.Midnight

import Benchmarks.Midnight.CalldataArgumentSlice
import Benchmarks.Midnight.CalldataSliceTrace
import Benchmarks.Midnight.RuntimeBlocks_038

/-! The repayment callback's calldata slice, retaining its two decoded accounts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayDataRef {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD midnightBytecode I g s0 ⟨9792⟩ (x0 :: x1 :: R) mem aw rdata σ k C) :
    (¬ CalldataArgumentValid true I.calldata 132 ∧ RDrev midnightBytecode g s0) ∨
    (CalldataArgumentValid true I.calldata 132 ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨9832⟩
        (calldataArgumentLength I.calldata 132 :: calldataArgumentPointer I.calldata 132 ::
          solcAddrMask :: x1 :: x0 :: R) mem aw rdata σ k' C') := by
  by_cases ho : (calldataWord I.calldata 132).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata 132)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ :=
      ugt_zero (by change _ ≤ 2^64 - 1; omega)
    have rd1 := midnightBlocks.midnight_block_9792_fallthrough (by omega) hc rd
    have rd2 := midnightBlocks.midnight_block_9811
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_9811_stack, addressMask_computed] at rd2
    change RD midnightBytecode I g s0 ⟨18889⟩
      (calldataArgumentHead I.calldata 132 :: UInt256.ofNat I.calldata.size ::
        ⟨9832⟩ :: solcAddrMask :: x1 :: x0 :: R) mem aw rdata σ _ _ at rd2
    rcases midnightCalldataSlice true (by simp only [List.length_cons]; omega) hsize
        (by rw [calldataArgumentHead_toNat ho]; omega) (by jump_dest) rd2 with
      ⟨hn, hr⟩ | ⟨hv, k', C', hC, rd3⟩
    · exact Or.inl ⟨fun h ↦ hn h.2, hr⟩
    · exact Or.inr ⟨⟨ho, hv⟩, k', C', by omega, rd3⟩
  · have hc : UInt256.gt (calldataWord I.calldata 132)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    have rr := midnightBlocks.midnight_block_9792_taken (by omega) hc (by jump_dest) rd
    exact Or.inl ⟨fun h ↦ ho h.1, midnightBlocks.midnight_block_712
      (by simp only [midnightBlocks.midnight_block_9792_taken_stack, List.length_cons]; omega) rr⟩

end Benchmarks.Midnight

import Benchmarks.Midnight.CalldataArgumentSlice
import Benchmarks.Midnight.CalldataSliceTrace
import Benchmarks.Midnight.RuntimeBlocks_022

variable {fork : Ethereum.Fork}

/-! The liquidation callback's calldata reference. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateDataRef {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD fork midnightBytecode I g s0 ⟨5095⟩ R mem aw rdata σ k C) :
    (¬ CalldataArgumentValid true I.calldata 260 ∧ RDrev fork midnightBytecode g s0) ∨
    (CalldataArgumentValid true I.calldata 260 ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨5126⟩
        (calldataArgumentLength I.calldata 260 :: calldataArgumentPointer I.calldata 260 :: R)
        mem aw rdata σ k' C') := by
  by_cases ho : (calldataWord I.calldata 260).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata 260)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero (by change _ ≤ 2^64 - 1; omega)
    have rd1 := midnightBlocks.midnight_block_5095_fallthrough (by omega) hc rd
    have rd2 := midnightBlocks.midnight_block_5113 (by omega) (by jump_dest) rd1
    change RD fork midnightBytecode I g s0 ⟨18889⟩
      (calldataArgumentHead I.calldata 260 :: UInt256.ofNat I.calldata.size :: ⟨5126⟩ :: R)
      mem aw rdata σ _ _ at rd2
    rcases midnightCalldataSlice true hstack hsize
        (by rw [calldataArgumentHead_toNat ho]; omega) (by jump_dest) rd2 with
      ⟨hn, hr⟩ | ⟨hv, k', C', hC, rd3⟩
    · exact Or.inl ⟨fun h ↦ hn h.2, hr⟩
    · exact Or.inr ⟨⟨ho, hv⟩, k', C', by omega, rd3⟩
  · have hc : UInt256.gt (calldataWord I.calldata 260)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    have rr := midnightBlocks.midnight_block_5095_taken (by omega) hc (by jump_dest) rd
    exact Or.inl ⟨fun h ↦ ho h.1, midnightBlocks.midnight_block_712
      (by change R.length + 1 + 2 ≤ 1024; omega) rr⟩

end Benchmarks.Midnight

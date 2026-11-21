import Benchmarks.Midnight.CalldataArgumentSlice
import Benchmarks.Midnight.CalldataSliceTrace
import Benchmarks.Midnight.RuntimeBlocks_060

/-! Flash loan argument references, before the address-array elements are inspected. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightFlashLoanTokensRef {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hsize : I.calldata.size < UInt256.size)
    (rd : RD midnightBytecode I g s0 ⟨16050⟩ R mem aw rdata σ k C) :
    (¬ CalldataArgumentValid false I.calldata 4 ∧ RDrev midnightBytecode g s0) ∨
    (CalldataArgumentValid false I.calldata 4 ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨16080⟩
        (calldataArgumentLength I.calldata 4 :: calldataArgumentPointer I.calldata 4 :: R)
        mem aw rdata σ k' C') := by
  by_cases ho : (calldataWord I.calldata 4).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ :=
      ugt_zero (by change _ ≤ 2^64 - 1; omega)
    have rd1 := midnightBlocks.midnight_block_16050_fallthrough (by omega) hc rd
    have rd2 := midnightBlocks.midnight_block_16067 (by omega) (by jump_dest) rd1
    change RD midnightBytecode I g s0 ⟨18841⟩
      (calldataArgumentHead I.calldata 4 :: UInt256.ofNat I.calldata.size :: ⟨16080⟩ :: R)
      mem aw rdata σ _ _ at rd2
    rcases midnightCalldataSlice false hstack hsize
        (by rw [calldataArgumentHead_toNat ho]; omega) (by jump_dest) rd2 with
      ⟨hn, hr⟩ | ⟨hv, k', C', hC, rd3⟩
    · exact Or.inl ⟨fun h ↦ hn h.2, hr⟩
    · exact Or.inr ⟨⟨ho, hv⟩, k', C', by omega, rd3⟩
  · have hc : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    have rr := midnightBlocks.midnight_block_16050_taken (by omega) hc (by jump_dest) rd
    exact Or.inl ⟨fun h ↦ ho h.1, midnightBlocks.midnight_block_6350
      (by simp only [midnightBlocks.midnight_block_16050_taken_stack,
        List.length_cons]; omega) rr⟩

theorem midnightFlashLoanTailRef (isBytes : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD midnightBytecode I g s0 (if isBytes then ⟨16121⟩ else ⟨16080⟩)
      (x0 :: x1 :: R) mem aw rdata σ k C) :
    (¬ CalldataArgumentValid isBytes I.calldata (if isBytes then 100 else 36) ∧
      RDrev midnightBytecode g s0) ∨
    (CalldataArgumentValid isBytes I.calldata (if isBytes then 100 else 36) ∧
      ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 (if isBytes then ⟨16153⟩ else ⟨16112⟩)
        (calldataArgumentLength I.calldata (if isBytes then 100 else 36) ::
          calldataArgumentPointer I.calldata (if isBytes then 100 else 36) :: x1 :: x0 :: R)
        mem aw rdata σ k' C') := by
  let slot := if isBytes then 100 else 36
  by_cases ho : (calldataWord I.calldata slot).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata slot)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ :=
      ugt_zero (by change _ ≤ 2^64 - 1; omega)
    have rd1 : RD midnightBytecode I g s0 (if isBytes then ⟨16140⟩ else ⟨16099⟩)
        (calldataWord I.calldata slot :: x1 :: x0 :: R) mem aw rdata σ
        (k + 13) (C + 44) := by
      cases isBytes
      · exact midnightBlocks.midnight_block_16080_fallthrough (by omega) hc rd
      · exact midnightBlocks.midnight_block_16121_fallthrough (by omega) hc rd
    have rd2 : RD midnightBytecode I g s0 (if isBytes then ⟨18889⟩ else ⟨18841⟩)
        (calldataArgumentHead I.calldata slot :: UInt256.ofNat I.calldata.size ::
          (if isBytes then ⟨16153⟩ else ⟨16112⟩) :: x1 :: x0 :: R)
        mem aw rdata σ (k + 13 + 8) (C + 44 + 28) := by
      cases isBytes
      · exact midnightBlocks.midnight_block_16099
          (by simp only [List.length_cons]; omega) (by jump_dest) rd1
      · exact midnightBlocks.midnight_block_16140
          (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    rcases midnightCalldataSlice isBytes
        (by simp only [List.length_cons]; omega) hsize
        (by rw [calldataArgumentHead_toNat ho]; omega)
        (by cases isBytes <;> jump_dest) rd2 with
      ⟨hn, hr⟩ | ⟨hv, k', C', hC, rd3⟩
    · exact Or.inl ⟨fun h ↦ hn h.2, hr⟩
    · exact Or.inr ⟨⟨ho, hv⟩, k', C', by omega, rd3⟩
  · have hc : UInt256.gt (calldataWord I.calldata slot)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    left
    refine ⟨fun h ↦ ho h.1, ?_⟩
    cases isBytes
    · have rr := midnightBlocks.midnight_block_16080_taken (by omega) hc (by jump_dest) rd
      exact midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_16080_taken_stack,
          List.length_cons]; omega) rr
    · have rr := midnightBlocks.midnight_block_16121_taken (by omega) hc (by jump_dest) rd
      exact midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_16121_taken_stack,
          List.length_cons]; omega) rr

end Benchmarks.Midnight

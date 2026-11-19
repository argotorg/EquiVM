import Benchmarks.Midnight.CalldataSliceBounds
import Benchmarks.Midnight.RuntimeBlocks_071
import Benchmarks.Midnight.RuntimeBlocks_072

/-! The shared calldata reference decoders for scalar arrays and bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCalldataSlice (isBytes : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size) (hhead : head.toNat < 2^128)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 (if isBytes then ⟨18889⟩ else ⟨18841⟩)
      (head :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    (¬ CalldataSliceValid isBytes I.calldata head ∧ RDrev midnightBytecode g s0) ∨
    (CalldataSliceValid isBytes I.calldata head ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ret
        (calldataWord I.calldata head.toNat :: (head + UInt256.ofNat 32) :: R)
        mem aw rdata σ k' C') := by
  by_cases hh : I.calldata.size < 2^255 ∧ head.toNat + 32 ≤ I.calldata.size
  · have hc : UInt256.isZero
        (UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat I.calldata.size)) = ⟨0⟩ := by
      rw [calldataSliceHeaderCheck hhead hsize, decide_eq_true hh]
      rfl
    have rd1 : RD midnightBytecode I g s0 (if isBytes then ⟨18902⟩ else ⟨18854⟩)
        (ret :: UInt256.ofNat I.calldata.size :: head :: R)
        mem aw rdata σ (k + 10) (C + 35) := by
      cases isBytes
      · exact midnightBlocks.midnight_block_18841_fallthrough (by omega) hc rd
      · exact midnightBlocks.midnight_block_18889_fallthrough (by omega) hc rd
    let len := calldataWord I.calldata head.toNat
    by_cases hn : len.toNat < 2^64
    · have hlen : UInt256.gt len
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
            (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero (by change len.toNat ≤ 2^64 - 1; omega)
      have rd2 : RD midnightBytecode I g s0 (if isBytes then ⟨18919⟩ else ⟨18871⟩)
          (UInt256.ofNat I.calldata.size :: ret :: len :: head :: R)
          mem aw rdata σ (k + 10 + 12) (C + 35 + 43) := by
        cases isBytes
        · exact midnightBlocks.midnight_block_18854_fallthrough (by omega) hlen rd1
        · exact midnightBlocks.midnight_block_18902_fallthrough (by omega) hlen rd1
      have hend := calldataSliceEnd_toNat isBytes hhead hn
      by_cases he : head.toNat + 32 + calldataSliceStride isBytes * len.toNat ≤ I.calldata.size
      · have hgt : UInt256.gt (calldataSliceEndWord isBytes head len)
            (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
          ugt_zero (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; exact he)
        have rd3 : RD midnightBytecode I g s0 (if isBytes then ⟨18933⟩ else ⟨18888⟩)
            (ret :: len :: (head + UInt256.ofNat 32) :: R) mem aw rdata σ
            (k + 10 + 12 + (if isBytes then 11 else 13))
            (C + 35 + 43 + (if isBytes then 40 else 46)) := by
          cases isBytes
          · exact midnightBlocks.midnight_block_18871_fallthrough hstack hgt rd2
          · exact midnightBlocks.midnight_block_18919_fallthrough hstack hgt rd2
        right
        refine ⟨⟨hh.1, hh.2, hn, he⟩, ?_⟩
        cases isBytes
        · have rd4 := midnightBlocks.midnight_block_18888
            (by simp only [List.length_cons]; omega) hret rd3
          exact ⟨_, _, by omega, rd4⟩
        · have rd4 := midnightBlocks.midnight_block_18933
            (by simp only [List.length_cons]; omega) hret rd3
          exact ⟨_, _, by omega, rd4⟩
      · left
        refine ⟨fun hv ↦ he hv.2.2.2, ?_⟩
        have hgt : UInt256.gt (calldataSliceEndWord isBytes head len)
            (UInt256.ofNat I.calldata.size) ≠ ⟨0⟩ := by
          rw [ugt_one (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; omega)]
          decide
        cases isBytes
        · have rr := midnightBlocks.midnight_block_18871_taken hstack hgt (by jump_dest) rd2
          exact midnightBlocks.midnight_block_6350
            (by simp only [midnightBlocks.midnight_block_18871_taken_stack,
                List.length_cons]; omega) rr
        · have rr := midnightBlocks.midnight_block_18919_taken hstack hgt (by jump_dest) rd2
          exact midnightBlocks.midnight_block_6350
            (by simp only [midnightBlocks.midnight_block_18919_taken_stack,
                List.length_cons]; omega) rr
    · left
      refine ⟨fun hv ↦ hn hv.2.2.1, ?_⟩
      have hlen : UInt256.gt len
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
            (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
        rw [ugt_one (by change 2^64 - 1 < len.toNat; omega)]
        decide
      cases isBytes
      · have rr := midnightBlocks.midnight_block_18854_taken (by omega) hlen (by jump_dest) rd1
        exact midnightBlocks.midnight_block_6350
          (by simp only [midnightBlocks.midnight_block_18854_taken_stack,
              List.length_cons]; omega) rr
      · have rr := midnightBlocks.midnight_block_18902_taken (by omega) hlen (by jump_dest) rd1
        exact midnightBlocks.midnight_block_6350
          (by simp only [midnightBlocks.midnight_block_18902_taken_stack,
              List.length_cons]; omega) rr
  · left
    refine ⟨fun hv ↦ hh ⟨hv.1, hv.2.1⟩, ?_⟩
    have hc : UInt256.isZero
        (UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat I.calldata.size)) ≠ ⟨0⟩ := by
      rw [calldataSliceHeaderCheck hhead hsize, decide_eq_false hh]
      decide
    cases isBytes
    · have rr := midnightBlocks.midnight_block_18841_taken (by omega) hc (by jump_dest) rd
      exact midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_18841_taken_stack,
            List.length_cons]; omega) rr
    · have rr := midnightBlocks.midnight_block_18889_taken (by omega) hc (by jump_dest) rd
      exact midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_18889_taken_stack,
            List.length_cons]; omega) rr

end Benchmarks.Midnight

import Benchmarks.Midnight.CalldataAddress
import Benchmarks.Midnight.ToMarketFirstFields

variable {fork : Ethereum.Fork}

/-! The first fields and dynamic offset of a market calldata record. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataFirstFields {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret finish : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hhead : head.toNat + 256 < UInt256.size) (hptr : ptr.toNat + 256 < UInt256.size)
    (rd : RD fork midnightBytecode I g s0 ⟨18601⟩ (head :: ptr :: ret :: finish :: R)
      mem aw rdata σ k C) :
    (decodeMarketData I.calldata head.toNat = none ∧ RDrev fork midnightBytecode g s0) ∨
    ((calldataWord I.calldata (head.toNat + 32)).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata (head.toNat + 64)).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata (head.toNat + 96)).toNat < 2^64 ∧ ∃ aw' k' C',
      RD fork midnightBytecode I g s0 ⟨18661⟩
        (calldataWord I.calldata (head.toNat + 96) :: finish :: head :: ptr :: ret :: ptr :: R)
        (marketFirstMemory mem ptr I.calldata head.toNat) aw' rdata σ k' C') := by
  have hh32 := uadd_word_ofNat_toNat head 32 (by omega)
  have hh64 := uadd_word_ofNat_toNat head 64 (by omega)
  have hh96 := uadd_word_ofNat_toNat head 96 (by omega)
  have hp32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hp64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have rd1 := midnightBlocks.midnight_block_18601 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_18601_stack] at rd1
  by_cases hm : (calldataWord I.calldata (head.toNat + 32)).toNat < EVM.addressModulus
  · obtain ⟨k2, C2, rd2⟩ := midnightCalldataAddress_ok
      (by simp only [List.length_cons]; omega) (by rw [hh32]; exact hm) (by jump_dest) rd1
    rw [hh32] at rd2
    have rd3 := midnightBlocks.midnight_block_18619 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_18619_stack] at rd3
    by_cases hl : (calldataWord I.calldata (head.toNat + 64)).toNat < EVM.addressModulus
    · obtain ⟨k4, C4, rd4⟩ := midnightCalldataAddress_ok
        (by simp only [List.length_cons]; omega) (by rw [hh64]; exact hl) (by jump_dest) rd3
      rw [hh64] at rd4
      by_cases hoff : (calldataWord I.calldata (head.toNat + 96)).toNat < 2^64
      · right
        refine ⟨hm, hl, hoff, ?_⟩
        have hg : UInt256.gt (calldataWord I.calldata (head + UInt256.ofNat 96).toNat)
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
              (UInt256.ofNat 1)) = ⟨0⟩ := by
          rw [hh96]
          apply ugt_zero
          change _ ≤ 18446744073709551615
          omega
        have rd5 := midnightBlocks.midnight_block_18636_fallthrough (by
          simp only [List.length_cons]; omega) hg rd4
        simp only [midnightBlocks.midnight_block_18636_fallthrough_stack, hh96] at rd5
        have hmem : midnightBlocks.midnight_block_18636_fallthrough_memory
            (mem := midnightBlocks.midnight_block_18619_memory
              (mem := midnightBlocks.midnight_block_18601_memory (ee := I) (mem := mem)
                (x0 := head) (x1 := ptr))
              (x0 := calldataWord I.calldata (head.toNat + 32)) (x3 := ptr))
            (x0 := calldataWord I.calldata (head.toNat + 64)) (x3 := ptr) =
            marketFirstMemory mem ptr I.calldata head.toNat := by
          simp only [midnightBlocks.midnight_block_18636_fallthrough_memory,
            midnightBlocks.midnight_block_18619_memory, midnightBlocks.midnight_block_18601_memory,
            hp32, hp64, marketFirstMemory, marketFirstWords, writeWordArray,
            Nat.add_assoc, Nat.reduceAdd]
          rfl
        rw [hmem] at rd5
        exact ⟨_, _, _, rd5⟩
      · left
        refine ⟨?_, ?_⟩
        · have hc : solcMaxU64 < (calldataWord I.calldata (head.toNat + 96)).toNat := by
            change 18446744073709551615 < _; omega
          simp [decodeMarketData, hc]
        · have hg : UInt256.gt (calldataWord I.calldata (head + UInt256.ofNat 96).toNat)
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
                (UInt256.ofNat 1)) = ⟨1⟩ := by
            rw [hh96]
            apply ugt_one
            change 18446744073709551615 < _
            omega
          have rd5 := midnightBlocks.midnight_block_18636_taken (by
            simp only [List.length_cons]; omega) (by rw [hg]; decide) (by jump_dest) rd4
          exact midnightBlocks.midnight_block_6350 (by
            simp only [midnightBlocks.midnight_block_18636_taken_stack, List.length_cons]; omega) rd5
    · left
      refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, hl], ?_⟩
      exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [hh64]; exact hl) rd3
  · left
    refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, hm], ?_⟩
    exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
      (by rw [hh32]; exact hm) rd1

end Benchmarks.Midnight

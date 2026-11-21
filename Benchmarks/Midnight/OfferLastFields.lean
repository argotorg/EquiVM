import Benchmarks.Midnight.OfferTailFields
import Benchmarks.Midnight.CalldataArgumentSlice

/-! Store the final offer caps and check the ratifier-data offset. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def offerLastWords (bytes : ByteArray) (base : Nat) : List UInt256 :=
  [calldataWord bytes (base + 416), calldataWord bytes (base + 448)]

def offerLastMemory (mem bytes : ByteArray) (base : Nat) : ByteArray :=
  writeWordArray mem 1248 (offerLastWords bytes base)

theorem midnightOfferLastFields {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw rel : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hrel : rel.toNat < 2^64) (hm : 416 ≤ mem.size)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10795⟩
      (calldataWord I.calldata (rel.toNat + 420) :: rel :: ⟨452⟩ :: R) mem aw rdata σ k C) :
    (decodeCalldataBytes I.calldata 36 = none ∧ RDrev midnightBytecode g s0) ∨
    ((calldataWord I.calldata 36).toNat < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding credit (offerLastMemory mem I.calldata (rel.toNat + 4)) aw' C' ∧
        RD midnightBytecode I g s0 ⟨10833⟩ (calldataWord I.calldata 36 :: R)
          (offerLastMemory mem I.calldata (rel.toNat + 4)) aw' rdata σ k' C') := by
  by_cases ho : (calldataWord I.calldata 36).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := by
      apply ugt_zero
      change _ ≤ 2^64 - 1
      omega
    have rd1 := midnightBlocks.midnight_block_10795_fallthrough (by omega) hc rd
    simp (disch := first | assumption | decide +kernel |
      (simp only [writeWord_fold, writeWord_sparse_size]; omega)) only
      [midnightBlocks.midnight_block_10795_fallthrough_stack,
        midnightBlocks.midnight_block_10795_fallthrough_memory, offerRoot_writeBytes, hroot] at rd1
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    have hadd : (rel + (⟨452⟩ : UInt256)).toNat = rel.toNat + 452 :=
      uadd_word_ofNat_toNat rel 452 (by change _ < 2^256; omega)
    rw [hadd] at ha1 rd1
    right
    refine ⟨ho, ?_⟩
    simp only [offerLastMemory, offerLastWords, writeWordArray, Nat.add_assoc, Nat.reduceAdd]
    exact ⟨_, _, _, ha1, rd1⟩
  · left
    refine ⟨by simp only [decodeCalldataBytes, ho, if_false], ?_⟩
    have hc : UInt256.gt (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    have rr := midnightBlocks.midnight_block_10795_taken (by omega) hc (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by
      simp only [midnightBlocks.midnight_block_10795_taken_stack, List.length_cons]; omega) rr

end Benchmarks.Midnight

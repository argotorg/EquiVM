import Benchmarks.Midnight.OfferDecodeFacts
import Benchmarks.Midnight.AllocationAccounting
import Benchmarks.Midnight.RuntimeBlocks_040

variable {fork : Ethereum.Fork}

/-! The external offer header, fixed record allocation, and nested market pointer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def offerPrepareMemory (mem : ByteArray) : ByteArray :=
  writeWord (writeWord mem 384 ⟨832⟩) 64 ⟨1312⟩

theorem offerPrepareMemory_size {mem : ByteArray} (hm : 832 ≤ mem.size) :
    (offerPrepareMemory mem).size = mem.size := by
  rw [offerPrepareMemory, writeWord_sparse_size, writeWord_sparse_size]
  omega

theorem offerPrepareMemory_free (mem : ByteArray) :
    memLoad (UInt256.ofNat 64) (offerPrepareMemory mem) = ⟨1312⟩ :=
  memLoad_writeWord _ _ _

theorem offerPrepareMemory_root (mem : ByteArray) :
    memLoad (UInt256.ofNat 384) (offerPrepareMemory mem) = ⟨832⟩ := by
  rw [offerPrepareMemory, memLoad_writeWord_preserved _ 64 (UInt256.ofNat 384) _
    (by rw [writeWord_sparse_size]; change 416 ≤ _; omega) (Or.inr (by decide))]
  exact memLoad_writeWord mem (UInt256.ofNat 384) _

theorem midnightOfferPrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10425⟩ R mem aw rdata σ k C) :
    (decodeCalldataOffer I.calldata 4 = none ∧ RDrev fork midnightBytecode g s0) ∨
    ((calldataWord I.calldata 4).toNat < 2^64 ∧
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (calldataWord I.calldata 4) +
        UInt256.lnot (UInt256.ofNat 3)) (UInt256.ofNat 480) = UInt256.ofNat 0 ∧
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 2^64 ∧
      ∃ aw' k' C', MemoryAccounting (offerPrepareMemory mem) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨18574⟩
          ((calldataWord I.calldata 4 +
              calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) + UInt256.ofNat 4) ::
            UInt256.ofNat I.calldata.size :: ⟨10530⟩ :: calldataWord I.calldata 4 :: R)
          (offerPrepareMemory mem) aw' rdata σ k' C') := by
  by_cases ho : (calldataWord I.calldata 4).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := by
      apply ugt_zero
      change _ ≤ 2^64 - 1
      omega
    have rd1 := midnightBlocks.midnight_block_10425_fallthrough (by omega) hc rd
    by_cases hh : UInt256.slt
        (UInt256.sub (UInt256.ofNat I.calldata.size) (calldataWord I.calldata 4) +
          UInt256.lnot (UInt256.ofNat 3)) (UInt256.ofNat 480) = UInt256.ofNat 0
    · have rd2 := midnightBlocks.midnight_block_10442_fallthrough (by omega) hh rd1
      have hstore : memLoad (UInt256.ofNat 384)
          ((⟨832⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32) = ⟨832⟩ :=
        memLoad_writeWord mem (UInt256.ofNat 384) _
      have rd3 := midnightBlocks.midnight_block_10457_fallthrough
        (by simp only [List.length_cons]; omega) (by
          simp only [hfree, hstore]
          decide +kernel) rd2
      have ha3 := memoryAccountingAt rd3 (by
        unfold midnightBlocks.midnight_block_10457_fallthrough_memory
        memory_account ha)
      simp only [midnightBlocks.midnight_block_10457_fallthrough_stack,
        midnightBlocks.midnight_block_10457_fallthrough_memory, hfree, hstore] at ha3 rd3
      have hhead := calldataArgumentHead_toNat ho
      change (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat = _ at hhead
      by_cases hm : (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 2^64
      · have hc4 : UInt256.gt
            (calldataWord I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat)
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
              (UInt256.ofNat 1)) = ⟨0⟩ := by
          rw [hhead]
          apply ugt_zero
          change _ ≤ 2^64 - 1
          omega
        have rd4 := midnightBlocks.midnight_block_10493_fallthrough (by omega) hc4 rd3
        have ha4 := memoryAccountingAt rd4 (by
          unfold midnightBlocks.midnight_block_10493_fallthrough_memory
          memory_account ha3)
        simp only [midnightBlocks.midnight_block_10493_fallthrough_stack,
          midnightBlocks.midnight_block_10493_fallthrough_memory, hhead] at ha4 rd4
        have rd5 := midnightBlocks.midnight_block_10515 (by omega) (by jump_dest) rd4
        have ha5 := memoryAccountingAt rd5 (by memory_account ha4)
        simp only [midnightBlocks.midnight_block_10515_stack] at rd5
        exact Or.inr ⟨ho, hh, hm, _, _, _, ha5, rd5⟩
      · left
        refine ⟨?_, ?_⟩
        · unfold decodeCalldataOffer
          dsimp only
          split
          · rfl
          · exact decodeOfferData_none_marketOffset hm
        · have hc4 : UInt256.gt
              (calldataWord I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat)
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
                (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
            rw [hhead, ugt_one (by change 2^64 - 1 < _; omega)]
            decide
          have rr := midnightBlocks.midnight_block_10493_taken (by omega) hc4 (by jump_dest) rd3
          exact midnightBlocks.midnight_block_6350 (by
            simp only [midnightBlocks.midnight_block_10493_taken_stack, List.length_cons]; omega) rr
    · left
      refine ⟨?_, ?_⟩
      · cases hd : decodeCalldataOffer I.calldata 4 with
        | none => rfl
        | some offer => exact False.elim (hh (decodeCalldataOffer_headerCheck hd))
      · have rr := midnightBlocks.midnight_block_10442_taken (by omega) hh (by jump_dest) rd1
        exact midnightBlocks.midnight_block_6350 (by simp only [List.length_cons]; omega) rr
  · left
    have hc : solcMaxU64 < (calldataWord I.calldata 4).toNat := by
      change 2^64 - 1 < _
      omega
    refine ⟨by simp only [decodeCalldataOffer, hc, true_or, if_true], ?_⟩
    have hg : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    have rr := midnightBlocks.midnight_block_10425_taken (by omega) hg (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by
      simp only [midnightBlocks.midnight_block_10425_taken_stack, List.length_cons]; omega) rr

end Benchmarks.Midnight

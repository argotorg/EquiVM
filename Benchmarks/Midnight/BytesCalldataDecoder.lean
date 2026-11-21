import Benchmarks.Midnight.BytesCalldataCopy
import Benchmarks.Midnight.RelativeBytesDecode
import Benchmarks.Midnight.AllocationFunding

/-! Materialized bytes decoding with every malformed and oversized allocation branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def bytesCalldataMemory (mem bytes : ByteArray) (ptr : UInt256) (head : Nat) : ByteArray :=
  calldataBytesEncodeMemory
    (writeWord mem 64 (returnDataPtr ptr (calldataWord bytes head).toNat)) bytes
    ptr.toNat (head + 32) (calldataWord bytes head).toNat

theorem midnightBytesCalldataDecoder_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw head ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hhead : head.toNat < 2^128) (hptr : ptr.toNat < 2^64)
    (hsize : I.calldata.size < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19043⟩
      (head :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    ((∀ data, decodeBytesAt I.calldata head.toNat = some data →
        ¬ ptr.toNat + returnDataAllocation data.size < 2^64) ∧
      RDrev midnightBytecode g s0) ∨
    (∃ data, decodeBytesAt I.calldata head.toNat = some data ∧
      ptr.toNat + returnDataAllocation data.size < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding (credit + 3 * ((data.size + 31) / 32))
          (bytesCalldataMemory mem I.calldata ptr head.toNat) aw' C' ∧
        RD midnightBytecode I g s0 ret (ptr :: R)
          (bytesCalldataMemory mem I.calldata ptr head.toNat) aw' rdata σ k' C') := by
  by_cases hh : I.calldata.size < 2^255 ∧ head.toNat + 32 ≤ I.calldata.size
  · have hc : UInt256.isZero
        (UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat I.calldata.size)) = ⟨0⟩ := by
      rw [calldataSliceHeaderCheck hhead hsize, decide_eq_true hh]
      rfl
    have rd1 := midnightBlocks.midnight_block_19043_fallthrough
      (by simp only [List.length_cons]; omega) hc rd
    have rd2 := midnightBlocks.midnight_block_19055
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_19055_stack] at rd2
    let len := calldataWord I.calldata head.toNat
    by_cases hn : len.toNat < 2^64
    · obtain ⟨k3, C3, hc3, rd3⟩ := midnightBytesAllocationSize_charge hn
        (by simp only [List.length_cons]; omega) (by jump_dest) rd2
      have ha3 : MemoryFunding credit mem aw C3 := ha.mono (by have := hc3.work_le; omega)
      have rd4 := midnightBlocks.midnight_block_19066
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha3)
      simp only [midnightBlocks.midnight_block_19066_stack, hfree] at rd4
      have hend : allocationEnd ptr (UInt256.ofNat (returnDataAllocation len.toNat)) =
          returnDataPtr ptr len.toNat := bytesAllocationEnd
        (by change len.toNat + 94 < 2^256; omega)
        (by change ptr.toNat + returnDataAllocation len.toNat < 2^256
            unfold returnDataAllocation; omega)
      have hp : (returnDataPtr ptr len.toNat).toNat =
          ptr.toNat + returnDataAllocation len.toNat :=
        uadd_word_ofNat_toNat _ _ (by
          change ptr.toNat + returnDataAllocation len.toNat < 2^256
          unfold returnDataAllocation; omega)
      by_cases hf : ptr.toNat + returnDataAllocation len.toNat < 2^64
      · have hc5 : allocationCheck ptr
            (allocationEnd ptr (UInt256.ofNat (returnDataAllocation len.toNat))) = ⟨0⟩ := by
          rw [hend]
          exact allocationCheck_ok (by rw [hp]; exact hf) (by rw [hp]; omega)
        obtain ⟨aw5, k5, C5, ha5, rd5⟩ := midnightAllocate_funded
          (by simp only [List.length_cons]; omega) hc5 (by jump_dest) ha4 rd4
        rw [hend] at ha5 rd5
        by_cases he : head.toNat + 32 + len.toNat ≤ I.calldata.size
        · obtain ⟨aw6, k6, C6, _, ha6, rd6⟩ := midnightBytesCalldataCopy_funded
            (by omega) hhead hn hptr hsize he hret ha5 rd5
          let data := I.calldata.extract (head.toNat + 32) (head.toNat + 32 + len.toNat)
          have hd : data.size = len.toNat := by
            dsimp only [data]
            rw [ByteArray.size_extract]
            omega
          right
          refine ⟨data, ?_, by rw [hd]; exact hf, aw6, k6, C6, ?_, ?_⟩
          · simp only [decodeBytesAt, show calldataWord I.calldata head.toNat = len from rfl,
              hh.1, hh.2, hn, he, and_self, if_true]
            rfl
          · simpa only [hd, bytesCalldataMemory] using ha6
          · exact rd6
        · left
          refine ⟨fun data hd ↦ False.elim
            (he (decodeBytesAt_success hd).2.2.2.1), ?_⟩
          have hew := calldataSliceEnd_toNat true hhead hn
          simp only [calldataSliceEndWord, calldataSliceStride, if_true, Nat.one_mul] at hew
          have hc6 : UInt256.gt (head + len + UInt256.ofNat 32)
              (UInt256.ofNat I.calldata.size) ≠ ⟨0⟩ := by
            rw [ugt_one (by rw [hew, UInt256.toNat_ofNat_of_lt hsize]; omega)]
            decide
          have rr := midnightBlocks.midnight_block_19080_taken
            (by simp only [List.length_cons]; omega) hc6 (by jump_dest) rd5
          exact midnightBlocks.midnight_block_6350 (by
            simp only [midnightBlocks.midnight_block_19080_taken_stack, List.length_cons]
            omega) rr
      · left
        refine ⟨fun data hd ↦ ?_, ?_⟩
        · rw [(decodeBytesAt_success hd).2.2.2.2.2]
          exact hf
        · apply midnightAllocateRevert (by simp only [List.length_cons]; omega) _ rd4
          rw [hend]
          exact allocationCheck_large (by rw [hp]; omega) (by rw [hp]; omega)
    · left
      refine ⟨fun data hd ↦ False.elim (hn (decodeBytesAt_success hd).2.2.1), ?_⟩
      exact midnightBytesLengthTooLarge (by change 2^64 ≤ len.toNat; omega)
        (by simp only [List.length_cons]; omega) rd2
  · left
    refine ⟨fun data hd ↦ False.elim
      (hh ⟨(decodeBytesAt_success hd).1, (decodeBytesAt_success hd).2.1⟩), ?_⟩
    have hc : UInt256.isZero
        (UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat I.calldata.size)) ≠ ⟨0⟩ := by
      rw [calldataSliceHeaderCheck hhead hsize, decide_eq_false hh]
      decide
    have rr := midnightBlocks.midnight_block_19043_taken
      (by simp only [List.length_cons]; omega) hc (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by simp only [List.length_cons]; omega) rr

end Benchmarks.Midnight

import Benchmarks.Midnight.CalldataScalarAccounting
import Benchmarks.Midnight.CollateralData

variable {fork : Ethereum.Fork}

/-! A collateral record copied from calldata into its allocated memory region. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCollateralCalldataCopy_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hhead : head.toNat + 128 < UInt256.size) (hptr : ptr.toNat + 128 < UInt256.size)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18524⟩ (ptr :: ret :: head :: R)
      mem aw rdata σ k C) :
    (¬ CollateralData.canonicalAt I.calldata head.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (CollateralData.canonicalAt I.calldata head.toNat ∧ ∃ aw' k' C',
      MemoryAccounting
        (writeWordArray mem ptr.toNat (CollateralData.at I.calldata head.toNat).words) aw' C' ∧
      RD fork midnightBytecode I g s0 ret (ptr :: R)
        (writeWordArray mem ptr.toNat (CollateralData.at I.calldata head.toNat).words)
        aw' rdata σ k' C') := by
  have hh32 := uadd_word_ofNat_toNat head 32 (by omega)
  have hh64 := uadd_word_ofNat_toNat head 64 (by omega)
  have hh96 := uadd_word_ofNat_toNat head 96 (by omega)
  have hp32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hp64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hp96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have rd1 := midnightBlocks.midnight_block_18524 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_18524_stack] at rd1
  have ha1 := memoryAccountingAt rd1 (by memory_account ha)
  by_cases ht : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus
  · obtain ⟨k2, C2, ha2, rd2⟩ := midnightCalldataAddress_ok_accounted
      (by simp only [List.length_cons]; omega) ht (by jump_dest) ha1 rd1
    have rd3 := midnightBlocks.midnight_block_18541 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd2
    have ha3 := memoryAccountingAt rd3 (by
      unfold midnightBlocks.midnight_block_18541_memory
      memory_account ha2)
    simp only [midnightBlocks.midnight_block_18541_stack] at rd3
    by_cases ho : (calldataWord I.calldata (head.toNat + 96)).toNat < EVM.addressModulus
    · have hc : CollateralData.canonicalAt I.calldata head.toNat := ⟨ht, ho⟩
      right
      refine ⟨hc, ?_⟩
      obtain ⟨k4, C4, ha4, rd4⟩ := midnightCalldataAddress_ok_accounted
        (by simp only [List.length_cons]; omega) (by rw [hh96]; exact ho)
        (by jump_dest) ha3 rd3
      have rd5 := midnightBlocks.midnight_block_18569 (by
        simp only [List.length_cons]; omega) hvalid rd4
      have ha5 := memoryAccountingAt rd5 (by
        unfold midnightBlocks.midnight_block_18569_memory
        memory_account ha4)
      have hm : midnightBlocks.midnight_block_18569_memory
          (mem := midnightBlocks.midnight_block_18541_memory (ee := I) (mem := mem)
            (x0 := calldataWord I.calldata head.toNat) (x1 := head) (x5 := ptr))
          (x0 := calldataWord I.calldata (head + UInt256.ofNat 96).toNat)
          (x1 := UInt256.ofNat 96) (x2 := ptr) =
          writeWordArray mem ptr.toNat (CollateralData.at I.calldata head.toNat).words := by
        change writeWord (writeWord (writeWord (writeWord mem ptr.toNat
          (calldataWord I.calldata head.toNat)) (ptr + UInt256.ofNat 32).toNat
          (calldataWord I.calldata (head + UInt256.ofNat 32).toNat))
          (ptr + UInt256.ofNat 64).toNat
          (calldataWord I.calldata (head + UInt256.ofNat 64).toNat))
          (ptr + UInt256.ofNat 96).toNat
          (calldataWord I.calldata (head + UInt256.ofNat 96).toNat) = _
        simp only [CollateralData.at_words hc, writeWordArray,
          hh32, hh64, hh96, hp32, hp64, hp96, Nat.add_assoc, Nat.reduceAdd]
      have hr := And.intro ha5 rd5
      simp only [midnightBlocks.midnight_block_18569_stack, hm] at hr
      exact ⟨_, _, _, hr⟩
    · left
      refine ⟨by simp [CollateralData.canonicalAt, ho], ?_⟩
      exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [hh96]; exact ho) rd3
  · left
    refine ⟨by simp [CollateralData.canonicalAt, ht], ?_⟩
    exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega) ht rd1

end Benchmarks.Midnight

import Benchmarks.Midnight.CalldataScalarAccounting
import Benchmarks.Midnight.MarketCalldataLastFields

variable {fork : Ethereum.Fork}

/-! The trailing market fields copied after the collateral calldata loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataLastFields_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head arrayPtr ret x0 x1 x2 x3 : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hhead : head.toNat + 256 < UInt256.size) (hptr : ptr.toNat + 256 < UInt256.size)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18734⟩
      (x0 :: x1 :: x2 :: x3 :: arrayPtr :: head :: ptr :: ret :: R) mem aw rdata σ k C) :
    (decodeMarketData I.calldata head.toNat = none ∧ RDrev fork midnightBytecode g s0) ∨
    ((calldataWord I.calldata (head.toNat + 192)).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata (head.toNat + 224)).toNat < EVM.addressModulus ∧ ∃ aw' k' C',
      MemoryAccounting (marketLastMemory mem ptr arrayPtr I.calldata head.toNat) aw' C' ∧
      RD fork midnightBytecode I g s0 ret R
        (marketLastMemory mem ptr arrayPtr I.calldata head.toNat) aw' rdata σ k' C') := by
  have hadd (off : Nat) (ho : off ≤ 224) :
      (head + UInt256.ofNat off).toNat = head.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have padd (off : Nat) (ho : off ≤ 224) :
      (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  let m3 := writeWord (writeWord (writeWord mem (ptr.toNat + 96) arrayPtr)
    (ptr.toNat + 128) (calldataWord I.calldata (head.toNat + 128)))
    (ptr.toNat + 160) (calldataWord I.calldata (head.toNat + 160))
  have hm3 : midnightBlocks.midnight_block_18734_memory (ee := I) (mem := mem)
      (x4 := arrayPtr) (x5 := head) (x6 := ptr) = m3 := by
    simp only [midnightBlocks.midnight_block_18734_memory,
      hadd 128 (by decide), hadd 160 (by decide), padd 96 (by decide),
      padd 128 (by decide), padd 160 (by decide)]
    rfl
  have rd1 := midnightBlocks.midnight_block_18734 (by
    simp only [List.length_cons]; omega) (by jump_dest) rd
  have ha1 := memoryAccountingAt rd1 (by
    unfold midnightBlocks.midnight_block_18734_memory
    memory_account ha)
  simp only [midnightBlocks.midnight_block_18734_stack, hm3] at rd1 ha1
  by_cases he : (calldataWord I.calldata (head.toNat + 192)).toNat < EVM.addressModulus
  · obtain ⟨k2, C2, ha2, rd2⟩ := midnightCalldataAddress_ok_accounted
      (by simp only [List.length_cons]; omega)
      (by rw [hadd 192 (by decide)]; exact he) (by jump_dest) ha1 rd1
    rw [hadd 192 (by decide)] at rd2
    have rd3 := midnightBlocks.midnight_block_18782 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd2
    have ha3 := memoryAccountingAt rd3 (by
      unfold midnightBlocks.midnight_block_18782_memory
      memory_account ha2)
    simp only [midnightBlocks.midnight_block_18782_stack] at rd3
    by_cases hl : (calldataWord I.calldata (head.toNat + 224)).toNat < EVM.addressModulus
    · right
      refine ⟨he, hl, ?_⟩
      obtain ⟨k4, C4, ha4, rd4⟩ := midnightCalldataAddress_ok_accounted
        (by simp only [List.length_cons]; omega)
        (by rw [hadd 224 (by decide)]; exact hl) (by jump_dest) ha3 rd3
      rw [hadd 224 (by decide)] at rd4
      have rd5 := midnightBlocks.midnight_block_18569 (by omega) hvalid rd4
      have ha5 := memoryAccountingAt rd5 (by
        unfold midnightBlocks.midnight_block_18569_memory
        memory_account ha4)
      have hm5 : midnightBlocks.midnight_block_18569_memory
          (mem := midnightBlocks.midnight_block_18782_memory (mem := m3)
            (x0 := calldataWord I.calldata (head.toNat + 192)) (x5 := ptr))
          (x0 := calldataWord I.calldata (head.toNat + 224))
          (x1 := UInt256.ofNat 224) (x2 := ptr) =
          marketLastMemory mem ptr arrayPtr I.calldata head.toNat := by
        simp only [midnightBlocks.midnight_block_18569_memory,
          midnightBlocks.midnight_block_18782_memory, padd 192 (by decide), padd 224 (by decide),
          marketLastMemory, marketLastWords, marketTailWords, List.cons_append, List.nil_append,
          writeWordArray, Nat.add_assoc, Nat.reduceAdd, m3]
        rfl
      have hr := And.intro ha5 rd5
      simp only [midnightBlocks.midnight_block_18569_stack, hm5] at hr
      exact ⟨_, _, _, hr⟩
    · left
      refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, hl], ?_⟩
      exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [hadd 224 (by decide)]; exact hl) rd3
  · left
    refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, he], ?_⟩
    exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
      (by rw [hadd 192 (by decide)]; exact he) rd1

end Benchmarks.Midnight

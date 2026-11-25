import Benchmarks.Midnight.TakeSellerPendingMemory
import Benchmarks.Midnight.MulDivGas
import Benchmarks.Midnight.CheckedUint128Gas

variable {fork : Ethereum.Fork}

/-! Runtime proportional fee reduction, including the zero-credit branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeSellerPendingRuntime {gasCredit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray}
    {aw sellerWord buyerFee buyerSlot debt buyerDebt sellerSlot marketSlot decrease : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hm : 384 ≤ mem.size)
    (hw : memLoad (UInt256.ofNat 352) mem = sellerWord)
    (hle : decrease.toNat ≤ (low128 sellerWord).toNat)
    (ha : MemoryFunding gasCredit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12150⟩
      ([buyerFee, low128 sellerWord, buyerSlot, debt, buyerDebt, sellerSlot, marketSlot,
        decrease] ++ R) mem aw rdata σ k C) :
    let value := takeSellerPendingValue (low128 sellerWord)
      (UInt256.shiftRight sellerWord (UInt256.ofNat 128)) decrease
    let mem' := takeSellerPendingMemory mem buyerFee value
    value.toNat < 2^128 ∧ ∃ aw' k' C', MemoryFunding gasCredit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12187⟩
        ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease] ++ R)
        mem' aw' rdata σ k' C' := by
  have hbound := takeSellerPendingValue_lt (low128_lt sellerWord) (shiftRight128_lt sellerWord) hle
  refine ⟨hbound, ?_⟩
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hz : low128 sellerWord = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_12150_taken
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_12150_taken_memory] at rd1
    have ha1 := memoryFundingAt (credit := gasCredit) rd1 (by memory_fund ha)
    change MemoryFunding gasCredit (takeSellerPendingInitMemory mem buyerFee) _ _ at ha1
    simp only [midnightBlocks.midnight_block_12150_taken_stack] at rd1
    change RD fork midnightBytecode I g s0 ⟨14453⟩ _
      (takeSellerPendingInitMemory mem buyerFee) _ rdata σ _ _ at rd1
    have rd2 := midnightBlocks.midnight_block_14453
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_14453_memory] at rd2
    have ha2 := memoryFundingAt (credit := gasCredit) rd2 (by memory_fund ha1)
    simp only [takeSellerPendingValue, if_pos hz]
    exact ⟨_, _, _, ha2, rd2⟩
  · have hpos := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    have hsafe := mulDivUpSafe_uint128 (shiftRight128_lt sellerWord) (low128_lt sellerWord) hle hpos
    have hsmall := (mulDivUp_le_left hsafe hle).trans_lt (shiftRight128_lt sellerWord)
    have rd1 := midnightBlocks.midnight_block_12150_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hz) rd
    simp only [midnightBlocks.midnight_block_12150_fallthrough_memory] at rd1
    have ha1 := memoryFundingAt (credit := gasCredit) rd1 (by memory_fund ha)
    change MemoryFunding gasCredit (takeSellerPendingInitMemory mem buyerFee) _ _ at ha1
    change RD fork midnightBytecode I g s0 ⟨12164⟩
      (low128 sellerWord :: buyerSlot :: debt :: buyerDebt :: sellerSlot :: marketSlot ::
        decrease :: R)
      (takeSellerPendingInitMemory mem buyerFee) _ rdata σ _ _ at rd1
    have hw1 : memLoad (UInt256.ofNat 352) (takeSellerPendingInitMemory mem buyerFee) =
        sellerWord := (takeSellerPendingInitMemory_load buyerFee (UInt256.ofNat 352) hm
          (Or.inr (by decide)) (Or.inr (by decide))).trans hw
    have rd2 := midnightBlocks.midnight_block_12164 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := gasCredit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_12164_stack, hw1] at rd2
    rcases midnightMulDivUp_mono (by simp only [List.length_cons]; omega) (by jump_dest) rd2 with
      ⟨hbad, _⟩ | ⟨_, k3, C3, hC3, rd3⟩
    · exact False.elim (hbad hsafe)
    · have ha3 := ha2.mono hC3
      have rd4 := midnightBlocks.midnight_block_4204
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have ha4 := memoryFundingAt (credit := gasCredit) rd4 (by memory_fund ha3)
      obtain ⟨k5, C5, hC5, rd5⟩ := midnightToUint128_mono
        (by simp only [List.length_cons]; omega) hsmall (by jump_dest) rd4
      have ha5 := ha4.mono hC5
      have rd6 := midnightBlocks.midnight_block_12183
        (by simp only [List.length_cons]; omega) rd5
      simp only [midnightBlocks.midnight_block_12183_memory] at rd6
      have ha6 := memoryFundingAt (credit := gasCredit) rd6 (by memory_fund ha5)
      simp only [takeSellerPendingValue, if_neg hz]
      exact ⟨_, _, _, ha6, rd6⟩

end Benchmarks.Midnight

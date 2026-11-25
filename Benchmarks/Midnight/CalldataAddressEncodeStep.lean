import Benchmarks.Midnight.CalldataAddress
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.RuntimeBlocks_075

variable {fork : Ethereum.Fork}

/-! One validation and copy step of the calldata address-array encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCalldataAddressEncodeStepFunded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19574⟩
      (index :: count :: ptr :: output :: ret :: R) mem aw rdata σ k C) :
    (¬ (calldataWord I.calldata ptr.toNat).toNat < EVM.addressModulus ∧
      RDrev fork midnightBytecode g s0) ∨
    ((calldataWord I.calldata ptr.toNat).toNat < EVM.addressModulus ∧
      ∃ aw' k' C', C ≤ C' ∧
      MemoryFunding credit (writeWord mem output.toNat (calldataWord I.calldata ptr.toNat)) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨19561⟩
        ((index + UInt256.ofNat 1) :: count :: (ptr + UInt256.ofNat 32) ::
          (output + UInt256.ofNat 32) :: ret :: R)
        (writeWord mem output.toNat (calldataWord I.calldata ptr.toNat)) aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_19574
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  by_cases hc : (calldataWord I.calldata ptr.toNat).toNat < EVM.addressModulus
  · have rd2 := midnightBlocks.midnight_block_18342_fallthrough
      (by simp only [List.length_cons]; omega) (addressCheck_zero hc) rd1
    have rd3 := midnightBlocks.midnight_block_18361
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_19600
      (by simp only [List.length_cons]; omega) (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_19600_stack,
      midnightBlocks.midnight_block_19600_memory, addressMask_computed,
      solcAddrMask_clean hc] at rd4
    have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha)
    exact Or.inr ⟨hc, _, _, _, by omega, ha4, rd4⟩
  · exact Or.inl ⟨hc, midnightCalldataAddress_bad
      (by simp only [List.length_cons]; omega) hc rd1⟩

theorem midnightCalldataAddressEncodeStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19574⟩
      (index :: count :: ptr :: output :: ret :: R) mem aw rdata σ k C) :
    (¬ (calldataWord I.calldata ptr.toNat).toNat < EVM.addressModulus ∧
      RDrev fork midnightBytecode g s0) ∨
    ((calldataWord I.calldata ptr.toNat).toNat < EVM.addressModulus ∧
      ∃ aw' k' C', C ≤ C' ∧
      MemoryAccounting (writeWord mem output.toNat (calldataWord I.calldata ptr.toNat)) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨19561⟩
        ((index + UInt256.ofNat 1) :: count :: (ptr + UInt256.ofNat 32) ::
          (output + UInt256.ofNat 32) :: ret :: R)
        (writeWord mem output.toNat (calldataWord I.calldata ptr.toNat)) aw' rdata σ k' C') := by
  rcases midnightCalldataAddressEncodeStepFunded hstack (MemoryFunding.of_accounting ha) rd with
    hrev | ⟨hc, aw', k', C', hC, ha', rd'⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨hc, aw', k', C', hC, ha'.accounting, rd'⟩

end Benchmarks.Midnight

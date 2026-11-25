import Benchmarks.Midnight.CalldataIndex
import Benchmarks.Midnight.FlashLoanEventEncode

variable {fork : Ethereum.Fork}

/-! Calldata reads and stack rearrangement for one repayment of a flash loan. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanInLoopStack (index tn tp callback an ap : UInt256) : List UInt256 :=
  [index, ap, callback, an, tp, tn]

def flashLoanInTransferTail (index tn tp callback an ap : UInt256) : List UInt256 :=
  [index, ⟨1⟩, ap, callback, an, tp, tn]

theorem midnightFlashLoanInTransferPrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index tn tp callback an ap : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024) (ht : index.toNat < tn.toNat) (ha : index.toNat < an.toNat)
    (hc : (calldataWord I.calldata (calldataIndex tp index).toNat).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode I g s0 ⟨16403⟩
      (flashLoanInLoopStack index tn tp callback an ap ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨23444⟩
      ([calldataWord I.calldata (calldataIndex tp index).toNat, callback, UInt256.ofNat I.codeOwner.val,
        calldataWord I.calldata (calldataIndex ap index).toNat, ⟨16453⟩] ++
        flashLoanInTransferTail index tn tp callback an ap ++ R)
      mem aw rdata σ k' C' := by
  unfold flashLoanInLoopStack at rd
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_16403_taken
    (by omega) (by rw [ult_one ht]; decide) (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_16412
    (by omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_16412_stack] at rd2
  obtain ⟨k3, C3, hC3, rd3⟩ := midnightCalldataIndex
    (by simp only [List.length_cons]; omega) ht (by jump_dest) rd2
  obtain ⟨k4, C4, hC4, rd4⟩ := midnightCalldataAddressRead
    (by simp only [List.length_cons]; omega) hc (by jump_dest) rd3
  have rd5 := midnightBlocks.midnight_block_16432
    (by simp only [List.length_cons]; omega) (by jump_dest) rd4
  simp only [midnightBlocks.midnight_block_16432_stack] at rd5
  obtain ⟨k6, C6, hC6, rd6⟩ := midnightCalldataIndex
    (by simp only [List.length_cons]; omega) ha (by jump_dest) rd5
  have rd7 := midnightBlocks.midnight_block_16443
    (by simp only [List.length_cons]; omega) (by jump_dest) rd6
  exact ⟨_, _, by omega, rd7⟩

theorem midnightFlashLoanInTransferReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index tn tp callback an ap : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨16453⟩
      (flashLoanInTransferTail index tn tp callback an ap ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨16403⟩
      (flashLoanInLoopStack (index + ⟨1⟩) tn tp callback an ap ++ R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_16453
    (by change R.length + 1 + 1 + 1 + 1 + 1 + 2 ≤ 1024; omega)
    (by jump_dest) rd
  exact ⟨_, _, by omega, rd1⟩

end Benchmarks.Midnight

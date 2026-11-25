import Benchmarks.Midnight.CalldataIndex
import Benchmarks.Midnight.FlashLoanEventEncode

variable {fork : Ethereum.Fork}

/-! Calldata reads and stack rearrangement for one outgoing flash-loan transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanOutLoopStack (index tn tp callback an ap dl dp : UInt256) : List UInt256 :=
  index :: flashLoanAfterEventStack tn tp callback an ap dl dp

def flashLoanOutTransferTail (index tn tp callback an ap dl dp : UInt256) : List UInt256 :=
  [index, ⟨1⟩, dl, dp, callback, ap, callback, an, tp, tn]

theorem midnightFlashLoanOutTransferPrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index tn tp callback an ap dl dp : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (ht : index.toNat < tn.toNat) (ha : index.toNat < an.toNat)
    (hc : (calldataWord I.calldata (calldataIndex tp index).toNat).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode I g s0 ⟨16258⟩
      (flashLoanOutLoopStack index tn tp callback an ap dl dp ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨23236⟩
      ([calldataWord I.calldata (calldataIndex tp index).toNat, callback,
        calldataWord I.calldata (calldataIndex ap index).toNat, ⟨16580⟩] ++
        flashLoanOutTransferTail index tn tp callback an ap dl dp ++ R)
      mem aw rdata σ k' C' := by
  unfold flashLoanOutLoopStack flashLoanAfterEventStack at rd
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_16258_taken
    (by simp only [List.length_cons]; omega) (by rw [ult_one ht]; decide) (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_16537
    (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_16537_stack] at rd2
  obtain ⟨k3, C3, hC3, rd3⟩ := midnightCalldataIndex
    (by simp only [List.length_cons]; omega) ht (by jump_dest) rd2
  obtain ⟨k4, C4, hC4, rd4⟩ := midnightCalldataAddressRead
    (by simp only [List.length_cons]; omega) hc (by jump_dest) rd3
  have rd5 := midnightBlocks.midnight_block_16561
    (by simp only [List.length_cons]; omega) (by jump_dest) rd4
  simp only [midnightBlocks.midnight_block_16561_stack] at rd5
  obtain ⟨k6, C6, hC6, rd6⟩ := midnightCalldataIndex
    (by simp only [List.length_cons]; omega) ha (by jump_dest) rd5
  have rd7 := midnightBlocks.midnight_block_16573
    (by simp only [List.length_cons]; omega) (by jump_dest) rd6
  exact ⟨_, _, by omega, rd7⟩

theorem midnightFlashLoanOutTransferReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index tn tp callback an ap dl dp : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨16580⟩
      (flashLoanOutTransferTail index tn tp callback an ap dl dp ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨16258⟩
      (flashLoanOutLoopStack (index + ⟨1⟩) tn tp callback an ap dl dp ++ R)
      mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_16580 hstack (by jump_dest) rd
  exact ⟨_, _, by omega, rd1⟩

end Benchmarks.Midnight

import Benchmarks.Midnight.TakeDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.RuntimeBlocks_042
import Benchmarks.Midnight.RuntimeBlocks_069

/-! The checked taker, receiver, callback, and callback-data offset in the take head. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeScalarsMemory (mem bytes : ByteArray) : ByteArray :=
  writeWord (writeWord (writeWord mem 544 (calldataWord bytes 100))
    288 (calldataWord bytes 132)) 192 (calldataWord bytes 164)

theorem midnightTakeScalars {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10846⟩ R mem aw rdata σ k C) :
    ((¬ TakeScalarsValid I.calldata ∨ decodeCalldataBytes I.calldata 196 = none) ∧
      RDrev midnightBytecode g s0) ∨
    (TakeScalarsValid I.calldata ∧ (calldataWord I.calldata 196).toNat < 2^64 ∧
      ∃ aw' k' C', MemoryFunding credit (takeScalarsMemory mem I.calldata) aw' C' ∧
        RD midnightBytecode I g s0 ⟨10911⟩ R
          (takeScalarsMemory mem I.calldata) aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_10846 (by omega) (by jump_dest) rd
  by_cases ht : (calldataWord I.calldata 100).toNat < EVM.addressModulus
  · have rd2 := midnightBlocks.midnight_block_18298_fallthrough (by omega)
      (addressCheck_zero ht) rd1
    have rd3 := midnightBlocks.midnight_block_18319
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_10854 (by omega) (by jump_dest) rd3
    have ha4 := memoryFundingAt (credit := credit) rd4 (by
      unfold midnightBlocks.midnight_block_10854_memory
      memory_fund ha)
    by_cases hr : (calldataWord I.calldata 132).toNat < EVM.addressModulus
    · have rd5 := midnightBlocks.midnight_block_18320_fallthrough (by omega)
        (addressCheck_zero hr) rd4
      have rd6 := midnightBlocks.midnight_block_18341
        (by simp only [List.length_cons]; omega) (by jump_dest) rd5
      by_cases hc : (calldataWord I.calldata 164).toNat < EVM.addressModulus
      · have rd7 := midnightBlocks.midnight_block_10866_fallthrough (by omega)
          (addressCheck_zero hc) rd6
        have ha7 := memoryFundingAt (credit := credit) rd7 (by
          unfold midnightBlocks.midnight_block_10866_fallthrough_memory
          memory_fund ha4)
        simp only [midnightBlocks.midnight_block_10866_fallthrough_stack] at rd7
        by_cases ho : (calldataWord I.calldata 196).toNat < 2^64
        · have rd8 := midnightBlocks.midnight_block_10895_fallthrough (by omega)
            (ugt_zero (by change (calldataWord I.calldata 196).toNat ≤ 2^64 - 1; omega)) rd7
          have ha8 := memoryFundingAt (credit := credit) rd8 (by memory_fund ha7)
          exact Or.inr ⟨⟨ht, hr, hc⟩, ho, _, _, _, ha8, rd8⟩
        · have rr := midnightBlocks.midnight_block_10895_taken (by omega) (by
            rw [ugt_one (by change 2^64 - 1 < (calldataWord I.calldata 196).toNat; omega)]
            decide) (by jump_dest) rd7
          exact Or.inl ⟨Or.inr (by simp only [decodeCalldataBytes, ho, if_false]),
            midnightBlocks.midnight_block_6350 (by omega) rr⟩
      · have rr := midnightBlocks.midnight_block_10866_taken (by omega)
          (addressCheck_nonzero hc) (by jump_dest) rd6
        exact Or.inl ⟨Or.inl (fun h ↦ hc h.2.2),
          midnightBlocks.midnight_block_6350 (by change R.length + 2 ≤ 1024; omega) rr⟩
    · have rr := midnightBlocks.midnight_block_18320_taken (by omega)
        (addressCheck_nonzero hr) (by jump_dest) rd4
      exact Or.inl ⟨Or.inl (fun h ↦ hr h.2.1),
        midnightBlocks.midnight_block_6350 (by change R.length + 2 + 2 ≤ 1024; omega) rr⟩
  · have rr := midnightBlocks.midnight_block_18298_taken (by omega)
      (addressCheck_nonzero ht) (by jump_dest) rd1
    exact Or.inl ⟨Or.inl (fun h ↦ ht h.1),
      midnightBlocks.midnight_block_6350 (by change R.length + 2 + 2 ≤ 1024; omega) rr⟩

end Benchmarks.Midnight

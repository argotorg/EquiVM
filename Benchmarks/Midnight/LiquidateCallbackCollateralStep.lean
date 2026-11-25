import Benchmarks.Midnight.CalldataAddressFunding
import Benchmarks.Midnight.CollateralData
import Benchmarks.Midnight.RuntimeBlocks_025
import Benchmarks.Midnight.RuntimeBlocks_026

variable {fork : Ethereum.Fork}

/-! One validated collateral record in liquidation's callback encoding loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCallbackCollateralStep {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw index base ptr a b c d output root badDebt : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hptr : ptr.toNat + 128 < UInt256.size) (hout : output.toNat + 128 < UInt256.size)
    (hc : CollateralData.canonicalAt I.calldata ptr.toNat) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨6376⟩
      ([index, base, ptr, a, b, c, d, output, root, badDebt, root] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧
      MemoryFunding credit
        (writeWordArray mem output.toNat (CollateralData.at I.calldata ptr.toNat).words) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨6038⟩
        ([index + UInt256.ofNat 1, base, ptr + UInt256.ofNat 128, a, b, c, d, output + UInt256.ofNat 128,
          root, badDebt, root] ++ R)
        (writeWordArray mem output.toNat (CollateralData.at I.calldata ptr.toNat).words)
        aw' rdata σ k' C' := by
  have hp32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hp64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hp96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have ho32 := uadd_word_ofNat_toNat output 32 (by omega)
  have ho64 := uadd_word_ofNat_toNat output 64 (by omega)
  have ho96 := uadd_word_ofNat_toNat output 96 (by omega)
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_6376
    (R := badDebt :: root :: R) (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_6376_stack, addressMask_computed] at rd1
  have ha1 := memoryFundingAt (credit := credit) rd1 (ha.mono (by omega))
  obtain ⟨k2, C2, hc2, ha2, rd2⟩ := midnightCalldataAddress_funded
    (by simp only [List.length_cons]; omega) hc.1 (by jump_dest) ha1 rd1
  have rd3 := midnightBlocks.midnight_block_6416
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  have ha3 := memoryFundingAt (credit := credit) rd3 (by
    unfold midnightBlocks.midnight_block_6416_memory
    memory_fund ha2)
  simp only [midnightBlocks.midnight_block_6416_stack] at rd3
  obtain ⟨k4, C4, hc4, ha4, rd4⟩ := midnightCalldataAddress_funded
    (by simp only [List.length_cons]; omega) (by rw [hp96]; exact hc.2)
    (by jump_dest) ha3 rd3
  have rd5 := midnightBlocks.midnight_block_6445
    (by omega) (by jump_dest) rd4
  have ha5 := memoryFundingAt (credit := credit) rd5 (by
    unfold midnightBlocks.midnight_block_6445_memory
    memory_fund ha4)
  have hf := And.intro ha5 rd5
  simp only [midnightBlocks.midnight_block_6445_stack,
    midnightBlocks.midnight_block_6445_memory, midnightBlocks.midnight_block_6416_memory,
    solcAddrMask_clean hc.1, hp96, solcAddrMask_clean hc.2, hp32, hp64, ho32, ho64, ho96] at hf
  have hm : writeWord (writeWord (writeWord (writeWord mem output.toNat
      (calldataWord I.calldata ptr.toNat)) (output.toNat + 32)
      (calldataWord I.calldata (ptr.toNat + 32))) (output.toNat + 64)
      (calldataWord I.calldata (ptr.toNat + 64))) (output.toNat + 96)
      (calldataWord I.calldata (ptr.toNat + 96)) =
      writeWordArray mem output.toNat (CollateralData.at I.calldata ptr.toNat).words := by
    simp only [CollateralData.at_words hc, writeWordArray, Nat.add_assoc, Nat.reduceAdd]
  simp only [calldataWord] at hf hm
  unfold Reasoning.Theory.writeWord at hm
  rw [hm] at hf
  refine ⟨_, _, _, ?_, hf⟩
  omega

end Benchmarks.Midnight

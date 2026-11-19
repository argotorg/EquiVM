import Benchmarks.Midnight.FlashLoanArguments
import Benchmarks.Midnight.FlashLoanSliceTrace
import Benchmarks.Midnight.AddressDecode

/-! The flash-loan entry checks through the decoding of all calldata references. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanRefStack (bytes : ByteArray) : List UInt256 :=
  [calldataArgumentLength bytes 100, calldataArgumentPointer bytes 100,
    calldataArgumentPointer bytes 36, calldataWord bytes 68, calldataArgumentLength bytes 36,
    calldataArgumentPointer bytes 4, calldataArgumentLength bytes 4]

theorem midnightFlashLoanEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (rd : RD midnightBytecode I g s0 ⟨16038⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? ["tokens", "assets", "callback", "data"]
        [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] I.calldata =
        none ∧ RDrev midnightBytecode g s0) ∨
    (132 ≤ I.calldata.size ∧ CalldataArgumentValid false I.calldata 4 ∧
      CalldataArgumentValid false I.calldata 36 ∧
      (calldataWord I.calldata 68).toNat < EVM.addressModulus ∧
      CalldataArgumentValid true I.calldata 100 ∧
      config.externalABI.decodeCalldata? ["tokens", "assets", "callback", "data"]
        [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] I.calldata =
        decodeFlashLoanArguments I.calldata ∧
      ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨16153⟩
        (flashLoanRefStack I.calldata ++ R) mem aw rdata σ k' C') := by
  have reject (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
      ⟨128⟩ = ⟨1⟩) :
      config.externalABI.decodeCalldata? ["tokens", "assets", "callback", "data"]
        [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] I.calldata =
        none ∧ RDrev midnightBytecode g s0 := by
    refine ⟨midnightDecodeFlashLoan_none_check h4
      (solcSLT_sub4_of_check (bit := true) hc), ?_⟩
    have rr := midnightBlocks.midnight_block_16038_taken (by omega)
      (by change UInt256.slt (UInt256.lnot ⟨3⟩ + _) ⟨128⟩ ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by omega) rr
  by_cases hshort : I.calldata.size < 132
  · exact Or.inl (reject (entrySizeCheck_short h4 hshort (by decide) hsize))
  by_cases hhuge : 2^255 + 4 ≤ I.calldata.size
  · exact Or.inl (reject (entrySizeCheck_huge hhuge hsize (by decide)))
  have h132 : 132 ≤ I.calldata.size := by omega
  have hcheck : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨128⟩ =
      ⟨0⟩ := entrySizeCheck_ok h132 (by omega) hsize
  have hdecode := midnightDecodeFlashLoan h132 hsize hselector
    (solcSLT_sub4_of_check (bit := false) hcheck)
  have rd1 := midnightBlocks.midnight_block_16038_fallthrough (by omega) hcheck rd
  rcases midnightFlashLoanTokensRef (by omega) hsize rd1 with
    ⟨ht, hr⟩ | ⟨ht, kt, Ct, hCt, rd2⟩
  · exact Or.inl ⟨hdecode.trans (decodeFlashLoanArguments_invalid (.inl ht)), hr⟩
  rcases midnightFlashLoanTailRef false (by omega) hsize rd2 with
    ⟨ha, hr⟩ | ⟨ha, ka, Ca, hCa, rd3⟩
  · exact Or.inl ⟨hdecode.trans (decodeFlashLoanArguments_invalid (.inr (.inl ha))), hr⟩
  have rd4 := midnightBlocks.midnight_block_16112
    (by simp only [List.length_cons]; omega) (by jump_dest) rd3
  by_cases hc : (calldataWord I.calldata 68).toNat < EVM.addressModulus
  · have rd5 := midnightBlocks.midnight_block_18276_fallthrough
      (by simp only [List.length_cons]; omega) (addressCheck_zero hc) rd4
    have rd6 := midnightBlocks.midnight_block_18297
      (by simp only [List.length_cons]; omega) (by jump_dest) rd5
    simp only [midnightBlocks.midnight_block_18297_stack] at rd6
    rcases midnightFlashLoanTailRef true
        (by simp only [List.length_cons]; omega) hsize rd6 with
      ⟨hd, hr⟩ | ⟨hd, kd, Cd, hCd, rd7⟩
    · exact Or.inl ⟨hdecode.trans
        (decodeFlashLoanArguments_invalid (.inr (.inr (.inr hd)))), hr⟩
    · exact Or.inr ⟨h132, ht, ha, hc, hd, hdecode, kd, Cd, by omega, rd7⟩
  · have rr := midnightBlocks.midnight_block_18276_taken
      (by simp only [List.length_cons]; omega) (addressCheck_nonzero hc) (by jump_dest) rd4
    exact Or.inl ⟨hdecode.trans
      (decodeFlashLoanArguments_invalid (.inr (.inr (.inl hc)))),
      midnightBlocks.midnight_block_6350
        (by simp only [midnightBlocks.midnight_block_18276_taken_stack,
          List.length_cons]; omega) rr⟩

end Benchmarks.Midnight

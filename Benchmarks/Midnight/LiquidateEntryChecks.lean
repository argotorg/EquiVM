import Benchmarks.Midnight.LiquidateScalars
import Benchmarks.Midnight.LiquidateDecodeFacts
import Benchmarks.Midnight.LiquidateDataRef
import Benchmarks.Midnight.CalldataHeadCheck
import Benchmarks.Midnight.RuntimeBlocks_021

variable {fork : Ethereum.Fork}

/-! The liquidation entry checks before materializing its market argument. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

set_option maxHeartbeats 800000 in
theorem midnightLiquidateEntryChecks {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨4983⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? liquidateNames liquidateTypes I.calldata = none ∧
      RDrev fork midnightBytecode g s0) ∨
    (292 ≤ I.calldata.size ∧ (calldataWord I.calldata 4).toNat < 2^64 ∧
      LiquidateScalarsValid I.calldata ∧ CalldataArgumentValid true I.calldata 260 ∧
      config.externalABI.decodeCalldata? liquidateNames liquidateTypes I.calldata =
        decodeLiquidateArguments I.calldata ∧
      ∃ aw' k' C', MemoryAccounting (writeWord mem 736 (calldataWord I.calldata 228)) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨5126⟩
          (calldataArgumentLength I.calldata 260 :: calldataArgumentPointer I.calldata 260 ::
            calldataWord I.calldata 132 :: calldataWord I.calldata 196 ::
            calldataWord I.calldata 164 :: R)
          (writeWord mem 736 (calldataWord I.calldata 228)) aw' rdata σ k' C') := by
  have reject (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
      ⟨288⟩ = ⟨1⟩) :
      config.externalABI.decodeCalldata? liquidateNames liquidateTypes I.calldata = none ∧
        RDrev fork midnightBytecode g s0 := by
    refine ⟨midnightDecodeLiquidate_none_check h4 (solcSLT_sub4_of_check (bit := true) hc), ?_⟩
    have rr := midnightBlocks.midnight_block_4983_taken (by omega)
      (by change UInt256.slt (UInt256.lnot ⟨3⟩ + _) ⟨288⟩ ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_712 (by omega) rr
  by_cases hshort : I.calldata.size < 292
  · exact Or.inl (reject (entrySizeCheck_short h4 hshort (by decide) hsize))
  by_cases hhuge : 2^255 + 4 ≤ I.calldata.size
  · exact Or.inl (reject (entrySizeCheck_huge hhuge hsize (by decide)))
  have h292 : 292 ≤ I.calldata.size := by omega
  have hcheck : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨288⟩ = ⟨0⟩ :=
    entrySizeCheck_ok h292 (by omega) hsize
  have hdecode := midnightDecodeLiquidate h292 hsize hselector
    (solcSLT_sub4_of_check (bit := false) hcheck)
  have rd1 := midnightBlocks.midnight_block_4983_fallthrough (by omega) hcheck rd
  by_cases ho : (calldataWord I.calldata 4).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero (by change _ ≤ 2^64 - 1; omega)
    have rd2 := midnightBlocks.midnight_block_4996_fallthrough (by omega) hc rd1
    by_cases hh : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.sub (UInt256.ofNat I.calldata.size)
        (calldataWord I.calldata 4)) ⟨256⟩ = ⟨0⟩
    · have rd3 := midnightBlocks.midnight_block_5012_fallthrough (by omega) hh rd2
      have ha3 := memoryAccountingAt rd3 (by memory_account ha)
      rcases midnightLiquidateScalars (by omega) ha3 rd3 with
        ⟨hbad, hrev⟩ | ⟨hv, aw4, k4, C4, _, ha4, rd4⟩
      · exact Or.inl ⟨hdecode.trans (decodeLiquidateArguments_none_scalars hbad), hrev⟩
      · rcases midnightLiquidateDataRef (by simp only [List.length_cons]; omega) hsize rd4 with
          ⟨hbad, hrev⟩ | ⟨hdata, k5, C5, hc5, rd5⟩
        · exact Or.inl ⟨hdecode.trans (decodeLiquidateArguments_none_data hbad), hrev⟩
        · exact Or.inr ⟨h292, ho, hv, hdata, hdecode, aw4, k5, C5,
            ⟨ha4.paid.mono hc5, ha4.covered⟩, rd5⟩
    · have rr := midnightBlocks.midnight_block_5012_taken (by omega) hh (by jump_dest) rd2
      refine Or.inl ⟨hdecode.trans ?_, midnightBlocks.midnight_block_712 (by omega) rr⟩
      have hn : decodeCalldataMarket I.calldata 4 = none := by
        cases hd : decodeCalldataMarket I.calldata 4 with
        | none => rfl
        | some m => exact False.elim (hh (decodeCalldataMarket_headerCheck hd))
      exact decodeLiquidateArguments_none_market hn
  · have hc : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    have rr := midnightBlocks.midnight_block_4996_taken (by omega) hc (by jump_dest) rd1
    refine Or.inl ⟨hdecode.trans ?_, midnightBlocks.midnight_block_712 (by omega) rr⟩
    have hcap : solcMaxU64 < (calldataWord I.calldata 4).toNat := by
      change 2^64 - 1 < _
      omega
    apply decodeLiquidateArguments_none_market
    simp only [decodeCalldataMarket, hcap, true_or, if_true]

end Benchmarks.Midnight

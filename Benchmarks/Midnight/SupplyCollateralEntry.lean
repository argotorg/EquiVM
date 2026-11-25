import Benchmarks.Midnight.MarketIndexAmountDecode
import Benchmarks.Midnight.MarketDecoderPreserved
import Benchmarks.Midnight.MarketCalldataHugeRuntime
import Benchmarks.Midnight.RuntimeBlocks_063
import Benchmarks.Midnight.RuntimeBlocks_064
import Benchmarks.Midnight.AddressDecode

variable {fork : Ethereum.Fork}

/-! Collateral-supply decoding, with the reserved memory words retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightSupplyCollateralEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C base : Nat} {R words : List UInt256}
    (hstack : R.length + 27 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (hkeep : MemoryWords mem base words) (hbase : 96 ≤ base)
    (hbelow : base + 32 * words.length ≤ 832)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨16940⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? ["market", "collateralIndex", "assets", "onBehalf"] [Model.marketABI, Model.u256, Model.u256, Model.addr] I.calldata = none ∧
      RDrev fork midnightBytecode g s0) ∨
    (∃ m, config.externalABI.decodeCalldata? ["market", "collateralIndex", "assets", "onBehalf"] [Model.marketABI, Model.u256, Model.u256, Model.addr] I.calldata =
        some (marketIndexAmountArguments m (calldataWord I.calldata 36) (calldataWord I.calldata 68) (AccountAddress.ofNat (calldataWord I.calldata 100).toNat)) ∧
      132 ≤ I.calldata.size ∧ I.calldata.size < 2^255 ∧
      (calldataWord I.calldata 100).toNat < EVM.addressModulus ∧
      ∃ mem' root aw' k' C', root.toNat = 1120 + 160 * m.collaterals.length ∧
        MarketStored mem' ⟨832⟩ ⟨1088⟩ root m ∧ memLoad (UInt256.ofNat 64) mem' = root ∧
        root.toNat ≤ mem'.size ∧ MemoryWords mem' base words ∧ MemoryAccounting mem' aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨17004⟩ (calldataWord I.calldata 100 :: solcAddrMask :: calldataWord I.calldata 36 :: calldataWord I.calldata 68 :: ⟨832⟩ :: R)
          mem' aw' rdata σ k' C') := by
  have reject (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨128⟩ = ⟨1⟩) :
      config.externalABI.decodeCalldata? ["market", "collateralIndex", "assets", "onBehalf"] [Model.marketABI, Model.u256, Model.u256, Model.addr] I.calldata = none ∧
        RDrev fork midnightBytecode g s0 := by
    refine ⟨midnightDecodeMarketIndexAmount_none_check h4
      (solcSLT_sub4_of_check (bit := true) hc), ?_⟩
    have rd1 := midnightBlocks.midnight_block_16940_taken (by omega)
      (by change UInt256.slt (UInt256.lnot ⟨3⟩ + _) ⟨128⟩ ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by omega) rd1
  by_cases hshort : I.calldata.size < 132
  · exact Or.inl (reject (entrySizeCheck_short h4 hshort (by decide) hsize))
  by_cases hhuge : 2^255 + 4 ≤ I.calldata.size
  · exact Or.inl (reject (entrySizeCheck_huge hhuge hsize (by decide)))
  have h132 : 132 ≤ I.calldata.size := by omega
  have hcheck : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨128⟩ = ⟨0⟩ :=
    entrySizeCheck_ok h132 (by omega) hsize
  have hdecode := midnightDecodeMarketIndexAmount h132 hsize hselector
    (solcSLT_sub4_of_check (bit := false) hcheck)
  have rd1 := midnightBlocks.midnight_block_16940_fallthrough (by omega) hcheck rd
  by_cases hoff : (calldataWord I.calldata 4).toNat < 2^64
  · have hg : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := by
      apply ugt_zero
      change _ ≤ 18446744073709551615
      omega
    have rd2 := midnightBlocks.midnight_block_16952_fallthrough (by omega) hg rd1
    have rd3 := midnightBlocks.midnight_block_16969 (by omega) (by jump_dest) rd2
    change RD fork midnightBytecode I g s0 ⟨18574⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 4) :: UInt256.ofNat I.calldata.size ::
        ⟨16982⟩ :: R) mem aw rdata σ _ _ at rd3
    have ha3 := memoryAccountingAt rd3 (by memory_account ha)
    have hh : (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat =
        4 + (calldataWord I.calldata 4).toNat := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by change 4 + _ < 2^256; omega)
    have hcap : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat := by
      change ¬ 18446744073709551615 < _; omega
    by_cases hsmall : I.calldata.size < 2^255
    · have hd : decodeCalldataMarket I.calldata 4 =
          decodeMarketData I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat := by
        simp only [decodeCalldataMarket, hcap, false_or, not_le_of_gt hsmall, if_false, hh]
      rw [hd] at hdecode
      rcases midnightMarketCalldataDecoder_preserved (R := R) (by omega)
          hsmall (by rw [hh]; omega) (by decide) (by decide) hfree (by jump_dest) hkeep hbase hbelow ha3 rd3 with
        ⟨hnone, hr⟩ | ⟨m, hm, hfit, mem', root, aw4, k4, C4, hroot, hstored, hf4, hmem4, hk4, ha4, rd4⟩
      · left
        refine ⟨?_, hr⟩
        rw [hdecode]
        cases hm : decodeMarketData I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat with
        | none => rfl
        | some m =>
          have hc := hnone m hm
          change ¬ 1120 + 160 * m.collaterals.length < 2^64 at hc
          simp only [bind, Option.bind, hc, and_false, if_false]
      · have rd5 := midnightBlocks.midnight_block_16982
          (by simp only [List.length_cons]; omega) (by jump_dest) rd4
        by_cases hu : (calldataWord I.calldata 100).toNat < EVM.addressModulus
        · have rd6 := midnightBlocks.midnight_block_18298_fallthrough (by
            simp only [List.length_cons]; omega)
            (addressCheck_zero hu) rd5
          have rd7 := midnightBlocks.midnight_block_18319 (by
            simp only [List.length_cons]; omega) (by jump_dest) rd6
          simp only [midnightBlocks.midnight_block_16982_stack,
            midnightBlocks.midnight_block_18298_fallthrough_stack,
            midnightBlocks.midnight_block_18319_stack, addressMask_computed] at rd7
          have ha8 := memoryAccountingAt rd7 (by memory_account ha4)
          refine Or.inr ⟨m, ?_, h132, hsmall, hu, mem', root, _, _, _, hroot, hstored, hf4,
            hmem4, hk4, ha8, rd7⟩
          rw [hdecode, hm]
          dsimp only [bind, Option.bind]
          exact if_pos ⟨hu, hfit⟩
        · left
          have rr := midnightBlocks.midnight_block_18298_taken
            (by simp only [List.length_cons]; omega) (addressCheck_nonzero hu) (by jump_dest) rd5
          refine ⟨?_, midnightBlocks.midnight_block_6350
            (by simp only [midnightBlocks.midnight_block_18298_taken_stack, List.length_cons]; omega) rr⟩
          rw [hdecode, hm]
          simp only [bind, Option.bind, hu, false_and, if_false]
    · left
      refine ⟨?_, midnightMarketCalldataHuge (R := R) (by omega)
        hsize (by omega) (by rw [hh]; omega) (by decide) hfree rd3⟩
      rw [hdecode]
      simp only [decodeCalldataMarket, show 2^255 ≤ I.calldata.size from by omega,
        or_true, if_true, bind, Option.bind]
  · left
    refine ⟨?_, ?_⟩
    · rw [hdecode]
      have hc : solcMaxU64 < (calldataWord I.calldata 4).toNat := by
        change 18446744073709551615 < _; omega
      simp only [decodeCalldataMarket, hc, true_or, if_true, bind, Option.bind]
    · have hg : UInt256.gt (calldataWord I.calldata 4)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
            (UInt256.ofNat 1)) = ⟨1⟩ := by
        apply ugt_one
        change 18446744073709551615 < _
        omega
      have rd2 := midnightBlocks.midnight_block_16952_taken (by omega)
        (by change UInt256.gt (calldataWord I.calldata 4) _ ≠ _; rw [hg]; decide)
        (by jump_dest) rd1
      exact midnightBlocks.midnight_block_6350 (by
        simp only [midnightBlocks.midnight_block_16952_taken_stack, List.length_cons]; omega) rd2

end Benchmarks.Midnight

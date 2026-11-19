import Benchmarks.Midnight.MarketUserDecode
import Benchmarks.Midnight.MarketDecoderAccounting
import Benchmarks.Midnight.MarketCalldataHugeRuntime
import Benchmarks.Midnight.RuntimeBlocks_059

/-! Decode updatePosition and enter the shared market initialization routine. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightUpdatePositionEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 27 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨15853⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? ["market", "user"] [Model.marketABI, Model.addr] I.calldata = none ∧
      RDrev midnightBytecode g s0) ∨
    (∃ m, config.externalABI.decodeCalldata? ["market", "user"] [Model.marketABI, Model.addr] I.calldata =
        some (marketUserArguments m (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)) ∧
      68 ≤ I.calldata.size ∧ I.calldata.size < 2^255 ∧
      (calldataWord I.calldata 36).toNat < EVM.addressModulus ∧
      ∃ mem' root aw' k' C', root.toNat = 1120 + 160 * m.collaterals.length ∧
        MarketStored mem' ⟨832⟩ ⟨1088⟩ root m ∧ memLoad (UInt256.ofNat 64) mem' = root ∧
        root.toNat ≤ mem'.size ∧ MemoryAccounting mem' aw' C' ∧
        RD midnightBytecode I g s0 ⟨20557⟩ (⟨832⟩ :: ⟨15919⟩ :: ⟨832⟩ :: calldataWord I.calldata 36 :: ⟨2594⟩ :: ⟨1184⟩ :: R)
          mem' aw' rdata σ k' C') := by
  have reject (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ = ⟨1⟩) :
      config.externalABI.decodeCalldata? ["market", "user"] [Model.marketABI, Model.addr] I.calldata = none ∧
        RDrev midnightBytecode g s0 := by
    refine ⟨midnightDecodeMarketUser_none_check h4
      (solcSLT_sub4_of_check (bit := true) hc), ?_⟩
    have rd1 := midnightBlocks.midnight_block_15853_taken (by omega)
      (by change UInt256.slt (UInt256.lnot ⟨3⟩ + _) ⟨64⟩ ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by omega) rd1
  by_cases hshort : I.calldata.size < 68
  · exact Or.inl (reject (entrySizeCheck_short h4 hshort (by decide) hsize))
  by_cases hhuge : 2^255 + 4 ≤ I.calldata.size
  · exact Or.inl (reject (entrySizeCheck_huge hhuge hsize (by decide)))
  have h68 : 68 ≤ I.calldata.size := by omega
  have hcheck : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ = ⟨0⟩ :=
    entrySizeCheck_ok h68 (by omega) hsize
  have hdecode := midnightDecodeMarketUser h68 hsize hselector
    (solcSLT_sub4_of_check (bit := false) hcheck)
  have rd1 := midnightBlocks.midnight_block_15853_fallthrough (by omega) hcheck rd
  by_cases hoff : (calldataWord I.calldata 4).toNat < 2^64
  · have hg : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := by
      apply ugt_zero
      change _ ≤ 18446744073709551615
      omega
    have rd2 := midnightBlocks.midnight_block_15865_fallthrough (by omega) hg rd1
    have rd3 := midnightBlocks.midnight_block_15882 (by omega) (by jump_dest) rd2
    change RD midnightBytecode I g s0 ⟨18574⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 4) :: UInt256.ofNat I.calldata.size ::
        ⟨15901⟩ :: ⟨2594⟩ :: ⟨1184⟩ :: R) mem aw rdata σ _ _ at rd3
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
      rcases midnightMarketCalldataDecoder_accounted (by simp only [List.length_cons]; omega)
          hsmall (by rw [hh]; omega) (by decide) (by decide) hfree (by jump_dest) ha3 rd3 with
        ⟨hnone, hr⟩ | ⟨m, hm, hfit, mem', root, aw4, k4, C4, hroot, hstored, hf4, hmem4, ha4, rd4⟩
      · left
        refine ⟨?_, hr⟩
        rw [hdecode]
        cases hm : decodeMarketData I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat with
        | none => rfl
        | some m =>
          have hc := hnone m hm
          change ¬ 1120 + 160 * m.collaterals.length < 2^64 at hc
          simp only [bind, Option.bind, hc, and_false, if_false]
      · have rd5 := midnightBlocks.midnight_block_15901
          (by simp only [List.length_cons]; omega) (by jump_dest) rd4
        by_cases hu : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · have rd6 := midnightBlocks.midnight_block_18232_fallthrough (by
            simp only [List.length_cons]; omega)
            (addressCheck_zero hu) rd5
          have rd7 := midnightBlocks.midnight_block_18253 (by
            simp only [List.length_cons]; omega) (by jump_dest) rd6
          have rd8 := midnightBlocks.midnight_block_15909 (by
            simp only [List.length_cons]; omega)
            (by jump_dest) rd7
          have ha8 := memoryAccountingAt rd8 (by memory_account ha4)
          refine Or.inr ⟨m, ?_, h68, hsmall, hu, mem', root, _, _, _, hroot, hstored, hf4,
            hmem4, ha8, rd8⟩
          rw [hdecode, hm]
          dsimp only [bind, Option.bind]
          exact if_pos ⟨hu, hfit⟩
        · left
          refine ⟨?_, midnightAddress36_revert (by
            simp only [List.length_cons]; omega)
            hu rd5⟩
          rw [hdecode, hm]
          simp only [bind, Option.bind, hu, false_and, if_false]
    · left
      refine ⟨?_, midnightMarketCalldataHuge (by simp only [List.length_cons]; omega)
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
      have rd2 := midnightBlocks.midnight_block_15865_taken (by omega)
        (by change UInt256.gt (calldataWord I.calldata 4) _ ≠ _; rw [hg]; decide)
        (by jump_dest) rd1
      exact midnightBlocks.midnight_block_6350 (by
        simp only [midnightBlocks.midnight_block_15865_taken_stack, List.length_cons]; omega) rd2

end Benchmarks.Midnight

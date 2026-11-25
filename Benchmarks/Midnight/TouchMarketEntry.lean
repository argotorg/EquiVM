import Benchmarks.Midnight.MarketOnlyDecode
import Benchmarks.Midnight.MarketCalldataDecoder
import Benchmarks.Midnight.MarketCalldataHugeRuntime
import Benchmarks.Midnight.RuntimeBlocks_019

variable {fork : Ethereum.Fork}

/-! Decode the public touchMarket argument and enter its shared routine. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightTouchMarketEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 27 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨4309⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? ["market"] [Model.marketABI] I.calldata = none ∧
      RDrev fork midnightBytecode g s0) ∨
    (∃ m, config.externalABI.decodeCalldata? ["market"] [Model.marketABI] I.calldata =
        some (marketOnlyArguments m) ∧
      36 ≤ I.calldata.size ∧ I.calldata.size < 2^255 ∧
      ∃ mem' root aw' k' C', root.toNat = 1120 + 160 * m.collaterals.length ∧
        MarketStored mem' ⟨832⟩ ⟨1088⟩ root m ∧ memLoad (UInt256.ofNat 64) mem' = root ∧
        RD fork midnightBytecode I g s0 ⟨20557⟩ (⟨832⟩ :: ⟨3755⟩ :: ⟨32⟩ :: R)
          mem' aw' rdata σ k' C') := by
  have reject (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨1⟩) :
      config.externalABI.decodeCalldata? ["market"] [Model.marketABI] I.calldata = none ∧
        RDrev fork midnightBytecode g s0 := by
    refine ⟨midnightDecodeMarketOnly_none_check h4
      (solcSLT_sub4_of_check (bit := true) hc), ?_⟩
    have rd1 := midnightBlocks.midnight_block_4309_taken (by omega)
      (by change UInt256.slt (UInt256.lnot ⟨3⟩ + _) ⟨32⟩ ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_712 (by omega) rd1
  by_cases hshort : I.calldata.size < 36
  · exact Or.inl (reject (entrySizeCheck_short h4 hshort (by decide) hsize))
  by_cases hhuge : 2^255 + 4 ≤ I.calldata.size
  · exact Or.inl (reject (entrySizeCheck_huge hhuge hsize (by decide)))
  have h36 : 36 ≤ I.calldata.size := by omega
  have hcheck : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩ :=
    entrySizeCheck_ok h36 (by omega) hsize
  have hdecode := midnightDecodeMarketOnly h36 hsize hselector
    (solcSLT_sub4_of_check (bit := false) hcheck)
  have rd1 := midnightBlocks.midnight_block_4309_fallthrough (by omega) hcheck rd
  by_cases hoff : (calldataWord I.calldata 4).toNat < 2^64
  · have hg : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := by
      apply ugt_zero
      change _ ≤ 18446744073709551615
      omega
    have rd2 := midnightBlocks.midnight_block_4321_fallthrough (by omega) hg rd1
    have rd3 := midnightBlocks.midnight_block_4338 (by omega) (by jump_dest) rd2
    change RD fork midnightBytecode I g s0 ⟨18574⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 4) :: UInt256.ofNat I.calldata.size ::
        ⟨4356⟩ :: ⟨3755⟩ :: ⟨32⟩ :: R) mem aw rdata σ _ _ at rd3
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
      rcases midnightMarketCalldataDecoder (by simp only [List.length_cons]; omega)
          hsmall (by rw [hh]; omega) (by decide) (by decide) hfree (by jump_dest) rd3 with
        ⟨hnone, hr⟩ | ⟨m, hm, hfit, mem', root, aw4, k4, C4, hroot, hstored, hf4, rd4⟩
      · left
        refine ⟨?_, hr⟩
        rw [hdecode]
        cases hm : decodeMarketData I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat with
        | none => rfl
        | some m =>
          have hc := hnone m hm
          change ¬ 1120 + 160 * m.collaterals.length < 2^64 at hc
          simp only [bind, Option.bind, hc, if_false]
      · have rd5 := midnightBlocks.midnight_block_4356
          (by simp only [List.length_cons]; omega) (by jump_dest) rd4
        refine Or.inr ⟨m, ?_, h36, hsmall, mem', root, _, _, _, hroot, hstored, hf4, rd5⟩
        rw [hdecode, hm]
        dsimp only [bind, Option.bind]
        exact if_pos hfit
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
      have rd2 := midnightBlocks.midnight_block_4321_taken (by omega)
        (by change UInt256.gt (calldataWord I.calldata 4) _ ≠ _; rw [hg]; decide)
        (by jump_dest) rd1
      exact midnightBlocks.midnight_block_712 (by
        simp only [midnightBlocks.midnight_block_4321_taken_stack, List.length_cons]; omega) rd2

end Benchmarks.Midnight

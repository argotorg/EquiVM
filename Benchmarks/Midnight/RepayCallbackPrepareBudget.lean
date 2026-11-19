import Benchmarks.Midnight.RepayCallbackPrepare
import Benchmarks.Midnight.MarketEncoderBudget
import Benchmarks.Midnight.CalldataBytesEncoderBudget

/-! Repayment callback encoding with the subsequent transfer's memory budget retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayCallbackPrepare_budget {budgetRoot : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root market arrayPtr limit id units user : UInt256}
    {callback payer dp dl : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 29 ≤ 1024) (hm : MarketStored mem market arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hroot : root.toNat < 2^128)
    (hlower : 832 ≤ root.toNat) (hmem : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hdl : dl.toNat < 2^64) (hd : dp.toNat + dl.toNat ≤ I.calldata.size)
    (ha : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10127⟩
      ([id, dp, callback, dl, user, payer, units, market] ++ R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C',
      TransferBudget budgetRoot (credit + 4 + 128 * m.collaterals.length)
        (repayCallbackMemory mem I.calldata root.toNat m id units user dp.toNat dl.toNat) aw' C' ∧
      RD midnightBytecode I g s0 ⟨10221⟩
        ([gasArg, callback, ⟨0⟩, root, UInt256.ofNat (repayCallbackSize m dl.toNat), root, ⟨32⟩,
          root, payer, units, market] ++ R)
        (repayCallbackMemory mem I.calldata root.toNat m id units user dp.toNat dl.toNat)
        aw' rdata σ k' C' := by
  have hn := hm.collateralCount
  have ho (n : Nat) (hn' : n ≤ repayCallbackSize m dl.toNat + 32) :
      (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by
      unfold repayCallbackSize returnDataAllocation at hn'
      change _ < 2^256
      omega)
  have hsel : UInt256.shiftLeft (UInt256.ofNat 172211497) (UInt256.ofNat 226) =
      UInt256.ofNat (688845988 * 2^224) := by decide +kernel
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_10127 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_10127_stack,
    midnightBlocks.midnight_block_10127_memory, hfree, hsel] at rd1
  have ha1 := transferBudgetAt (root := budgetRoot) (credit := credit + 4) rd1 (by transfer_budget ha)
  simp only [ho 4 (by unfold repayCallbackSize; omega),
    ho 36 (by unfold repayCallbackSize; omega)] at rd1 ha1
  have hp := repayCallbackHeaderMemory_prefix mem root.toNat limit.toNat id hlimit
  have hm1 := hm.preserve hp
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightMarketEncoder_budget m
    (by simp only [List.length_cons]; omega) hm1.words hm1.length
    (by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
      using hm1.header.size) hm1.collaterals (by have := hm.array; have := hm.extent; omega)
    hm.extent (by rw [ho 164 (by unfold repayCallbackSize; omega)]; omega)
    (by rw [ho 164 (by unfold repayCallbackSize; omega)]; change _ < 2^256; omega)
    (by jump_dest) ha1 rd1
  have he : 164 + (288 + 128 * m.collaterals.length) =
      452 + 128 * m.collaterals.length := by omega
  simp only [wordAddNat_add, he, List.cons_append, List.nil_append] at rd2
  have rd3 := midnightBlocks.midnight_block_10183
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_10183_stack,
    midnightBlocks.midnight_block_10183_memory, word_add_sub_left] at rd3
  have hd4 : UInt256.ofNat (452 + 128 * m.collaterals.length) + UInt256.lnot (UInt256.ofNat 3) =
      UInt256.ofNat (448 + 128 * m.collaterals.length) := by
    rw [u256_add_comm]
    have he4 : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat 452 = UInt256.ofNat 448 :=
      by decide +kernel
    rw [← wordAddNat_add, he4]
    apply u256_inj
    simp only [uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [hd4] at rd3
  have ha3 := transferBudgetAt (root := budgetRoot) (credit := credit + 4 + 128 * m.collaterals.length) rd3
    (by transfer_budget ha2)
  obtain ⟨aw4, k4, C4, hc4, ha4, rd4⟩ := midnightCalldataBytesEncoderBudget
    (by simp only [List.length_cons]; omega) hdl
    (by rw [ho (452 + 128 * m.collaterals.length) (by unfold repayCallbackSize; omega)]
        change _ < 2^256; omega) (by jump_dest) ha3 rd3
  simp only [wordAddNat_add] at rd4
  have rd5 := midnightBlocks.midnight_block_10212
    (by simp only [List.length_cons]; omega) rd4
  simp only [midnightBlocks.midnight_block_10212_stack, word_add_sub_left] at rd5
  have ha5 := transferBudgetAt (root := budgetRoot) (credit := credit + 4 + 128 * m.collaterals.length) rd5
    (by transfer_budget ha4)
  have hf := And.intro ha5 rd5
  simp only [ho 68 (by unfold repayCallbackSize; omega),
    ho 100 (by unfold repayCallbackSize; omega), ho 132 (by unfold repayCallbackSize; omega),
    ho 164 (by unfold repayCallbackSize; omega),
    ho (452 + 128 * m.collaterals.length) (by unfold repayCallbackSize; omega)] at hf
  rw [show root.toNat + (452 + 128 * m.collaterals.length) =
    root.toNat + 452 + 128 * m.collaterals.length by omega] at hf
  change TransferBudget budgetRoot _ (repayCallbackMemory mem I.calldata root.toNat m id units user
      dp.toNat dl.toNat) _ _ ∧ RD _ _ _ _ _
      (_ :: callback :: memLoad (UInt256.ofNat 800)
        (repayCallbackMemory mem I.calldata root.toNat m id units user dp.toNat dl.toNat) :: _)
      _ _ _ _ _ _ at hf
  have hz' := (repayCallbackMemory_prefix mem I.calldata root.toNat root.toNat m id units user
    dp.toNat dl.toNat le_rfl hd).load (UInt256.ofNat 800) (by decide) hlower hmem
  rw [hz', hz] at hf
  exact ⟨_, _, _, _, hf⟩

end Benchmarks.Midnight

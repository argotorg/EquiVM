import Benchmarks.Midnight.LiquidateBitmapSource
import Benchmarks.Midnight.LiquidateBitmapTrace
import Benchmarks.Midnight.LiquidateLoopSourceEntry
import Benchmarks.Midnight.TransferBudget

/-! Paired execution of the optional bitmap clear after the collateral write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateBitmap {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt value root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hn : frame.locals.get? "newCollateral" = some (.int value.toNat))
    (hvalue : value.toNat < 2^128) (hcanon : borrower.toNat < EVM.addressModulus)
    (hidx : index.toNat < 128) (hp : I.perm = true) (hi : calldataWord I.calldata 36 = index)
    (hseized : memLoad ⟨640⟩ mem = seized) (hs : SourceState s0 I σ evm)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6820⟩
      (value :: uint128Mask :: positionSlot id borrower :: R) mem aw rdata σ k C) :
    ∃ frame' evm' σ' aw' k' C',
      ExecStmt config frame evm (liquidateAmountsBody[9]!) (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      SourceState s0 I σ' evm' ∧ TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨6833⟩
        (positionSlot id borrower :: R) mem aw' rdata σ' k' C' := by
  have hg := evalLiquidateClearGuard (evm := evm) hn hf.seized
  have finishFalse {aw1 : UInt256} {k1 C1 : Nat}
      (hno : ¬ (value = ⟨0⟩ ∧ seized ≠ ⟨0⟩))
      (hb1 : TransferBudget root credit mem aw1 C1)
      (rd1 : RD midnightBytecode I g s0 ⟨6828⟩
        (⟨0⟩ :: positionSlot id borrower :: R) mem aw1 rdata σ k1 C1) :
      ∃ frame' evm' σ' aw' k' C',
        ExecStmt config frame evm (liquidateAmountsBody[9]!) (.ok frame' evm') ∧
        LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
        LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
        SourceState s0 I σ' evm' ∧ TransferBudget root credit mem aw' C' ∧
        RD midnightBytecode I g s0 ⟨6833⟩
          (positionSlot id borrower :: R) mem aw' rdata σ' k' C' := by
    have rd2 := midnightBlocks.midnight_block_6828_fallthrough
      (by simp only [List.length_cons]; omega) rfl rd1
    exact ⟨frame, evm, σ, aw1, _, _,
      ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hno])) ExecBlock.nil,
      hf, ha, hs, hb1.mono (by omega), rd2⟩
  by_cases hz : value = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_6820_taken
      (by simp only [List.length_cons]; omega)
      (by rw [uint128Mask_clean hvalue, hz]; decide) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_7002
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    have hb2 := transferBudgetAt (root := root) (credit := credit) rd2 (by transfer_budget hb)
    simp only [midnightBlocks.midnight_block_7002_stack,
      show UInt256.ofNat 640 = (⟨640⟩ : UInt256) from rfl, hseized] at rd2 hb2
    by_cases hzseized : seized = ⟨0⟩
    · apply finishFalse (by simp only [hzseized, ne_self_iff_false, and_false, not_false_eq_true]) hb2
      simpa only [hzseized, show UInt256.isZero (UInt256.isZero ⟨0⟩) = ⟨0⟩ from rfl] using rd2
    · have rd3 := midnightBlocks.midnight_block_6828_taken
        (by simp only [List.length_cons]; omega)
        (by rw [isZero_eq_zero_of_ne hzseized]; decide) (by jump_dest) rd2
      obtain ⟨k4, C4, hc4, rd4⟩ := midnightLiquidateBitmapWrite (R := R)
        (by omega) hp hi hs rd3
      let cleared := bitmapClear (positionBitmapWord evm id borrower) index
      have hs4 := SourceState.storeHigh128 hs (positionSlot id borrower + ⟨2⟩) cleared
      have hx4 : ExecStmt config frame evm (liquidateAmountsBody[9]!)
          (.ok (wordLocal frame "__c28" cleared)
            (storeHigh128 evm (positionSlot id borrower + ⟨2⟩) cleared)) :=
        ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true ⟨hz, hzseized⟩]))
          (liquidateBitmapSource hf hcanon hidx (by rw [hs.env]; exact hp))
      refine ⟨wordLocal frame "__c28" cleared,
        storeHigh128 evm (positionSlot id borrower + ⟨2⟩) cleared,
        storeHigh128Accounts σ I (positionSlot id borrower + ⟨2⟩) cleared,
        M aw ⟨640⟩ ⟨32⟩, k4, C4, hx4,
        hf.insert "__c28" (.int cleared.toNat) (by decide),
        ha.insert "__c28" (.int cleared.toNat) (by decide),
        ?_, ?_, ?_⟩
      · exact hs4
      · exact hb2.mono (by omega)
      · exact rd4
  · have rd1 := midnightBlocks.midnight_block_6820_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [uint128Mask_clean hvalue]; exact isZero_eq_zero_of_ne hz) rd
    apply finishFalse (C1 := C + 23) (k1 := k + 6)
      (by simp only [hz, false_and, not_false_eq_true]) (hb.mono (by omega))
    simpa only [midnightBlocks.midnight_block_6820_fallthrough_stack,
      uint128Mask_clean hvalue, isZero_eq_zero_of_ne hz] using rd1

end Benchmarks.Midnight

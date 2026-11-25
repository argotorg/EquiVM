import Benchmarks.Midnight.LiquidateLoopSourceEntry
import Benchmarks.Midnight.LiquidateOracleReturn

variable {fork : Ethereum.Fork}

/-! Save the oracle price only for the collateral selected for liquidation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidatePriceFrame (frame : Frame) (index target price : UInt256) : Frame :=
  if index = target then wordLocal frame "liquidatedCollatPrice" price else frame

theorem liquidatePriceSource {frame : Frame} {evm : State} {index target price oldPrice : UInt256}
    (hi : frame.locals.get? "i" = some (.int index.toNat))
    (ht : frame.locals.get? "collateralIndex" = some (.int target.toNat))
    (hp : frame.locals.get? "price" = some (.int price.toNat))
    (ho : frame.locals.get? "liquidatedCollatPrice" = some (.int oldPrice.toNat)) :
    ExecStmt fork config frame evm (liquidateLoopBody[3]!)
      (.ok (liquidatePriceFrame frame index target price) evm) := by
  have hc : evalExpr? config frame evm (.binary .eq (.var "i") (.var "collateralIndex")) =
      .ok (.bool (decide (index = target))) := by
    simp only [evalExpr?, hi, ht, EvalResult.ofOption, bind, pure, EvalResult.bind,
      evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq, Int.natCast_inj]
    simp only [show index.toNat = target.toNat ↔ index = target from
      ⟨u256_inj, congrArg UInt256.toNat⟩]
  by_cases he : index = target
  · rw [liquidatePriceFrame, if_pos he]
    exact ExecStmt.iteTrue (hc.trans (by rw [decide_eq_true he]))
      (ExecBlock.consNormal (execLocalAssign ho (evalWordLocal hp)) (ExecBlock.nil ..))
  · rw [liquidatePriceFrame, if_neg he]
    exact ExecStmt.iteFalse (hc.trans (by rw [decide_eq_false he])) (ExecBlock.nil ..)

theorem LiquidateAccumulators.setPrice {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt) (p : UInt256) :
    LiquidateAccumulators (wordLocal frame "liquidatedCollatPrice" p)
      bitmap maxDebt p originalDebt badDebt := by
  rcases h with ⟨hb, hm, hp, ho, hd⟩
  constructor <;> simp_all [wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem liquidatePriceFrame_accumulators {frame : Frame}
    {bitmap maxDebt oldPrice originalDebt badDebt index target price : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt oldPrice originalDebt badDebt) :
    LiquidateAccumulators (liquidatePriceFrame frame index target price)
      bitmap maxDebt (if index = target then price else oldPrice) originalDebt badDebt := by
  by_cases he : index = target
  · simp only [liquidatePriceFrame, if_pos he]
    exact h.setPrice price
  · simpa only [liquidatePriceFrame, if_neg he] using h

theorem liquidatePriceFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode target price : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (h : LiquidateSourceFrame frame m id target seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidatePriceFrame frame index target price)
      m id target seized repaid borrower mode receiver callback data := by
  by_cases he : index = target
  · simp only [liquidatePriceFrame, if_pos he]
    exact h.insert _ _ (by decide)
  · simpa only [liquidatePriceFrame, if_neg he] using h

theorem midnightLiquidatePriceChoice {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root cp badDebt reverseRep rep maxDebt oldPrice pos dp dl borrower
      debtWord receiver mode selector price bitmap budgetRoot : UInt256}
    {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hfork : fork ≥ .osaka)
    (hp : memLoad root mem = price) (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨8252⟩
      ([root, cp, badDebt, reverseRep, rep, maxDebt, oldPrice, pos, dp, dl, borrower,
        debtWord, receiver, mode, selector] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨7967⟩
        ([maxDebt, cp, badDebt, reverseRep, rep, price,
          if bitmapMsb bitmap = calldataWord I.calldata 36 then price else oldPrice,
          pos, dp, dl, borrower, debtWord, receiver, mode, selector] ++ R)
        mem aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_8252 (R := R) (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_8252_stack, hp] at rd1
  have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1
    (by transfer_budget hb)
  by_cases he : bitmapMsb bitmap = calldataWord I.calldata 36
  · have hc : UInt256.eq (bitmapMsb bitmap) (calldataWord I.calldata 36) ≠ ⟨0⟩ := by
      rw [he, uInt256_eq_self]
      decide
    have rd2 := midnightBlocks.midnight_block_7949_taken
      (by simp only [List.length_cons]; omega) hfork
      (by rw [hbitmap]; exact hc) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_8207
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    have hb3 := transferBudgetAt (root := budgetRoot) (credit := credit) rd3
      (by transfer_budget hb1)
    rw [if_pos he]
    exact ⟨_, _, _, hb3, rd3⟩
  · have hc : UInt256.eq (bitmapMsb bitmap) (calldataWord I.calldata 36) = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ he (uInt256_eq_one_eq h))
    have rd2 := midnightBlocks.midnight_block_7949_fallthrough
      (by simp only [List.length_cons]; omega) hfork (by rw [hbitmap]; exact hc) rd1
    have hb2 := transferBudgetAt (root := budgetRoot) (credit := credit) rd2
      (by transfer_budget hb1)
    rw [if_neg he]
    exact ⟨_, _, _, hb2, rd2⟩

end Benchmarks.Midnight

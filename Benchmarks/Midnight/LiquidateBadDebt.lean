import Benchmarks.Midnight.LiquidateBadDebtBranch
import Benchmarks.Midnight.RuntimeBlocks_023

variable {fork : Ethereum.Fork}

/-! The full optional bad-debt update, returning to the liquidation amount calculation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateBadDebt {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {receiver callback : AccountAddress} {data mem rdata : ByteArray}
    {aw root debtWord reverseRep rep maxDebt price id index seized repaid dp dl borrower
      mode bitmap originalDebt badDebt receiverWord selector : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256} (hstack : R.length + 26 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hdebt : healthPositionWord evm id borrower = debtWord)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨5463⟩
      ([debtWord, reverseRep, rep, maxDebt, price, positionSlot id borrower, dp, dl,
        borrower, badDebt, receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecStmt fork config frame evm (liquidateTransition.body[17]!) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecStmt fork config frame evm (liquidateTransition.body[17]!) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (∃ frame' evm' σ' head aw' k' C', SourceState s0 I σ' evm' ∧
      ExecStmt fork config frame evm (liquidateTransition.body[17]!) (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      TransferBudget root credit mem aw' C' ∧ RD fork midnightBytecode I g s0 ⟨5468⟩
        ([head, reverseRep, rep, maxDebt, price, positionSlot id borrower, dp, dl,
          borrower, badDebt, receiverWord, mode, selector] ++ R) mem aw' rdata σ' k' C') := by
  have hcond : evalExpr? config frame evm (.binary .gt (.var "badDebt") (.intLit 0)) =
      .ok (.bool (decide (0 < badDebt.toNat))) := by
    simp only [evalExpr?, ha.badDebt, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?]
    norm_num
  by_cases hz : badDebt = ⟨0⟩
  · have hfalse : evalExpr? config frame evm (.binary .gt (.var "badDebt") (.intLit 0)) =
        .ok (.bool false) := by simpa only [hz] using hcond
    have hex : ExecStmt fork config frame evm (liquidateTransition.body[17]!) (.ok frame evm) :=
      ExecStmt.iteFalse hfalse ExecBlock.nil
    have rd1 := midnightBlocks.midnight_block_5463_fallthrough
      (R := receiverWord :: mode :: selector :: R)
      (by simp only [List.length_cons]; omega) hz rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (hb.mono (by omega))
    exact Or.inr (Or.inr ⟨frame, evm, σ, debtWord, _, _, _, hs, hex, hf, ha, hb1, rd1⟩)
  · have hpos : 0 < badDebt.toNat := by
      by_contra hn
      exact hz (uint256_toNat_eq_zero (by omega))
    have htrue := hcond.trans (by rw [decide_eq_true hpos])
    have rd1 := midnightBlocks.midnight_block_5463_taken
      (R := receiverWord :: mode :: selector :: R)
      (by simp only [List.length_cons]; omega) hz (by jump_dest) rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (hb.mono (by omega))
    rcases midnightLiquidateBadDebtBranch
      (R := receiverWord :: mode :: selector :: R)
      (by simp only [List.length_cons]; omega) hf ha hcanon hdebt hslot hzero hs hb1 rd1 with
      ⟨hex, hrev⟩ | ⟨hex, hstatic⟩ | ⟨frame2, evm2, σ2, aw2, k2, C2, hs2, hex, hf2, ha2, hb2, rd2⟩
    · exact Or.inl ⟨ExecStmt.iteTrue htrue hex, hrev⟩
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue htrue hex, hstatic⟩)
    · have rd3 := midnightBlocks.midnight_block_7768 (R := R) (by omega) (by jump_dest) rd2
      simp only [midnightBlocks.midnight_block_7768_stack] at rd3
      have hb3 := transferBudgetAt (root := root) (credit := credit) rd3 (hb2.mono (by omega))
      exact Or.inr (Or.inr ⟨frame2, evm2, σ2, selector, _, _, _, hs2,
        ExecStmt.iteTrue htrue hex, hf2, ha2, hb3, rd3⟩)

end Benchmarks.Midnight

import Benchmarks.Midnight.LiquidateMaxRepaidStep
import Benchmarks.Midnight.LiquidateCapGuard
import Benchmarks.Midnight.LiquidateThresholdStep

/-! The complete enabled recovery-threshold branch: repayment cap, optional valuation, and check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateRcfCheck {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt lltv lif dp dl receiverWord selector root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 22 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hll : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hl : frame.locals.get? "lif" = some (.int lif.toNat))
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hd : decodeCalldataMarket I.calldata 4 = some m) (hi : calldataWord I.calldata 36 = index)
    (hmr : memLoad (UInt256.ofNat 608) mem = repaid)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7014⟩
      ([maxDebt, lltv, lif, price, positionSlot id borrower, dp, dl, borrower, badDebt,
        receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm liquidateRcfBody .reverted ∧ RDrev midnightBytecode g s0) ∨
    ∃ frame' aw' k' C', ExecBlock config frame evm liquidateRcfBody (.ok frame' evm) ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨6744⟩
        ([selector, selector, selector, selector, positionSlot id borrower, dp, dl, borrower,
          badDebt, receiverWord, mode, selector] ++ R) mem aw' rdata σ k' C' := by
  rcases liquidateMaxRepaidStep
    (R := [dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hf.contract hcanon hf.position ha.maxDebt hl hll hs hb rd with
    ⟨hsrev, hrev⟩ | ⟨hs0, k1, C1, hb1, rd1⟩
  · exact Or.inl ⟨ExecBlock.consRevert hsrev, hrev⟩
  · let cap := liquidateMaxRepaid (low128 (healthPositionWord evm id borrower)) maxDebt lif lltv
    let f1 := wordLocal frame "maxRepaid" cap
    have hf1 : LiquidateSourceFrame f1 m id index seized repaid borrower mode receiver callback data :=
      hf.insert _ _ (by decide)
    have ha1 : LiquidateAccumulators f1 bitmap maxDebt price originalDebt badDebt :=
      ha.insert _ _ (by decide)
    have hcap : f1.locals.get? "maxRepaid" = some (.int cap.toNat) := wordLocal_get _ _ _
    have hl1 : f1.locals.get? "lif" = some (.int lif.toNat) := by
      simpa only [f1, wordLocal_get_ne _ _ _ _ (show "maxRepaid" ≠ "lif" by decide)] using hl
    have hcond : evalExpr? config f1 evm (.binary .gt (.var "repaidUnits") (.var "maxRepaid")) =
        .ok (.bool (decide (cap.toNat < repaid.toNat))) := by
      simp only [evalExpr?, hf1.repaid, hcap, EvalResult.ofOption, bind, pure,
        EvalResult.bind, evalBinaryOp?, Int.ofNat_lt]
    rcases midnightLiquidateCapGuard (R := R) (by omega) hmr hb1 rd1 with
      ⟨hlt, aw2, k2, C2, hb2, rd2⟩ | ⟨hle, aw2, k2, C2, hb2, rd2⟩
    · rcases liquidateThresholdStep (R := R) hstack hf1 ha1 hl1 hcap hcanon hd hi hs hb2 rd2 with
        ⟨hsrev, hrev⟩ | ⟨f3, k3, C3, hsok, hf3, ha3, hb3, rd3⟩
      · exact Or.inl ⟨ExecBlock.consNormal hs0 (ExecBlock.consRevert
          (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true hlt])) hsrev)), hrev⟩
      · exact Or.inr ⟨f3, aw2, k3, C3, ExecBlock.consNormal hs0
          (ExecBlock.consNormal (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true hlt])) hsok)
            ExecBlock.nil), hf3, ha3, hb3, rd3⟩
    · exact Or.inr ⟨f1, aw2, k2, C2, ExecBlock.consNormal hs0
        (ExecBlock.consNormal (ExecStmt.iteFalse
          (hcond.trans (by rw [decide_eq_false (Nat.not_lt.mpr hle)])) ExecBlock.nil)
          ExecBlock.nil), hf1, ha1, hb2, rd2⟩

end Benchmarks.Midnight

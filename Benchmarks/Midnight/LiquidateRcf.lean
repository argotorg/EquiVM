import Benchmarks.Midnight.LiquidateRcfGuard
import Benchmarks.Midnight.LiquidateRcfCheck

variable {fork : Ethereum.Fork}

/-! Source/runtime agreement for liquidation's conditional repayment-cap and recovery check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateRcf {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
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
    (rd : RD fork midnightBytecode I g s0 ⟨6731⟩
      ([maxDebt, lltv, lif, price, positionSlot id borrower, dp, dl, borrower, badDebt,
        receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecStmt fork config frame evm (liquidateAmountsBody[5]!) .reverted ∧ RDrev fork midnightBytecode g s0) ∨
    ∃ frame' d0 d1 d2 d3 aw' k' C',
      ExecStmt fork config frame evm (liquidateAmountsBody[5]!) (.ok frame' evm) ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      TransferBudget root credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨6744⟩
        ([d0, d1, d2, d3, positionSlot id borrower, dp, dl, borrower, badDebt,
          receiverWord, mode, selector] ++ R) mem aw' rdata σ k' C' := by
  have hcond := evalLiquidateRcfGuard (evm := evm) hf.mode hll
  rcases midnightLiquidateRcfGuard (R := selector :: R)
    (by simp only [List.length_cons]; omega) rd with
    ⟨henabled, k1, C1, hc1, rd1⟩ | ⟨hdisabled, k1, C1, hc1, rd1⟩
  · change mode = ⟨0⟩ ∧ lltv.toNat < lifScale.toNat at henabled
    rcases liquidateRcfCheck (R := R) hstack hf ha hll hl hcanon hd hi hmr hs (hb.mono hc1) rd1 with
      ⟨hsrev, hrev⟩ | ⟨f2, aw2, k2, C2, hsok, hf2, ha2, hb2, rd2⟩
    · exact Or.inl ⟨ExecStmt.iteTrue
        (hcond.trans (by rw [decide_eq_true henabled])) hsrev, hrev⟩
    · exact Or.inr ⟨f2, selector, selector, selector, selector, aw2, k2, C2,
        ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true henabled])) hsok,
        hf2, ha2, hb2, rd2⟩
  · change ¬ (mode = ⟨0⟩ ∧ lltv.toNat < lifScale.toNat) at hdisabled
    exact Or.inr ⟨frame, maxDebt, lltv, lif, price, aw, k1, C1,
      ExecStmt.iteFalse (hcond.trans (by rw [decide_eq_false hdisabled])) ExecBlock.nil,
      hf, ha, hb.mono hc1, rd1⟩

end Benchmarks.Midnight

import Benchmarks.Midnight.LiquidateBadDebtHead
import Benchmarks.Midnight.LiquidateBadDebtTail
import Benchmarks.Midnight.LiquidateBadDebtFrames

/-! The complete nonzero-bad-debt branch, including all arithmetic and static failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateBadDebtBranch {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {receiver callback : AccountAddress} {data mem rdata : ByteArray}
    {aw root debtWord reverseRep rep maxDebt price id index seized repaid dp dl borrower
      mode bitmap originalDebt badDebt : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256} (hstack : R.length + 23 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hdebt : healthPositionWord evm id borrower = debtWord)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7431⟩
      ([debtWord, reverseRep, rep, maxDebt, price, positionSlot id borrower, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm liquidateBadDebtBody .reverted ∧ RDrev midnightBytecode g s0) ∨
    (ExecBlock config frame evm liquidateBadDebtBody .staticViolation ∧ RDstatic midnightBytecode g s0) ∨
    (∃ frame' evm' σ' aw' k' C', SourceState s0 I σ' evm' ∧
      ExecBlock config frame evm liquidateBadDebtBody (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      TransferBudget root credit mem aw' C' ∧ RD midnightBytecode I g s0 ⟨7768⟩
        ([reverseRep, rep, maxDebt, price, positionSlot id borrower, dp, dl, borrower, badDebt] ++ R)
        mem aw' rdata σ' k' C') := by
  rcases midnightLiquidateBadDebtHead hstack hcanon hf.contract hf.position hf.marketState
    ha.badDebt hdebt hslot hs hb rd with
    ⟨hex, hrev⟩ | ⟨hex, hstatic⟩ | ⟨hp, σ1, aw1, k1, C1, hs1, hex1, hb1, rd1⟩
  · refine Or.inl ⟨?_, hrev⟩
    simpa only [List.take_append_drop] using
      execBlockAppendReverted (suff := liquidateBadDebtBody.drop 5) hex
  · refine Or.inr (Or.inl ⟨?_, hstatic⟩)
    simpa only [List.take_append_drop] using execBlock_append_term
      (s2 := liquidateBadDebtBody.drop 5) hex (by intro _ _ h; cases h)
  · let evm1 := liquidateBadDebtState evm id borrower badDebt
    let word := liquidateBadDebtMarketWord evm id borrower badDebt
    let total := low128 word
    let loss := UInt256.shiftRight word ⟨128⟩
    let newLoss := liquidateNextLoss total loss badDebt
    let frame1 := liquidateLossFrame frame total loss badDebt
    have hf1 : LiquidateSourceFrame frame1 m id index seized repaid borrower mode receiver callback data :=
      liquidateLossFrame_arguments hf
    have ha1 : LiquidateAccumulators frame1 bitmap maxDebt price originalDebt badDebt :=
      liquidateLossFrame_accumulators ha
    have hl1 : frame1.locals.get? "__c13" = some (.int newLoss.toNat) := wordLocal_get _ _ _
    have ho1 : frame1.locals.get? "_lossFactor" = some (.int loss.toNat) :=
      liquidateLossFrame_loss frame total loss badDebt
    rcases midnightLiquidateBadDebtTail (frame := frame1) (R := R) (by omega)
      hf1.contract hf1.marketState hl1 ho1 ha1.badDebt hslot hzero hp hs1 hb1 rd1 with
      ⟨hex2, hrev⟩ | ⟨σ2, aw2, k2, C2, hs2, hex2, hb2, rd2⟩
    · refine Or.inl ⟨?_, hrev⟩
      simpa only [List.take_append_drop] using execBlock_append_ok hex1 hex2
    · let evm2 := liquidateTotalState evm1 id newLoss badDebt
      let amount := liquidateFeeValue evm2 id loss
      let frame2 := liquidateFeeFrame (wordLocal frame1 "__c14" badDebt) loss amount
      have hf2 : LiquidateSourceFrame frame2 m id index seized repaid borrower mode receiver callback data :=
        liquidateFeeFrame_arguments (hf1.insert "__c14" (.int badDebt.toNat) (by decide))
      have ha2 : LiquidateAccumulators frame2 bitmap maxDebt price originalDebt badDebt :=
        liquidateFeeFrame_accumulators (ha1.insert "__c14" (.int badDebt.toNat) (by decide))
      have hex : ExecBlock config frame evm liquidateBadDebtBody
          (.ok frame2 (marketBalanceStore evm2 id 2 amount)) := by
        simpa only [List.take_append_drop] using execBlock_append_ok hex1 hex2
      exact Or.inr (Or.inr ⟨frame2, _, σ2, aw2, k2, C2, hs2, hex, hf2, ha2, hb2, rd2⟩)

end Benchmarks.Midnight

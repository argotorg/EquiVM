import Benchmarks.Midnight.LiquidateCollateralUpdate
import Benchmarks.Midnight.LiquidateBitmap
import Benchmarks.Midnight.LiquidateBalances

/-! The collateral, bitmap, market-balance, and debt writes in the amount branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateAmountsTail {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt d0 d1 d2 d3 dp dl receiverWord selector root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus) (hi : calldataWord I.calldata 36 = index)
    (hseized : memLoad ⟨640⟩ mem = seized) (hpaid : memLoad ⟨608⟩ mem = repaid)
    (hslot : memLoad ⟨672⟩ mem = solcMappingSlot ⟨1⟩ id)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6744⟩
      ([d0, d1, d2, d3, positionSlot id borrower, dp, dl, borrower, badDebt,
        receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (liquidateAmountsBody.drop 6) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    (ExecBlock config frame evm (liquidateAmountsBody.drop 6) .staticViolation ∧
      RDstatic midnightBytecode g s0) ∨
    ∃ frame' evm' σ' aw' k' C',
      ExecBlock config frame evm (liquidateAmountsBody.drop 6) (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      SourceState s0 I σ' evm' ∧ TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨5480⟩
        ([selector, selector, selector, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
        mem aw' rdata σ' k' C' := by
  rcases liquidateCollateralUpdate
    (R := [dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hf ha hcanon hi hseized hs hb rd with ⟨hx, hr⟩ | ⟨hx, hr⟩ |
      ⟨hp, hidx, f1, evm1, σ1, value, aw1, k1, C1, hx1, hf1, ha1, hn1, hv1, hs1, hb1, rd1⟩
  · exact Or.inl ⟨execBlockAppendReverted (suff := liquidateAmountsBody.drop 9) hx, hr⟩
  · exact Or.inr (Or.inl ⟨execBlock_append_term
      (s2 := liquidateAmountsBody.drop 9) hx (by intro _ _ h; cases h), hr⟩)
  · obtain ⟨f2, evm2, σ2, aw2, k2, C2, hx2, hf2, ha2, hs2, hb2, rd2⟩ := liquidateBitmap
      (R := [dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hf1 ha1 hn1 hv1 hcanon hidx hp hi hseized hs1 hb1 rd1
    rcases liquidateBalances (R := R) (by omega) hf2 ha2 hcanon hp hpaid hslot hs2 hb2 rd2 with
      ⟨hx, hr⟩ | ⟨f3, evm3, σ3, aw3, k3, C3, hx3, hf3, ha3, hs3, hb3, rd3⟩
    · exact Or.inl ⟨execBlockAppendRevert hx1 (ExecBlock.consNormal hx2 hx), hr⟩
    · exact Or.inr (Or.inr ⟨f3, evm3, σ3, aw3, k3, C3,
        execBlockAppendOk hx1 (ExecBlock.consNormal hx2 hx3), hf3, ha3, hs3, hb3, rd3⟩)

end Benchmarks.Midnight

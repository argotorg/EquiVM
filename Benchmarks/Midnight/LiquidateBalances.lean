import Benchmarks.Midnight.LiquidateWithdrawable
import Benchmarks.Midnight.LiquidateDebtUpdate

variable {fork : Ethereum.Fork}

/-! Ordered market-balance and borrower-debt updates at the end of the amount branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateBalances {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt dp dl receiverWord selector root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 18 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus) (hp : I.perm = true)
    (hpaid : memLoad ⟨608⟩ mem = repaid)
    (hslot : memLoad ⟨672⟩ mem = solcMappingSlot ⟨1⟩ id)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨6833⟩
      ([positionSlot id borrower, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (liquidateAmountsBody.drop 10) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ frame' evm' σ' aw' k' C',
      ExecBlock fork config frame evm (liquidateAmountsBody.drop 10) (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      SourceState s0 I σ' evm' ∧ TransferBudget root credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨5480⟩
        ([selector, selector, selector, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
        mem aw' rdata σ' k' C' := by
  rcases liquidateWithdrawable
    (R := [positionSlot id borrower, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hf hp hpaid hslot hs hb rd with ⟨hx, hr⟩ | ⟨h128, evm1, σ1, aw1, k1, C1, hx1, hs1, hb1, rd1⟩
  · exact Or.inl ⟨execBlockAppendReverted (suff := liquidateAmountsBody.drop 12) hx, hr⟩
  · have hf1 := hf.insert "__c29" (.int repaid.toNat) (by decide)
    rcases liquidateDebtUpdate (R := R) (by omega) hf1 hp h128 hcanon hs1 hb1 rd1 with
      ⟨hx, hr⟩ | ⟨evm2, σ2, k2, C2, hx2, hs2, hb2, rd2⟩
    · exact Or.inl ⟨execBlockAppendRevert hx1 hx, hr⟩
    · exact Or.inr ⟨_, evm2, σ2, aw1, k2, C2, execBlockAppendOk hx1 hx2,
        hf1.insert "__c30" (.int repaid.toNat) (by decide),
        (ha.insert "__c29" (.int repaid.toNat) (by decide)).insert
          "__c30" (.int repaid.toNat) (by decide), hs2, hb2, rd2⟩

end Benchmarks.Midnight

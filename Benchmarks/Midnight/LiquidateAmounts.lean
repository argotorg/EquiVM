import Benchmarks.Midnight.LiquidateAmountsHead
import Benchmarks.Midnight.LiquidateAmountsTail

/-! Complete paired execution of the nonzero liquidation-amount branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateAmounts {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt dp dl receiverWord selector root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 23 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hd : decodeCalldataMarket I.calldata 4 = some m) (hi : calldataWord I.calldata 36 = index)
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hms : memLoad ⟨640⟩ mem = seized) (hmr : memLoad ⟨608⟩ mem = repaid)
    (hslot : memLoad ⟨672⟩ mem = solcMappingSlot ⟨1⟩ id)
    (hsize : 704 ≤ mem.size) (hs : SourceState s0 I σ evm)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6477⟩
      ([maxDebt, price, positionSlot id borrower, dp, dl, borrower, badDebt, receiverWord,
        mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm liquidateAmountsBody .reverted ∧ RDrev midnightBytecode g s0) ∨
    (ExecBlock config frame evm liquidateAmountsBody .staticViolation ∧
      RDstatic midnightBytecode g s0) ∨
    ∃ frame' evm' σ' seized' repaid' mem' aw' k' C',
      ExecBlock config frame evm liquidateAmountsBody (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized' repaid' borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      SourceState s0 I σ' evm' ∧ memLoad ⟨640⟩ mem' = seized' ∧ memLoad ⟨608⟩ mem' = repaid' ∧
      mem.size ≤ mem'.size ∧
      (∀ read : UInt256, read.toNat + 32 ≤ mem.size →
        (read.toNat + 32 ≤ 608 ∨ 672 ≤ read.toNat) → memLoad read mem' = memLoad read mem) ∧
      TransferBudget root credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨5480⟩
        ([selector, selector, selector, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
        mem' aw' rdata σ' k' C' := by
  rcases liquidateAmountsHead hstack hf ha hcanon hd hi hcs hcr hms hmr (by omega) hs hb rd with
    ⟨hx, hr⟩ | ⟨f1, seized1, repaid1, mem1, d0, d1, d2, d3, aw1, k1, C1,
      hx1, hf1, ha1, hms1, hmr1, hsize1, hmem1, hb1, rd1⟩
  · exact Or.inl ⟨execBlockAppendReverted (suff := liquidateAmountsBody.drop 6) hx, hr⟩
  · have hslot1 : memLoad ⟨672⟩ mem1 = solcMappingSlot ⟨1⟩ id :=
      (hmem1 ⟨672⟩ hsize (Or.inr (by decide))).trans hslot
    rcases liquidateAmountsTail (R := R) (by omega) hf1 ha1 hcanon hi hms1 hmr1 hslot1
      hs hb1 rd1 with ⟨hx, hr⟩ | ⟨hx, hr⟩ |
        ⟨f2, evm2, σ2, aw2, k2, C2, hx2, hf2, ha2, hs2, hb2, rd2⟩
    · exact Or.inl ⟨execBlockAppendRevert hx1 hx, hr⟩
    · exact Or.inr (Or.inl ⟨execBlockAppendOk hx1 hx, hr⟩)
    · exact Or.inr (Or.inr ⟨f2, evm2, σ2, seized1, repaid1, mem1, aw2, k2, C2,
        execBlockAppendOk hx1 hx2, hf2, ha2, hs2, hms1, hmr1, hsize1, hmem1, hb2, rd2⟩)

end Benchmarks.Midnight

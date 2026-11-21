import Benchmarks.Midnight.LiquidateIncentive
import Benchmarks.Midnight.LiquidateAmountsConversion
import Benchmarks.Midnight.LiquidateRcf

/-! Paired execution of liquidation's incentive, amount conversion, and recovery-threshold check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateAmountsHead {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
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
    (hsize : 672 ≤ mem.size) (hs : SourceState s0 I σ evm)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6477⟩
      ([maxDebt, price, positionSlot id borrower, dp, dl, borrower, badDebt, receiverWord,
        mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (liquidateAmountsBody.take 6) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ frame' seized' repaid' mem' d0 d1 d2 d3 aw' k' C',
      ExecBlock config frame evm (liquidateAmountsBody.take 6) (.ok frame' evm) ∧
      LiquidateSourceFrame frame' m id index seized' repaid' borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      memLoad ⟨640⟩ mem' = seized' ∧ memLoad ⟨608⟩ mem' = repaid' ∧
      mem.size ≤ mem'.size ∧
      (∀ read : UInt256, read.toNat + 32 ≤ mem.size →
        (read.toNat + 32 ≤ 608 ∨ 672 ≤ read.toNat) → memLoad read mem' = memLoad read mem) ∧
      TransferBudget root credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨6744⟩
        ([d0, d1, d2, d3, positionSlot id borrower, dp, dl, borrower, badDebt,
          receiverWord, mode, selector] ++ R) mem' aw' rdata σ k' C' := by
  rcases liquidateIncentive (R := selector :: R)
    (by simp only [List.length_cons]; omega) hf ha hs.env hd hi hb rd with
    ⟨hsrev, hrev⟩ | ⟨f1, lltv, lif, k1, C1, hs1, hf1, ha1, hll1, hl1, hb1, rd1⟩
  · exact Or.inl ⟨execBlockAppendReverted
      (suff := [liquidateAmountsBody[4]!, liquidateAmountsBody[5]!]) hsrev, hrev⟩
  · rcases liquidateAmountsConversion
      (R := [positionSlot id borrower, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hf1 ha1 hll1 hl1 hcs hcr hms hmr hsize hb1 rd1 with
      ⟨hsrev, hrev⟩ | ⟨f2, seized2, repaid2, mem2, aw2, k2, C2, hs2, hf2, ha2, hll2, hl2,
        hms2, hmr2, hsize2, hmem2, hb2, rd2⟩
    · exact Or.inl ⟨execBlockAppendRevert (suff := [liquidateAmountsBody[4]!,
        liquidateAmountsBody[5]!]) hs1 (ExecBlock.consRevert hsrev), hrev⟩
    · rcases liquidateRcf (R := R) (by omega) hf2 ha2 hll2 hl2 hcanon hd hi hmr2 hs hb2 rd2 with
        ⟨hsrev, hrev⟩ | ⟨f3, d0, d1, d2, d3, aw3, k3, C3, hs3, hf3, ha3, hb3, rd3⟩
      · exact Or.inl ⟨execBlockAppendRevert hs1
          (ExecBlock.consNormal hs2 (ExecBlock.consRevert hsrev)), hrev⟩
      · exact Or.inr ⟨f3, seized2, repaid2, mem2, d0, d1, d2, d3, aw3, k3, C3,
          execBlockAppendOk hs1 (ExecBlock.consNormal hs2 (ExecBlock.consNormal hs3 ExecBlock.nil)),
          hf3, ha3, hms2, hmr2, hsize2, hmem2, hb3, rd3⟩

end Benchmarks.Midnight

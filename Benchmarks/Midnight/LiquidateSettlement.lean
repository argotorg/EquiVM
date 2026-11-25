import Benchmarks.Midnight.LiquidateAmountsPhase
import Benchmarks.Midnight.LiquidateTail

variable {fork : Ethereum.Fork}

/-! Calculate liquidation amounts, choose the payer, and execute the event and transfers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateSettlement {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root id index seized repaid borrower mode bitmap maxDebt price originalDebt badDebt
      head dp dl saved : UInt256} {receiver callback : AccountAddress} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 26 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index)
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size) (hused : root.toNat ≤ mem.size)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5468⟩
      ([head, UInt256.isZero (UInt256.isZero repaid), UInt256.isZero repaid, maxDebt, price,
        positionSlot id borrower, dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, mode,
        saved] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 18) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 18) .staticViolation ∧
      RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm' seized' repaid',
      ExecBlock fork config frame evm (liquidateTransition.body.drop 18)
        (.returned frame' evm' (some [.int seized'.toNat, .int repaid'.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized', repaid']) := by
  rcases liquidateAmountsPhase (R := R) (by omega) hf ha hcanon hd hi hcs hcr hseized hpaid hslot
      (by omega) hs hh.funding.budget rd with
    ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨f1, evm1, σ1, seized1, repaid1, mem1, d0, d1, d2, aw1, k1, C1,
      hx1, hf1, ha1, hs1, hseized1, hpaid1, hsize1, hkeep, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hx, hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ExecBlock.consStatic hx, hr⟩))
  · have hk (read : UInt256) (hin : read.toNat + 32 ≤ 832)
        (hdisj : read.toNat + 32 ≤ 608 ∨ 672 ≤ read.toNat) :
        memLoad read mem1 = memLoad read mem := hkeep read (hin.trans hsize) hdisj
    obtain ⟨aw2, k2, C2, hb2, rd2⟩ := midnightLiquidatePayer (R := saved :: R)
      (by simp only [List.length_cons]; omega)
      ((hk _ (by decide) (Or.inr (by decide))).trans hcallback) hb1 rd1
    have hxpay := liquidatePayerSource (fork := fork) (evm := evm1) hf1.callback
    rw [hs1.env] at hxpay
    have hf2 := hf1.insert "payer" (.address (repayPayer I callback)) (by decide)
    have hpay2 : (repayPayerFrame f1 I callback).locals.get? "payer" =
        some (.address (repayPayer I callback)) := store_get_self ..
    have hbad2 : (repayPayerFrame f1 I callback).locals.get? "badDebt" =
        some (.int badDebt.toNat) := (store_get_ne _ _ (by decide)).trans ha1.badDebt
    have hh2 : TransferHeap mem1 aw2 root C2 :=
      ⟨hh.size.trans hsize1, hh.lower, (hk _ (by decide) (Or.inl (by decide))).trans hh.free,
        (hk _ (by decide) (Or.inl (by decide))).trans hh.zero,
        (hused.trans hsize1).trans hb2.funding.covered, hh.aligned, hb2.funding⟩
    rcases midnightLiquidateTail hstack hf2 hbad2 hpay2 hd hi hlo (hsize.trans hsize1)
        (hused.trans hsize1) ((hk _ (by decide) (Or.inr (by decide))).trans hid)
        ((hk _ (by decide) (Or.inr (by decide))).trans hz)
        ((hk _ (by decide) (Or.inr (by decide))).trans hcallback) hcanon hseized1 hpaid1
        ((hk _ (by decide) (Or.inr (by decide))).trans hslot) hdl hdata hh2 hgas hfork hs1 rd2 with
      hoog | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨frame', evm', ht, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨.consNormal hx1 (.consNormal hxpay ht), hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨.consNormal hx1 (.consNormal hxpay ht), hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', seized1, repaid1,
        .consNormal hx1 (.consNormal hxpay ht), hr⟩))

end Benchmarks.Midnight

import Benchmarks.Midnight.LiquidateEvent
import Benchmarks.Midnight.LiquidateTransfers
import Benchmarks.Midnight.FundingBudget

/-! Liquidation's event, transfers, callback, and returned amounts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateTail {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root id index seized repaid borrower mode dp dl badDebt saved : UInt256}
    {receiver callback payer : AccountAddress} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 26 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hbad : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hpay : frame.locals.get? "payer" = some (.address payer))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size) (hused : root.toNat ≤ mem.size)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5508⟩
      ([mode, dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val,
        saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (liquidateTransition.body.drop 20) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (liquidateTransition.body.drop 20) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (liquidateTransition.body.drop 20)
        (.returned frame' evm' (some [.int seized.toNat, .int repaid.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized, repaid]) := by
  rcases midnightMemoryPaid_headroom rd hh.funding.accounting.paid hgas hh.covered with
    hoog | hroom
  · exact Or.inl hoog
  rcases liquidateEvent (R := saved :: R) (by simp only [List.length_cons]; omega)
      hf hpay hbad hd hi (by omega) hlo hsize hh.free hslot hseized hpaid hs hh.funding.budget rd with
    ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨hidx, _, mem1, aw1, k1, C1, ht, hsize1, hkeep, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert ht, hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ExecBlock.consStatic ht, hr⟩))
  · have hk (read : UInt256) (hb : read.toNat + 32 ≤ 832) :
        memLoad read mem1 = memLoad read mem := hkeep read (hb.trans hsize) (hb.trans hlo)
    have hh1 : TransferHeap mem1 aw1 root C1 :=
      ⟨hh.size.trans hsize1, hh.lower, (hk _ (by decide)).trans hh.free,
        (hk _ (by decide)).trans hh.zero, (hused.trans hsize1).trans hb1.funding.covered,
        hh.aligned, hb1.funding⟩
    rcases midnightLiquidateTransfers hstack hf hbad hpay hd hi hidx hlo (hsize.trans hsize1)
        ((hk _ (by decide)).trans hid) ((hk _ (by decide)).trans hz)
        ((hk _ (by decide)).trans hcallback) hcanon
        ((hk _ (by decide)).trans hseized) ((hk _ (by decide)).trans hpaid)
        hdl hdata hh1 hgas hfork hs rd1 with
      hoog | ⟨htail, hr⟩ | ⟨frame', evm', htail, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨ExecBlock.consNormal ht htail, hr⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', ExecBlock.consNormal ht htail, hr⟩))

end Benchmarks.Midnight

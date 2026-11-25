import Benchmarks.Midnight.LiquidateTransfer
import Benchmarks.Midnight.LiquidateAfterTransfer

variable {fork : Ethereum.Fork}

/-! Both liquidation transfers and the intervening optional callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateTransfers {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root id index seized repaid borrower mode dp dl badDebt saved : UInt256}
    {receiver callback payer : AccountAddress} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 26 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hbad : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hpay : frame.locals.get? "payer" = some (.address payer))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index) (hidx : index.toNat < m.collaterals.length)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨20488⟩
      ([⟨4⟩ + calldataWord I.calldata 4, calldataWord I.calldata 4 + ⟨100⟩,
        ⟨5734⟩, ⟨5750⟩, UInt256.ofNat receiver.val, ⟨5543⟩, ⟨5755⟩,
        dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 21) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (liquidateTransition.body.drop 21)
        (.returned frame' evm' (some [.int seized.toNat, .int repaid.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized, repaid]) := by
  rcases midnightLiquidateTransfer (R := saved :: R)
      (by simp only [List.length_cons]; omega) hf hd hi hidx hseized hh hgas hfork hs rd with
    hoog | ⟨ht, hr⟩ | ⟨evm1, σ1, out1, mem1, root1, aw1, k1, C1, ht, hs1, hp1, hlo1, hh1, rd1⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert ht, hr⟩)
  · have hkeep (read : UInt256) (hb : read.toNat + 32 ≤ 832) (hl : 96 ≤ read.toNat) :
        memLoad read mem1 = memLoad read mem := hp1.load read hl (hb.trans hlo) (hb.trans hsize)
    have hbad1 : (liquidateTransferFrame frame).locals.get? "badDebt" =
        some (.int badDebt.toNat) := by rw [liquidateTransferFrame_get _ _ (by decide), hbad]
    have hpay1 : (liquidateTransferFrame frame).locals.get? "payer" = some (.address payer) := by
      rw [liquidateTransferFrame_get _ _ (by decide), hpay]
    rcases midnightLiquidateAfterTransfer (R := R) hstack (liquidateTransferFrame_arguments hf)
        hbad1 hpay1 hd hi (hlo.trans hlo1) (hsize.trans hp1.size)
        ((hkeep _ (by decide) (by decide)).trans hid)
        ((hkeep _ (by decide) (by decide)).trans hz)
        ((hkeep _ (by decide) (by decide)).trans hcallback) hcanon
        ((hkeep _ (by decide) (by decide)).trans hseized)
        ((hkeep _ (by decide) (by decide)).trans hpaid)
        hdl hdata hh1 hgas hfork hs1 rd1 with
      hoog | ⟨htail, hr⟩ | ⟨frame', evm', htail, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨ExecBlock.consNormal ht htail, hr⟩)
    · exact Or.inr (Or.inr ⟨frame', evm', ExecBlock.consNormal ht htail, hr⟩)

end Benchmarks.Midnight

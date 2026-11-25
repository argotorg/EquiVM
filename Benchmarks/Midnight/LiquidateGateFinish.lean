import Benchmarks.Midnight.LiquidatorGateAligned
import Benchmarks.Midnight.LiquidateLoopFinish

variable {fork : Ethereum.Fork}

/-! The optional liquidator gate and all subsequent liquidation phases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateGateFinish {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw heap root id seized repaid borrower mode debtWord dp dl saved : UInt256}
    {receiver callback : AccountAddress} {m : MarketData} {σ : AccountMap} {k C credit : Nat}
    {R : List UInt256} (hstack : R.length + 33 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id (calldataWord I.calldata 36) seized repaid borrower mode
      receiver callback (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (halign : root.toNat % 32 = 0)
    (hcover : root.toNat ≤ 32 * aw.toNat)
    (hm : MarketStored mem ⟨832⟩ ⟨1088⟩ heap m) (hheap : heap.toNat ≤ root.toNat)
    (hz96 : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hdebt : healthPositionWord evm id borrower = debtWord)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hfund : MemoryFunding credit mem aw C)
    (hcredit : 4 * ((root.toNat + 20831) / 32) ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5275⟩
      ([UInt256.isZero repaid, UInt256.isZero (UInt256.isZero repaid), positionSlot id borrower,
        dp, dl, borrower, debtWord, UInt256.ofNat receiver.val, mode, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 8) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 8) .staticViolation ∧
      RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm' seized' repaid',
      ExecBlock fork config frame evm (liquidateTransition.body.drop 8)
        (.returned frame' evm' (some [.int seized'.toNat, .int repaid'.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized', repaid']) := by
  rcases midnightMemoryPaid_headroom rd hfund.accounting.paid hgas hcover with hoog | hroom
  · exact Or.inl hoog
  rcases midnightLiquidatorGateAligned (R := R) (by omega) (by omega) hlo hsize hfree hz
      hf.market hd hs hfund.budget rd with
    ⟨hx, hr⟩ | ⟨f1, evm1, σ1, mem1, out1, root1, aw1, k1, C1,
      hx1, hframe, hs1, hstorage, hp1, hlo1, hhi1, halign1, hfree1, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hx, hr⟩)
  · have hf1 : LiquidateSourceFrame f1 m id (calldataWord I.calldata 36) seized repaid borrower
        mode receiver callback (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)) := by
      rcases hframe with rfl | rfl
      · exact hf
      · exact hf.insert "allowed" _ (by decide)
    have hdebt1 : healthPositionWord evm1 id borrower = debtWord := by
      have he : healthPositionWord evm1 id borrower = healthPositionWord evm id borrower := by
        unfold healthPositionWord
        rw [hs1.env, hs.env]
        exact (accountStorageStateEq_storage_getD hstorage I.codeOwner _ ⟨0⟩).symm
      exact he.trans hdebt
    have hxentry := liquidateLoopSourceEntry (fork := fork) (evm := evm1) hcanon hf1.position
    rw [hdebt1] at hxentry
    have hz1 : memLoad (UInt256.ofNat 800) mem1 = ⟨0⟩ :=
      (hp1.load (UInt256.ofNat 800) (by decide) hlo hsize).trans hz
    obtain ⟨aw2, k2, C2, hb2, rd2⟩ := midnightLiquidateLoopEntry
      (R := [UInt256.ofNat receiver.val, mode, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hz1 hb1 rd1
    let mem2 := liquidateBitmapMemory mem1 (UInt256.shiftRight debtWord ⟨128⟩)
    have hp2 := hp1.liquidateClear (UInt256.shiftRight debtWord ⟨128⟩)
    have hk (read : UInt256) (hin : read.toNat + 32 ≤ 832) (hl : 96 ≤ read.toNat)
        (hdisj : read.toNat + 32 ≤ 704 ∨ 736 ≤ read.toNat) :
        memLoad read mem2 = memLoad read mem :=
      hp2.load read hl (hin.trans hlo) (hin.trans hsize) hdisj
    have hfree2 : memLoad (UInt256.ofNat 64) mem2 = root1 := by
      rw [liquidateBitmapMemory_preserved _ _ (by change 96 ≤ mem1.size; have := hp1.size; omega)
        (Or.inl (by decide)), hfree1]
    have hm2 : MarketStored mem2 ⟨832⟩ ⟨1088⟩ heap m :=
      (hm.preserve (hp1.mono hheap)).writeWord_below _ (by decide)
    have sourcePrefix {result : ExecResult}
        (ht : ExecBlock fork config (liquidateLoopInitialFrame f1 debtWord) evm1
          (liquidateTransition.body.drop 14) result) :
        ExecBlock fork config frame evm (liquidateTransition.body.drop 8) result :=
      .consNormal hx1 (execBlock_append_ok hxentry ht)
    rcases midnightLiquidateLoopFinish hstack (liquidateLoopInitialFrame_arguments hf1)
        (liquidateLoopInitialFrame_accumulators f1 debtWord) hd hcs hcr (by omega)
        (hlo.trans hlo1) (hsize.trans hp2.size) hfree2 (halign1.trans halign)
        (shiftRight128_lt _) (liquidateBitmapMemory_load _ _) hm2 (hheap.trans hlo1)
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hz96)
        ((hk _ (by decide) (by decide) (Or.inr (by decide))).trans hid)
        ((hk _ (by decide) (by decide) (Or.inr (by decide))).trans hz)
        ((hk _ (by decide) (by decide) (Or.inr (by decide))).trans hcallback) hcanon
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hseized)
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hpaid)
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hslot)
        hdebt1 hdl hdata hb2.funding (by omega) hgas hfork hs1 rd2 with
      hoog | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨frame', evm', seized', repaid', ht, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨sourcePrefix ht, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨sourcePrefix ht, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', seized', repaid', sourcePrefix ht, hr⟩))

end Benchmarks.Midnight

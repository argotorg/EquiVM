import Benchmarks.Midnight.LiquidatePostLoop

/-! Finish liquidation from the collateral loop with its retained memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateLoopFinish {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw heap root id seized repaid borrower mode debtWord bitmap maxDebt price badDebt dp dl saved : UInt256}
    {receiver callback : AccountAddress} {m : MarketData} {σ : AccountMap} {k C credit : Nat}
    {R : List UInt256} (hstack : R.length + 33 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id (calldataWord I.calldata 36) seized repaid borrower mode
      receiver callback (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (ha : LiquidateAccumulators frame bitmap maxDebt price (low128 debtWord) badDebt)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hroot : root.toNat + 20608 < 2^64) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (halign : root.toNat % 32 = 0)
    (hbits : bitmap.toNat < 2^128) (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
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
    (hcredit : 4 * ((root.toNat + 20799) / 32) ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka) (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5340⟩
      ([debtWord, UInt256.isZero (UInt256.isZero repaid), UInt256.isZero repaid, maxDebt, price,
        positionSlot id borrower, dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, mode,
        saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (liquidateTransition.body.drop 14) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (liquidateTransition.body.drop 14) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm' seized' repaid',
      ExecBlock config frame evm (liquidateTransition.body.drop 14)
        (.returned frame' evm' (some [.int seized'.toNat, .int repaid'.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized', repaid']) := by
  rcases midnightLiquidateLoop hstack hfork hcanon hd 128 evm frame mem rdata aw root
      bitmap maxDebt price badDebt σ k C (by decide) hbits (by omega) hlo hheap hsize
      hfree hbitmap hz hm hf ha hs hfund.budget rd with
    ⟨hx, hr⟩ | ⟨evm1, σ1, f1, mem1, out1, root1, max1, price1, bad1, aw1, k1, C1,
      hx1, hs1, hstorage, hf1, ha1, _, hfree1, _, hz1, hlo1, hhi1, halign1, hp1, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hx, hr⟩)
  · have hk (read : UInt256) (hin : read.toNat + 32 ≤ 832) (hl : 96 ≤ read.toNat)
        (hdisj : read.toNat + 32 ≤ 704 ∨ 736 ≤ read.toNat) :
        memLoad read mem1 = memLoad read mem :=
      hp1.load read hl (hin.trans hlo) (hin.trans hsize) hdisj
    have hdebt1 : healthPositionWord evm1 id borrower = debtWord := by
      have he : healthPositionWord evm1 id borrower = healthPositionWord evm id borrower := by
        unfold healthPositionWord
        rw [hs1.env, hs.env]
        exact (accountStorageStateEq_storage_getD hstorage I.codeOwner _ ⟨0⟩).symm
      exact he.trans hdebt
    have hc1 : transferHeapCredit (root1 + UInt256.ofNat 128) ≤ credit := by
      unfold transferHeapCredit
      rw [uadd_word_ofNat_toNat root1 128 (by change _ < 2^256; omega)]
      omega
    rcases midnightLiquidatePostLoop (by omega) hf1 ha1 hd rfl hcs hcr (by omega)
        (hlo.trans hlo1) (hsize.trans hp1.size) hfree1 (halign1.trans halign)
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hz96)
        ((hk _ (by decide) (by decide) (Or.inr (by decide))).trans hid) hz1
        ((hk _ (by decide) (by decide) (Or.inr (by decide))).trans hcallback) hcanon
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hseized)
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hpaid)
        ((hk _ (by decide) (by decide) (Or.inl (by decide))).trans hslot)
        hdebt1 hdl hdata hb1.funding hc1 hgas hfork hs1 rd1 with
      hoog | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨frame', evm', seized', repaid', ht, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨.consNormal hx1 ht, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨.consNormal hx1 ht, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', seized', repaid', .consNormal hx1 ht, hr⟩))

end Benchmarks.Midnight

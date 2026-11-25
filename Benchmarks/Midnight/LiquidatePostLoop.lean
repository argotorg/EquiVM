import Benchmarks.Midnight.LiquidatePostLoopGuard
import Benchmarks.Midnight.LiquidateBadDebt
import Benchmarks.Midnight.LiquidateSettlement

variable {fork : Ethereum.Fork}

/-! The post-loop eligibility, bad-debt update, amount calculation, and settlement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidatePostLoop {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root id index seized repaid borrower mode debtWord maxDebt price badDebt dp dl saved : UInt256}
    {receiver callback : AccountAddress} {m : MarketData} {σ : AccountMap} {k C credit : Nat}
    {R : List UInt256} (hstack : R.length + 26 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (ha : LiquidateAccumulators frame ⟨0⟩ maxDebt price (low128 debtWord) badDebt)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index)
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hroot : root.toNat + 128 < 2^64) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (halign : root.toNat % 32 = 0)
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
    (hcredit : transferHeapCredit (root + UInt256.ofNat 128) ≤ credit)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5358⟩
      ([debtWord, UInt256.isZero (UInt256.isZero repaid), UInt256.isZero repaid, maxDebt, price,
        positionSlot id borrower, dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, mode,
        saved] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 15) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 15) .staticViolation ∧
      RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm' seized' repaid',
      ExecBlock fork config frame evm (liquidateTransition.body.drop 15)
        (.returned frame' evm' (some [.int seized'.toNat, .int repaid'.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized', repaid']) := by
  rcases midnightLiquidatePostLoopGuard (R := saved :: R)
      (by simp only [List.length_cons]; omega) hcanon hd hroot (by omega) hfree hid hf ha hs
      hfund.budget rd (liquidateTransition.body.drop 17) with
    ⟨hx, hr⟩ | ⟨aw1, k1, C1, hx1, _, hp1, hfree1, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨hx, hr⟩)
  · let mem1 := dynamicLockMemory mem root id borrower
    have hk (read : UInt256) (hin : read.toNat + 32 ≤ 832) (hl : 96 ≤ read.toNat) :
        memLoad read mem1 = memLoad read mem := hp1.load read hl (hin.trans hlo) (hin.trans hsize)
    have hf1 := hf.insert "__c11" (lockValue evm liquidationLockBase id borrower) (by decide)
    have ha1 := ha.insert "__c11" (lockValue evm liquidationLockBase id borrower) (by decide)
    rcases midnightLiquidateBadDebt (R := R) hstack hf1 ha1 hcanon hdebt
        ((hk _ (by decide) (by decide)).trans hslot)
        ((hk _ (by decide) (by decide)).trans hz) hs hb1 rd1 with
      ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨f2, evm2, σ2, head, aw2, k2, C2, hs2, hx2, hf2, ha2, hb2, rd2⟩
    · exact Or.inr (Or.inl ⟨hx1.run (ExecBlock.consRevert hx), hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hx1.run (ExecBlock.consStatic hx), hr⟩))
    · have hnext : (root + UInt256.ofNat 128).toNat = root.toNat + 128 :=
        uadd_word_ofNat_toNat root 128 (by change _ < 2^256; omega)
      have hused : (root + UInt256.ofNat 128).toNat ≤ mem1.size := by
        dsimp only [mem1]
        rw [hnext, dynamicLockMemory, writeWord_sparse_size, dynamicLockHashMemory_size]
        omega
      have hh2 : TransferHeap mem1 aw2 (root + UInt256.ofNat 128) C2 :=
        ⟨(by have := hp1.size; omega), (by rw [hnext]; omega), hfree1,
          (hk _ (by decide) (by decide)).trans hz96, hused.trans hb2.funding.covered,
          (by rw [hnext]; omega), hb2.funding.weaken hcredit⟩
      rcases midnightLiquidateSettlement hstack hf2 ha2 hd hi hcs hcr (by rw [hnext]; omega)
          (hsize.trans hp1.size) hused ((hk _ (by decide) (by decide)).trans hid)
          ((hk _ (by decide) (by decide)).trans hz)
          ((hk _ (by decide) (by decide)).trans hcallback) hcanon
          ((hk _ (by decide) (by decide)).trans hseized)
          ((hk _ (by decide) (by decide)).trans hpaid)
          ((hk _ (by decide) (by decide)).trans hslot) hdl hdata hh2 hgas hfork hs2 rd2 with
        hoog | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨frame', evm', seized', repaid', ht, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨hx1.run (.consNormal hx2 ht), hr⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hx1.run (.consNormal hx2 ht), hr⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', seized', repaid',
          hx1.run (.consNormal hx2 ht), hr⟩))

end Benchmarks.Midnight

import Benchmarks.Midnight.LiquidateInputTrace
import Benchmarks.Midnight.LiquidateDebtTrace
import Benchmarks.Midnight.LiquidateGuardsSource
import Benchmarks.Midnight.LiquidateCoreMemory
import Benchmarks.Midnight.LiquidateGateFinish

/-! Liquidation after touchMarket: guards, collateral loop, and settlement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCore {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw heap root id seized repaid borrower mode dp dl saved : UInt256}
    {receiver callback : AccountAddress} {m : MarketData} {σ : AccountMap} {k C credit : Nat}
    {R : List UInt256} (hstack : R.length + 33 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id (calldataWord I.calldata 36) seized repaid borrower mode
      receiver callback (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size) (hspace : root.toNat ≤ mem.size + 31)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (halign : root.toNat % 32 = 0)
    (hm : MarketStored mem ⟨832⟩ ⟨1088⟩ heap m) (hheap : heap.toNat ≤ root.toNat)
    (hz96 : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hfund : MemoryFunding credit mem aw C)
    (hcredit : 4 * ((root.toNat + 20831) / 32) ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka) (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5161⟩
      ([id, dl, borrower, dp, UInt256.ofNat receiver.val, mode, saved] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (liquidateTransition.body.drop 6) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (liquidateTransition.body.drop 6) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm' seized' repaid',
      ExecBlock config frame evm (liquidateTransition.body.drop 6)
        (.returned frame' evm' (some [.int seized'.toNat, .int repaid'.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized', repaid']) := by
  rcases midnightLiquidateInputGuard (R := [UInt256.ofNat receiver.val, mode, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hsize hz hcanon hfund.budget rd with ⟨hbad, hr⟩ | ⟨hinput, aw1, k1, C1, hb1, rd1⟩
  · rw [hcs, hcr] at hbad
    exact Or.inr (Or.inl ⟨liquidateInputRevert hf.seized hf.repaid hbad, hr⟩)
  · rw [hcs, hcr] at hinput
    have hword : healthPositionWord evm id borrower =
        solcSlotWordAt (positionSlot id borrower + ⟨2⟩) σ I := hs.storageRead _
    rcases midnightLiquidateDebtGuard (R := [UInt256.ofNat receiver.val, mode, saved] ++ R)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hb1 rd1 with
      ⟨hzdebt, hr⟩ | ⟨hdebt, k2, C2, hb2, rd2⟩
    · exact Or.inr (Or.inl ⟨liquidateDebtRevert hf.seized hf.repaid hf.position hcanon hinput
        (by rw [hword]; exact hzdebt), hr⟩)
    · have hpositive : 0 < (low128 (healthPositionWord evm id borrower)).toNat := by
        rw [hword]
        by_contra hn
        exact hdebt (uint256_toNat_eq_zero (by omega))
      let mem1 := liquidatePositionMemory mem id borrower
      have hm1 := liquidatePositionMemory_market (id := id) (borrower := borrower) hm (by decide)
      have hsz1 : mem1.size = mem.size := liquidatePositionMemory_size id borrower hsize
      have hk (read : UInt256) (hin : read.toNat + 32 ≤ 832) (hl : 64 ≤ read.toNat)
          (hslot : read.toNat + 32 ≤ 672 ∨ 704 ≤ read.toNat)
          (hid : read.toNat + 32 ≤ 768 ∨ 800 ≤ read.toNat) :
          memLoad read mem1 = memLoad read mem :=
        liquidatePositionMemory_load id borrower read hsize hl (hin.trans hsize) hslot hid
      have hcover : root.toNat ≤ 32 * aw1.toNat := by
        have hc := hb2.funding.covered
        change mem1.size ≤ 32 * aw1.toNat at hc
        rw [hsz1] at hc
        omega
      rw [hcr] at rd2
      rcases midnightLiquidateGateFinish hstack hf hd hcs hcr hlo (by rw [hsz1]; exact hsize)
          ((hk _ (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hfree)
          halign hcover hm1 hheap
          ((hk _ (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hz96)
          (liquidatePositionMemory_id id borrower hsize)
          ((hk _ (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hz)
          ((hk _ (by decide) (by decide) (Or.inr (by decide)) (Or.inl (by decide))).trans hcallback)
          hcanon
          ((hk _ (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hseized)
          ((hk _ (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hpaid)
          (liquidatePositionMemory_slot id borrower hsize) hword hdl hdata hb2.funding hcredit
          hgas hfork hs rd2 with
        hoog | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨frame', evm', seized', repaid', ht, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨liquidateGuardsSource hf.seized hf.repaid hf.position hcanon hinput
          hpositive ht, hr⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨liquidateGuardsSource hf.seized hf.repaid hf.position hcanon
          hinput hpositive ht, hr⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', seized', repaid',
          liquidateGuardsSource hf.seized hf.repaid hf.position hcanon hinput hpositive ht, hr⟩))

end Benchmarks.Midnight

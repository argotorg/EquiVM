import Benchmarks.Midnight.RepayBalanceTrace
import Benchmarks.Midnight.RepayTail

/-! Repayment from the checked debt reduction to the final transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayCore {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root market arrayPtr limit id units user dp dl saved : UInt256}
    {callback : AccountAddress} {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : RepaySourceFrame frame m id user units callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hu : user.toNat < EVM.addressModulus) (hstack : R.length + 30 ≤ 1024)
    (hmem : 832 ≤ mem.size) (hm : MarketStored mem market arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hroot : root.toNat + 32 < 2^64)
    (hlower : 832 ≤ root.toNat) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hdl : dl.toNat < 2^64) (hd : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hb : TransferBudget (root + UInt256.ofNat 32) credit mem aw C)
    (hcredit : 4 * (((root + UInt256.ofNat 32).toNat + safeTransferCallAllocation true + 31) / 32)
      ≤ credit + 999921) (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨9861⟩
      ([id, dp, dl, user, UInt256.ofNat callback.val, units, market, saved] ++ R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (repayTransition.body.drop 5) .reverted) ∨
    (RDstatic midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (repayTransition.body.drop 5) .staticViolation) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (repayTransition.body.drop 5) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  rcases midnightRepayBalances (R := saved :: R) hs.env hf hu
      (by simp only [List.length_cons]; omega) hmem hzero800 hb rd with
    ⟨hr, ht⟩ | ⟨hr, ht⟩ | ⟨hperm, hsafe, aw1, k1, C1, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨hr, ht⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, ht⟩))
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightRepayWriteWithdrawable
      (by change R.length + 3 + 12 ≤ 1024; omega) hperm rd1
    let evm2 := repayBalanceState evm id user units
    let frame1 := repayBalanceFrame frame units
    let frame2 := repayPayerFrame frame1 I callback
    let mem1 := repayBalanceMemory mem id user
    have henv2 : evm2.executionEnv = I := (repayBalanceState_env ..).trans hs.env
    have hs2 : SourceState s0 I evm2.accountMap evm2 := by
      refine ⟨?_, henv2, rfl⟩
      simpa only [evm2, repayBalanceState, repayDebtState, marketBalanceStore,
        show ¬ (1 : Fin 3).val = 2 from by decide, if_false,
        storeLow128, storageStore_σ₀] using hs.world
    have hstore : storeLow128Accounts (repayDebtState evm id user units).accountMap I
        (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
        (marketBalanceWord (repayDebtState evm id user units) id 1 + units) = evm2.accountMap := by
      change _ = (storeLow128 (repayDebtState evm id user units)
        (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
        (marketBalanceWord (repayDebtState evm id user units) id 1 + units)).accountMap
      rw [storeLow128_accounts, repayDebtState_env, hs.env]
    rw [hstore] at rd2
    have hf1 : RepaySourceFrame frame1 m id user units callback
        (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)) :=
      (hf.insert "__c1" (.int units.toNat) (by decide)).insert "__c2" (.int units.toNat) (by decide)
    have hf2 := repayPayerFrame_spec hf1 I
    have hpayer : frame2.locals.get? "payer" = some (.address (repayPayer I callback)) := by
      simp [frame2, repayPayerFrame]
    have hp1 : MemoryPrefix mem mem1 root.toNat :=
      (positionReadMemory_prefix mem id user root.toNat).trans (twoWordHashMem_prefix ..)
    have hm1 := hm.preserve (hp1.mono hlimit)
    have hmem1 : 832 ≤ mem1.size := hmem.trans hp1.size
    have hfree1 : memLoad (UInt256.ofNat 64) mem1 = root := by
      dsimp only [mem1, repayBalanceMemory]
      rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
          (by rw [positionReadMemory_size _ _ _ (by omega)]; change 96 ≤ mem.size; omega),
        positionReadMemory,
        memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
          (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; change 96 ≤ mem.size; omega),
        memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
          (by change 96 ≤ mem.size; omega), hfree]
    have hz1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ := by
      rw [hp1.load (UInt256.ofNat 96) (by decide) (by change 128 ≤ root.toNat; omega)
        (by change 128 ≤ mem.size; omega), hzero]
    have hz8001 : memLoad (UInt256.ofNat 800) mem1 = ⟨0⟩ := by
      rw [hp1.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
    have sourcePrefix {result : ExecResult}
        (ht : ExecBlock config frame2 evm2 (repayTransition.body.drop 10) result) :
        ExecBlock config frame evm (repayTransition.body.drop 5) result := by
      apply repayBalancesSource hf hu hsafe (by rw [hs.env]; exact hperm)
      apply repayPayerSource hf1
      change ExecBlock config (repayPayerFrame frame1 evm2.executionEnv callback) evm2 _ _
      rw [henv2]
      exact ht
    rcases midnightRepayTail hs2 hf2 hpayer hperm hstack hmem1 hm1 hlimit hroot hlower
        hfree1 hz1 hz8001 hu hdl hd (hb1.mono hc2) hcredit hgas hfork rd2 with
      hoog | ⟨hr, ht⟩ | ⟨frame', evm', ht, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, sourcePrefix ht⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', sourcePrefix ht, hr⟩))

end Benchmarks.Midnight

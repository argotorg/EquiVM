import Benchmarks.Midnight.WithdrawUnitsUpdateEntry
import Benchmarks.Midnight.WithdrawUnitsUpdateSource
import Benchmarks.Midnight.WithdrawUnitsAfterUpdate
import Benchmarks.Midnight.PositionUpdateInternalBudget

/-! Unit withdrawal from the market touch through the internal update and final transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawUnitsCore {I : ExecutionEnv} {g : UInt256} {s0 evm origin : State}
    {m : MarketData} {mem rdata : ByteArray}
    {aw market array heap root user units saved : UInt256}
    {receiver : AccountAddress} {gasCredit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hcanon : user.toNat < EVM.addressModulus) (hstack : R.length + 40 ≤ 1024)
    (hmem : 832 ≤ mem.size) (hm : MarketStored mem market array heap m)
    (hroot : root.toNat < 2^64) (hlower : 832 ≤ root.toNat) (hheap : heap.toNat ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root gasCredit mem aw C)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation false + 31) / 32) ≤
      gasCredit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3881⟩
      ([m.id, user, user, market, UInt256.ofNat 64, solcAddrMask,
        UInt256.ofNat receiver.val, units, UInt256.ofNat 3723, saved] ++ R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
        (withdrawTransition.body.drop 5) .reverted) ∨
    (RDstatic midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
        (withdrawTransition.body.drop 5) .staticViolation) ∨
    ∃ frame' evm',
      ExecBlock config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
        (withdrawTransition.body.drop 5) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  simp only [List.cons_append, List.nil_append] at rd
  obtain ⟨aw1, k1, C1, hb1, rd1⟩ := midnightWithdrawUnitsUpdateEntry
    (by simp only [List.length_cons]; omega) hmem hzero800 hb rd
  let mem1 := twoWordHashMem m.id (⟨1⟩ : UInt256) mem
  have hp1 : MemoryPrefix mem mem1 root.toNat := twoWordHashMem_prefix ..
  have hm1 := hm.preserve (hp1.mono hheap)
  have hmem1 : 832 ≤ mem1.size := hmem.trans hp1.size
  have hfree1 : memLoad (UInt256.ofNat 64) mem1 = root := by
    dsimp only [mem1]
    rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
      (by change 96 ≤ mem.size; omega), hfree]
  have hmarket : (market + UInt256.ofNat 128).toNat = market.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by
      have := hm.array
      have := hm.extent
      have := hm.bound
      change _ < 2^256
      omega)
  have hmaturity : memLoad (market + UInt256.ofNat 128) mem1 = m.maturity :=
    hm1.words.load_word ⟨4, by simp [MarketData.words]⟩ (by simpa using hmarket)
  have hmatureLo : 64 ≤ (market + UInt256.ofNat 128).toNat := by
    rw [hmarket]
    omega
  have hmatureHi : (market + UInt256.ofNat 128).toNat + 32 ≤ mem1.size := by
    rw [hmarket]
    have hwords := hm1.words.size
    change market.toNat + 32 * 8 ≤ mem1.size at hwords
    omega
  rcases midnightPositionUpdateInternal_budget (evm := evm) (s0 := s0)
      (g := Sat256.ofUInt256 g) (m := m) (id := m.id)
      (imms := ∅) (ret := UInt256.ofNat 3909)
      (R := [m.id, user, solcMappingSlot ⟨1⟩ m.id, market, UInt256.ofNat 64, solcAddrMask,
        UInt256.ofNat receiver.val, units, UInt256.ofNat 3723, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hcanon
      hmatureLo hmatureHi
      hmaturity (by omega) hroot hfree1 (by jump_dest) hb1
      (by simpa only [hs.env] using rd1) with
    ⟨hr, ht⟩ | ⟨hr, ht⟩ | ⟨hperm, hc, hp, hf, ht, aw2, k2, C2, hb2, rd2⟩
  · exact Or.inr (Or.inl ⟨hr, withdrawUnitsUpdateReverts ht⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, withdrawUnitsUpdateStatic ht⟩))
  · let evm2 := positionUpdateFinalState evm m m.id user
    let mem2 := positionUpdateLogMemory mem1 root evm m m.id user
    have hp2 := hp1.trans (positionUpdateLogMemory_prefix mem1 root evm m m.id user)
    have hm2 := hm.preserve (hp2.mono hheap)
    have hs2 : SourceState s0 I evm2.accountMap evm2 := by
      refine ⟨?_, (positionUpdateFinalState_env ..).trans hs.env, rfl⟩
      simpa only [evm2, positionUpdateFinalState, positionUpdateFeeState,
        positionUpdatedBalances, positionUpdateState, storeLow128, storeHigh128,
        storageStore_σ₀] using hs.world
    have hfree2 : memLoad (UInt256.ofNat 64) mem2 = root :=
      positionUpdateLogMemory_free mem1 root evm m m.id user (by omega) (by omega) hfree1
    have hz2 : memLoad (UInt256.ofNat 96) mem2 = ⟨0⟩ := by
      rw [hp2.load (UInt256.ofNat 96) (by decide)
        (by change 128 ≤ root.toNat; omega) (by change 128 ≤ mem.size; omega), hzero]
    have hz8002 : memLoad (UInt256.ofNat 800) mem2 = ⟨0⟩ := by
      rw [hp2.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
    have sourcePrefix {result : ExecResult}
        (hbody : ExecBlock config
          (withdrawUnitsReadyFrame origin m user units receiver
            (positionNewCredit evm m m.id user) (positionNewPending evm m m.id user)
            (positionViewFee evm m m.id user)) evm2 (withdrawTransition.body.drop 9) result) :
        ExecBlock config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
          (withdrawTransition.body.drop 5) result := withdrawUnitsUpdateReturns ht hbody
    rcases withdrawUnitsAfterUpdate (R := R) (saved := saved) hs2
        (withdrawUnitsReady_get ..) hcanon
        (by rw [← hs.env]; exact hperm) (by omega) (hmem.trans hp2.size) hm2
        hroot hlower hheap hfree2 hz2 hz8002 (by apply wordLocal_get)
        hb2 hcredit hgas hfork (by simpa only [hs.env] using rd2) with
      hoog | ⟨hr, hbody⟩ | ⟨frame', evm', hbody, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, sourcePrefix hbody⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', sourcePrefix hbody, hr⟩))

end Benchmarks.Midnight

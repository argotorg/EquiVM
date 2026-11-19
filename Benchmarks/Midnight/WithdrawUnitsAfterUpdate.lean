import Benchmarks.Midnight.WithdrawUnitsPendingPhase
import Benchmarks.Midnight.WithdrawUnitsBalanceTrace
import Benchmarks.Midnight.WithdrawUnitsFinalWrite
import Benchmarks.Midnight.WithdrawUnitsTransfer
import Benchmarks.Midnight.AddressDecode

/-! Withdrawal after updating the position, through balance writes and the final transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawUnitsAfterUpdate {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market array heap root fee pending credit id user units saved : UInt256}
    {receiver : AccountAddress} {gasCredit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 34 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hm : MarketStored mem market array heap m)
    (hroot : root.toNat < 2^64) (hlower : 832 ≤ root.toNat) (hheap : heap.toNat ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hz : frame.locals.get? "pendingFeeDecrease" = some (.int 0))
    (hb : TransferBudget root gasCredit mem aw C)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation false + 31) / 32) ≤
      gasCredit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3909⟩
      ([fee, pending, credit, id, user, solcMappingSlot ⟨1⟩ id, market, UInt256.ofNat 64,
        solcAddrMask, UInt256.ofNat receiver.val, units, UInt256.ofNat 3723, saved] ++ R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (withdrawTransition.body.drop 9) .reverted) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (withdrawTransition.body.drop 9) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  rcases midnightWithdrawUnitsPending hs hf hcanon hperm (by omega) hmem hzero800 hz hb rd with
    ⟨hr, ht⟩ | ⟨frame1, evm1, decrease, aw1, k1, C1, hs1, hf1, hd128, hd, hif, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨hr, ht⟩)
  · let mem1 := positionReadMemory mem id user
    have hp1 : MemoryPrefix mem mem1 root.toNat := positionReadMemory_prefix ..
    have hm1 := hm.preserve (hp1.mono hheap)
    have hmem1 : 832 ≤ mem1.size := hmem.trans hp1.size
    have hfree1 : memLoad (UInt256.ofNat 64) mem1 = root := by
      dsimp only [mem1]
      rw [positionReadMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
          (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; change 96 ≤ mem.size; omega),
        memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
          (by change 96 ≤ mem.size; omega), hfree]
    have hz1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ := by
      rw [hp1.load (UInt256.ofNat 96) (by decide)
        (by change 128 ≤ root.toNat; omega) (by change 128 ≤ mem.size; omega), hzero]
    have hz800 : memLoad (UInt256.ofNat 800) mem1 = ⟨0⟩ := by
      rw [hp1.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
    simp only [List.cons_append, List.nil_append] at rd1
    rcases midnightWithdrawUnitsBalances hs1.env hf1 hcanon hperm
        (by simp only [List.length_cons]; omega) hb1 rd1 with
      ⟨hr, ht⟩ | ⟨hsafe, k2, C2, hb2, rd2⟩
    · exact Or.inr (Or.inl ⟨hr, ExecBlock.consNormal hif ht⟩)
    · obtain ⟨aw3, k3, C3, hb3, rd3⟩ := midnightWithdrawUnitsFinalWrite hs1.env
        (by simp only [List.length_cons]; omega) hperm hroot hfree1 hd128 hb2 rd2
      let mem3 := withdrawUnitsLogMemory mem1 root I units decrease
      have hp3 : MemoryPrefix mem1 mem3 root.toNat := memoryPrefix_writeWordArray _ _ _ _ le_rfl
      have hm3 := hm1.preserve (hp3.mono hheap)
      have hmem3 : 832 ≤ mem3.size := hmem1.trans hp3.size
      have hloan : memLoad (market + UInt256.ofNat 64) mem3 = UInt256.ofNat m.loanToken.val :=
        hm3.words.load_word ⟨2, by simp [MarketData.words]⟩ (by
          change (market + UInt256.ofNat 64).toNat = market.toNat + 64
          exact uadd_word_ofNat_toNat _ _ (by
            have := hm.array
            have := hm.extent
            have := hm.bound
            change _ < 2^256
            omega))
      have hclean : UInt256.land (UInt256.ofNat m.loanToken.val) solcAddrMask =
          UInt256.ofNat m.loanToken.val := addressWord_val_clean m.loanToken
      change RD _ _ _ _ _
        ([UInt256.land (memLoad (market + UInt256.ofNat 64) mem3) solcAddrMask,
          UInt256.ofNat receiver.val, units, UInt256.ofNat 3723, saved] ++ R)
        mem3 _ _ _ _ _ at rd3
      rw [hloan, hclean] at rd3
      have hfree3 : memLoad (UInt256.ofNat 64) mem3 = root := by
        dsimp only [mem3, withdrawUnitsLogMemory]
        rw [memLoad_writeWordArray_preserved _ _ _ _ (by change 96 ≤ mem1.size; omega)
          (Or.inl (by change 96 ≤ root.toNat; omega)), hfree1]
      have hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩ := by
        rw [hp3.load (UInt256.ofNat 96) (by decide)
          (by change 128 ≤ root.toNat; omega) (by change 128 ≤ mem1.size; omega), hz1]
      have hz3800 : memLoad (UInt256.ofNat 800) mem3 = ⟨0⟩ := by
        rw [hp3.load (UInt256.ofNat 800) (by decide) hlower hmem1, hz800]
      have hused : root.toNat ≤ mem3.size := by
        dsimp only [mem3, withdrawUnitsLogMemory]
        rw [writeWordArray_size_nonempty _ _ _ (by simp)]
        simp only [List.length_cons, List.length_nil] at ⊢
        omega
      let evm3 := withdrawUnitsFinalState evm1 id user units
      let frame3 := withdrawUnitsFinalFrame frame1 units
      have hs3 : SourceState s0 I evm3.accountMap evm3 := by
        refine ⟨?_, (withdrawUnitsFinalState_env ..).trans hs1.env, rfl⟩
        simpa only [evm3, withdrawUnitsFinalState, withdrawUnitsWithdrawableState,
          withdrawUnitsCreditState, storeLow128, storageStore_σ₀] using hs1.world
      have hf3 : WithdrawUnitsSourceFrame frame3 m id user units receiver :=
        ((hf1.insert "__c4" (.int units.toNat) (by decide)).insert "__c5"
          (.int units.toNat) (by decide)).insert "__c6" (.int units.toNat) (by decide)
      have hd3 : frame3.locals.get? "pendingFeeDecrease" = some (.int decrease.toNat) := by
        dsimp only [frame3, withdrawUnitsFinalFrame, withdrawUnitsWithdrawableFrame,
          withdrawUnitsCreditFrame]
        rw [wordLocal_get_ne _ _ _ _ (by decide), wordLocal_get_ne _ _ _ _ (by decide),
          wordLocal_get_ne _ _ _ _ (by decide), hd]
      have sourcePrefix {result : ExecResult}
          (ht : ExecBlock config frame3 evm3 (withdrawTransition.body.drop 16) result) :
          ExecBlock config frame evm (withdrawTransition.body.drop 9) result :=
        ExecBlock.consNormal hif (withdrawUnitsBalancesSource hf1 hcanon hsafe
          (by rw [hs1.env]; exact hperm) ht)
      simp only [List.cons_append, List.nil_append] at rd3
      rcases withdrawUnitsTransfer hs3 hf3 hd3 hperm
          (by simp only [List.length_cons]; omega) hmem3 hroot hlower hfree3 hz3 hz3800
          hb3 hused hcredit hgas hfork rd3 with hoog | ⟨hr, ht⟩ | ⟨frame', evm', ht, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨hr, sourcePrefix ht⟩)
      · exact Or.inr (Or.inr ⟨frame', evm', sourcePrefix ht, hr⟩)

end Benchmarks.Midnight

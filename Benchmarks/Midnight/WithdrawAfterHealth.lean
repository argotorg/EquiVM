import Benchmarks.Midnight.HealthInternalBudget
import Benchmarks.Midnight.WithdrawHealthSource
import Benchmarks.Midnight.WithdrawCollateralTransfer

/-! Withdrawal from the internal health call through the final token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawAfterHealth {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market array heap root budgetRoot index id user assets : UInt256}
    {token receiver : AccountAddress} {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hcanon : user.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 30 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hroot : root.toNat + 4096 < 2^64) (hlower : 832 ≤ root.toNat)
    (hheap : heap.toNat ≤ root.toNat)
    (halign : root.toNat % 32 = 0 ∨ budgetRoot.toNat + 160 ≤ 2^62)
    (hbound : root.toNat + 4096 ≤ budgetRoot.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hm : MarketStored mem market array heap m)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (hcredit : 4 * ((budgetRoot.toNat + safeTransferCallAllocation false + 31) / 32) ≤
      credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨19775⟩
      ([market, id, user, UInt256.ofNat 4643, user, UInt256.ofNat token.val,
        UInt256.ofNat receiver.val, assets, id] ++ R) mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 11) .reverted) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 11) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  simp only [List.cons_append, List.nil_append] at rd
  rcases midnightHealthInternal_budget frame.immutables
      (by simp only [List.length_cons]; omega) hfork hcanon hroot hheap hfree hm hs
      (by jump_dest) hb rd with
    ⟨hbody, hr⟩ | ⟨evm1, σ1, frame1, mem1, out1, root1, aw1, k1, C1, value,
      hbody, hs1, hm1, hfree1, hheap1, hroot1, hlo1, hhi1, hmod1, hp1, hb1, rd1⟩
  · exact Or.inr (Or.inl ⟨hr, withdrawHealthRevert hf hbody⟩)
  · have hcall := withdrawHealthReturn hf hbody
    cases value with
    | false =>
      have rd2 := midnightBlocks.midnight_block_4643_taken
        (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_4721
        (by simp only [midnightBlocks.midnight_block_4643_taken_stack, List.length_cons]; omega) rd2
      exact Or.inr (Or.inl ⟨hr, ExecBlock.consNormal hcall
        (ExecBlock.consRevert (ExecStmt.requireFalse (withdrawHealthGuard false)))⟩)
    | true =>
      have rd2 := midnightBlocks.midnight_block_4643_fallthrough
        (by simp only [List.length_cons]; omega) (by decide) rd1
      have hb2 := transferBudgetAt (root := root1) (credit := credit) rd2 (by
        rcases hb1 with hsmall | ⟨_, hfund⟩
        · exact Or.inl (by omega)
        · rcases halign with ha | hsmall
          · exact Or.inr ⟨hmod1.trans ha, hfund.mono (by omega)⟩
          · exact Or.inl (by omega))
      have hz1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ := by
        rw [hp1.load (UInt256.ofNat 96) (by decide)
          (by change 128 ≤ root.toNat; omega) (by change 128 ≤ mem.size; omega), hzero]
      have hz800 : memLoad (UInt256.ofNat 800) mem1 = ⟨0⟩ := by
        rw [hp1.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
      have hc1 : 4 * ((root1.toNat + safeTransferCallAllocation false + 31) / 32) ≤
          credit + 999921 := by omega
      have sourcePrefix {result : ExecResult}
          (ht : ExecBlock config (withdrawHealthFrame frame true) evm1
            (withdrawCollateralTransition.body.drop 13) result) :
          ExecBlock config frame evm (withdrawCollateralTransition.body.drop 11) result :=
        ExecBlock.consNormal hcall (ExecBlock.consNormal
          (ExecStmt.requireTrue (withdrawHealthGuard true)) ht)
      rw [hs1.accounts] at rd2
      rcases withdrawCollateralTransfer ⟨hs1.world, hs1.env, rfl⟩ (hf.healthFrame true)
          hperm (by omega) (hmem.trans hp1.size)
          hroot1 (by omega) hfree1 hz1 hz800 hb2 hc1 hgas hfork rd2 with
        hoog | ⟨hr, ht⟩ | ⟨frame', evm', ht, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨hr, sourcePrefix ht⟩)
      · exact Or.inr (Or.inr ⟨frame', evm', sourcePrefix ht, hr⟩)

end Benchmarks.Midnight

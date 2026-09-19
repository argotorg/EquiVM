import Solm.Benchmarks.Auction.PaymentSource
import Solm.Benchmarks.Auction.PaymentFallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- Full refinement of `_safeTransferETHWithFallback`, from its entry at 3337 to the caller's
return destination. The cursor result records allocations without assuming dense memory. -/
theorem paymentRoutine {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨3337⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 140 ≤ 2 ^ 200)
    (hv : PaymentValues locals recipient amount ptr)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 24 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
        safeTransferETHWithFallback.body
        (.returned { contract := auctionContract, locals := locals' } evm'
          (some [.int (Int.ofNat ptr'.toNat)])) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C' ∧
      MemoryCursor mem' aw' ptr' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 140 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
      safeTransferETHWithFallback.body .reverted ∧ RDrev auctionBytecode g s0) := by
  have rd4768 := evm_run h with [jumpdest, push2 ⟨3347⟩, dup3, dup3, push2 ⟨4768⟩,
    jump (by jump_dest)]
  have hbraw : ptr.toNat + 2 ^ 139 ≤ 2 ^ 200 := by omega
  obtain ⟨evm1, cA1, σ1, z1, out1, _, _, hc1, hs1, rd3347, hm1, hpre1, ho1, hlo1, hhi1⟩ :=
    rawEthRoutine rd4768 hs hperm hm hbraw (by jump_dest) (by evm_ov)
  obtain ⟨locals1, hraw, hv1, hz1⟩ := rawEthSource hv hbraw ho1 hc1
  have hg1 := rawEthWords_mono hm hbraw ho1
  cases z1 with
  | true =>
    have rdret := evm_run rd3347 with [jumpdest, push2 ⟨3570⟩,
      jumpiT (by decide) (by jump_dest), jumpdest, pop, pop, jump hret]
    exact Or.inl ⟨evm1, cA1, σ1, locals1, _, _, _, out1, _, _,
      paymentSourceRawSuccess hraw hv1 hz1, hs1, rdret, hm1.cursor, hpre1, hlo1,
      by omega, hg1⟩
  | false =>
    have rd3352 := evm_run rd3347 with [jumpdest, push2 ⟨3570⟩, jumpiNT (by decide)]
    have hb1 : (rawEthPtr ptr out1).toNat + 2 ^ 139 ≤ 2 ^ 200 := by omega
    rcases paymentFallbackRoutine rd3352 hs1 hperm hm1 hb1 hv1 hret (by omega) with
      ⟨evm2, cA2, σ2, locals2, mem2, aw2, ptr2, out2, _, _, hfb, hv2, hs2, rdret,
        hm2, hpre2, hlo2, hhi2, hg2⟩ | ⟨hbad, hrev⟩
    · exact Or.inl ⟨evm2, cA2, σ2, locals2, mem2, aw2, ptr2, out2, _, _,
        paymentSourceFallbackSuccess hraw hz1 hfb hv2, hs2, rdret, hm2,
        hpre1.trans (hpre2.mono hlo1), by omega, by omega, le_trans hg1 hg2⟩
    · exact Or.inr ⟨paymentSourceFallbackFailure hraw hz1 hbad, hrev⟩

end Auction

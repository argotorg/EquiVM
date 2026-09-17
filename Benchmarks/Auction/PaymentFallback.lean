import Benchmarks.Auction.TransferSource
import Benchmarks.Auction.TransferRoutine
import Benchmarks.Auction.CallGrowth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- The fallback starts only after the raw ETH send has failed. Each source call uses the state
returned by the matching EVM call, so a callback can change the WETH storage slot. -/
theorem paymentFallbackRoutine {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨3352⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 139 ≤ 2 ^ 200)
    (hv : PaymentValues locals recipient amount ptr)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        paymentFallbackStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      PaymentValues locals' recipient amount ptr' ∧ SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C' ∧
      MemoryCursor mem' aw' ptr' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 139 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentFallbackStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  have hb32 : ptr.toNat + 32 ≤ 2 ^ 200 := by omega
  by_cases hcode : extCodeSizeWord σ (wethWord σ I) = ⟨0⟩
  · exact Or.inr ⟨depositSourceNoCode hs hv hcode, depositNoCode h hm hb32 hcode hov⟩
  · obtain ⟨evm1, cA1, σ1, z1, out1, _, _, hc1, hs1, rd3432, ho1⟩ :=
      depositCall h hs hperm hm hb32 hcode hov
    cases z1 with
    | false =>
      exact Or.inr ⟨depositSourceFailure hs hv hcode hc1, depositAfterFailure rd3432 (by omega)⟩
    | true =>
      obtain ⟨_, _, rd3449⟩ := depositAfterSuccess rd3432 (by omega)
      have hm1 := depositCall_heap hm hb32
      have hdep := depositSourceSuccess hs hv hcode hc1
      have hv1 := hv.insertOther (collapseReturns []) (name := "_dep")
        (by decide) (by decide) (by decide) (by decide)
      obtain ⟨evm2, cA2, σ2, z2, out2, hc2, hs2, ho2, ht⟩ :=
        transferRoutine rd3449 hs1 hperm hm1 hb hret hov
      have hbound : ptr.toNat + out2.size + 31 ≤ 2 ^ 200 := by omega
      have ho255 : out2.size < 2 ^ 255 := by omega
      rcases ht with ⟨rfl, hvalid, ⟨_, _, rdret⟩, hm2, hprefix, hlo, hhi⟩ | ⟨hbad, hr⟩
      · obtain ⟨locals2, hsrc2, hv2⟩ := transferSourceSuccess hs1 hv1 hc2 hbound ho255 hvalid
        exact Or.inl ⟨evm2, cA2, σ2, locals2, _, _, _, out2, _, _,
          execBlock_append hdep hsrc2, hv2, hs2, rdret, hm2,
          (selectorMem_prefix hm depositWord).trans hprefix, hlo, hhi,
          le_trans (depositCallWords_mono hm.active hb32)
            (transferFinalWords_mono hm1 (by omega))⟩
      · exact Or.inr ⟨execBlock_append hdep
          (transferSourceFailure hs1 hv1 hc2 hbound ho255 hbad), hr⟩

end Auction

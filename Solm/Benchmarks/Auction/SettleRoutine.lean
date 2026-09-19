import Solm.Benchmarks.Auction.SettleChecks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- Full refinement of `_settleAuction`: snapshot, guards, storage flag, noun call, payment,
event, and internal return. Calls retain their actual success/failure outcomes. -/
theorem settleRoutine {I g s0 ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨4086⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 142 ≤ 2 ^ 200)
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (ha : locals.get? "auction" = none) (hn : locals.get? "nouns" = none)
    (ho : locals.get? "_owner" = none)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
        settleAuctionFn.body
        (.returned { contract := auctionContract, locals := locals' } evm'
          (some [.int (Int.ofNat ptr'.toNat)])) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C' ∧
      HeapMemory mem' aw' ptr' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 141 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
      settleAuctionFn.body .reverted ∧ RDrev auctionBytecode g s0) := by
  have hb192 : ptr.toNat + 192 ≤ 2 ^ 200 := by omega
  obtain ⟨_, _, rd4162⟩ := settleSnapshotPrefix h hm hb192 (by omega)
  have hptr : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
    addWord_toNat ptr ⟨192⟩ (by change ptr.toNat + 192 < 2 ^ 256; omega)
  obtain ⟨locals1, hsrc1, hv1⟩ := settleSnapshotSource hp ha hn ho
    (by change ptr.toNat + 192 < 2 ^ 256; omega)
  rw [snapshotSourceState hs] at hv1
  have hm1 := (snapshotOf σ I).mem_heap hm hb192
  have hsm1 := snapshotMemory_made (snapshotOf σ I) hm hb192
  rcases settleChecks rd4162 hs hperm hm1 (by omega) hsm1 (by omega) hv1 hret hov with
    ⟨evm', cA', σ', locals', mem', aw', ptr', out, _, _, hsrc2, hs', hr, hm', hpre,
      hlo, hhi, hg⟩ | ⟨hbad, hr⟩
  · have h160 : (ptr + ⟨160⟩).toNat = ptr.toNat + 160 :=
      addWord_toNat ptr ⟨160⟩ (by change ptr.toNat + 160 < 2 ^ 256; omega)
    have hg1 : aw.toNat ≤ (snapshotWords aw ptr).toNat :=
      expandedWords_mono hm.active (by change _ + 32 ≤ _; omega)
    refine Or.inl ⟨evm', cA', σ', locals', mem', aw', ptr', out, _, _, ?_, hs', hr,
      hm', ((snapshotOf σ I).mem_prefix mem ptr).trans (hpre.mono (by omega)),
      by omega, by omega, le_trans hg1 hg⟩
    apply ExecFuncBody.execBlockRet
    rw [settleBody_eq, List.append_assoc]
    exact execBlock_append hsrc1 hsrc2
  · refine Or.inr ⟨?_, hr⟩
    apply ExecFuncBody.execBlockRevert
    rw [settleBody_eq, List.append_assoc]
    exact execBlock_append hsrc1 hbad

end Auction

import Solm.Benchmarks.Auction.SettleEvent

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def settleAfterStmts : List Stmt :=
  [.assign .storage (aField "settled") (.boolLit true), settleNounStmt,
    settlePaymentStmt, .return [.var "_freePtr"]]

theorem settleBody_eq : settleAuctionFn.body =
    settleSnapshotStmts ++ settleGuardStmts ++ settleAfterStmts := rfl

theorem settleAfter {I g s0 s snap ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨4397⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 141 ≤ 2 ^ 200)
    (hsm : SnapshotMemory s mem aw snap) (hsep : snap.toNat + 192 ≤ ptr.toNat)
    (hv : SettleValues locals s ptr)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        settleAfterStmts
        (.returned { contract := auctionContract, locals := locals' } evm'
          (some [.int (Int.ofNat ptr'.toNat)])) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C' ∧
      HeapMemory mem' aw' ptr' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 140 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      settleAfterStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  obtain ⟨_, _, rd4434⟩ := settleStorePrefix h hsm hperm (by omega)
  have hstore := settleStoreSource (evm := evm) hv.auction
  rcases settleNounRoutine rd4434 hs.settled hperm hm (by omega) hsm hsep hv (by omega) with
    ⟨evm1, cA1, σ1, locals1, mem1, aw1, out1, _, _, hsrc1, hv1, hs1, rd4647, hm1,
      hsm1, hp1, hg1⟩ | ⟨hbad, hr⟩
  · rcases settlePaymentRoutine rd4647 hs1 hperm hm1 (by omega) hsm1 hsep hv1 hov with
      ⟨evm2, cA2, σ2, locals2, mem2, aw2, ptr2, out2, _, _, hsrc2, hv2, hs2, rd4688,
        hm2, hsm2, hp2, hlo2, hhi2, hg2⟩ | ⟨hbad, hr⟩
    · have hb2 : ptr2.toNat + 64 ≤ 2 ^ 200 := by omega
      obtain ⟨_, _, rdret⟩ := settleEvent rd4688 hm2 hb2 hsm2 hperm hret (by omega)
      refine Or.inl ⟨evm2, cA2, σ2, locals2, _, _, ptr2, out2, _, _, ?_, hs2, rdret,
        settleEventHeap hm2 hb2,
        hp1.trans (hp2.trans ((settleEventPrefix mem2 ptr2 s).mono hlo2)), hlo2, hhi2,
        le_trans (le_trans hg1 hg2) (settleEventGrowth hm2.active hb2)⟩
      apply ExecBlock.consNormal hstore
      apply ExecBlock.consNormal hsrc1
      apply ExecBlock.consNormal hsrc2
      exact ExecBlock.consReturn (ExecStmt.return (by
        simp only [evalExprs?, evalExpr?, hv2.ptr, EvalResult.ofOption, pure, bind,
          EvalResult.bind]))
    · exact Or.inr ⟨ExecBlock.consNormal hstore
        (ExecBlock.consNormal hsrc1 (ExecBlock.consRevert hbad)), hr⟩
  · exact Or.inr ⟨ExecBlock.consNormal hstore (ExecBlock.consRevert hbad), hr⟩

end Auction

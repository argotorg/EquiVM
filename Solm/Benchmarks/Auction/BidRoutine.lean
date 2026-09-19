import Solm.Benchmarks.Auction.BidMinimumCheck
import Solm.Benchmarks.Auction.BidAfter
import Solm.Benchmarks.Auction.ReentrancyGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def bidParams (noun : UInt256) : Store := (∅ : Store).insert "nounId" (.int (Int.ofNat noun.toNat))

theorem bidBody_eq : createBidTransition.body =
    [.require (.binary .ne (.storage statusRef) entered), .assign .storage statusRef entered,
      .letDecl "_auction" none (.storage auctionRef)] ++
      (bidInitialGuardStmts ++ (.require bidMinimumGuard :: bidAfterStmts)) := rfl

theorem bidRoutine {I g s0 noun ret R mem aw rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨1165⟩ (noun :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ⟨128⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 28 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := bidParams noun } evm
        createBidTransition.body (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C') ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := bidParams noun } evm
      createBidTransition.body .reverted ∧ RDrev auctionBytecode g s0) := by
  rw [bidBody_eq]
  have hstatus := statusGuardSource (locals := bidParams noun) hs (by simp [bidParams])
  by_cases hentered : storedWord σ I ⟨101⟩ = ⟨2⟩
  · rw [decide_eq_false (not_not_intro hentered)] at hstatus
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.requireFalse hstatus),
      reentrancyDenied 0 h hentered (by evm_ov)⟩
  · rw [decide_eq_true hentered] at hstatus
    obtain ⟨_, _, rd1199⟩ := reentrancyAllowed 0 h hentered (by evm_ov)
    have rd1204 := evm_run rd1199 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
    obtain ⟨_, _, rd1205⟩ := rd1204.sstore hperm (by native_decide) (by evm_ov)
    have hs2 := hs.status ⟨2⟩
    let σ2 := sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨2⟩
    let s := snapshotOf σ2 I
    let locals2 := (bidParams noun).insert "_auction" s.value
    have hv : BidValues locals2 s noun := by
      refine ⟨store_get_self _ _ _, (store_get_ne _ _ (by decide)).trans
        (store_get_self _ _ _), ?_⟩
      intro name hn
      simp only [bidStorageNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp [locals2, bidParams]
    have hstore := statusStoreSource (evm := evm) (locals := bidParams noun) (word := ⟨2⟩)
      (e := entered) (by simp [bidParams]) (by simp only [entered, evalExpr?, pure]; rfl)
    have hsnap := snapshotSourceRead (statusState evm ⟨2⟩) (bidParams noun) (by simp [bidParams])
    rw [snapshotSourceState hs2] at hsnap
    have hprefix : ExecBlock auctionConfig
        { contract := auctionContract, locals := bidParams noun } evm
        [.require (.binary .ne (.storage statusRef) entered), .assign .storage statusRef entered,
          .letDecl "_auction" none (.storage auctionRef)]
        (.ok { contract := auctionContract, locals := locals2 } (statusState evm ⟨2⟩)) :=
      ExecBlock.consNormal (ExecStmt.requireTrue hstatus)
        (ExecBlock.consNormal hstore (ExecBlock.consNormal (ExecStmt.letDecl hsnap) ExecBlock.nil))
    obtain ⟨_, _, rd1282⟩ := bidSnapshotPrefix rd1205 hm (by decide) (by evm_ov)
    have hsm := snapshotMemory_made s hm (by decide)
    have hm2 := s.mem_heap hm (by decide)
    rcases bidInitialChecks rd1282 hs2 hsm hv (by evm_ov) with
      ⟨_, _, hchecks, ht, rd1511⟩ | ⟨hchecks, hr⟩
    · rcases bidMinimumCheck rd1511 hs2 hsm hv (by evm_ov) with
        ⟨_, _, hminimum, rd1681⟩ | ⟨hminimum, hr⟩
      · rcases bidAfterRoutine rd1681 hs2 hperm hm2 hsm hv ht hret hov with
          ⟨evm', cA', σ', locals', mem', aw', out, _, _, hafter, hs', hr⟩ | ⟨hafter, hr⟩
        · exact Or.inl ⟨evm', cA', σ', locals', mem', aw', out, _, _,
            execBlock_append hprefix (execBlock_append hchecks
              (ExecBlock.consNormal hminimum hafter)), hs', hr⟩
        · exact Or.inr ⟨execBlock_append hprefix (execBlock_append hchecks
            (ExecBlock.consNormal hminimum hafter)), hr⟩
      · exact Or.inr ⟨execBlock_append hprefix (execBlock_append hchecks
          (ExecBlock.consRevert hminimum)), hr⟩
    · exact Or.inr ⟨execBlock_append hprefix (execBlock_append_term hchecks (by simp)), hr⟩

end Auction

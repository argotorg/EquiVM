import Benchmarks.Auction.SettleAfter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem settleChecks {I g s0 s snap ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨4162⟩ (snap :: Snapshot.startTime s :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 141 ≤ 2 ^ 200)
    (hsm : SnapshotMemory s mem aw snap) (hsep : snap.toNat + 192 ≤ ptr.toNat)
    (hv : SettleValues locals s ptr)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        (settleGuardStmts ++ settleAfterStmts)
        (.returned { contract := auctionContract, locals := locals' } evm'
          (some [.int (Int.ofNat ptr'.toNat)])) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C' ∧
      HeapMemory mem' aw' ptr' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 140 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      (settleGuardStmts ++ settleAfterStmts) .reverted ∧ RDrev auctionBytecode g s0) := by
  have he0 := settleStartGuardSource (evm := evm) hv.snapshot
  by_cases hz0 : s.startTime = ⟨0⟩
  · rw [decide_eq_false (not_not_intro hz0)] at he0
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.requireFalse he0),
      settleNotStarted h hz0 (by omega)⟩
  · rw [decide_eq_true hz0] at he0
    obtain ⟨_, _, rd4231⟩ := settleStarted h hz0 (by omega)
    have he1 := settleUnsettledGuardSource (evm := evm) hv.snapshot
    by_cases hz1 : s.settledByte = ⟨0⟩
    · rw [decide_eq_true hz1] at he1
      obtain ⟨_, _, rd4313⟩ := settleUnsettled rd4231 hsm hz1 (by omega)
      have he2 := settleEndGuardSource (evm := evm) hv.snapshot
      rw [hs.env] at he2
      by_cases ht : s.endTime.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat
      · rw [decide_eq_true ht] at he2
        obtain ⟨_, _, rd4397⟩ := settleEnded rd4313 hsm ht (by omega)
        rcases settleAfter rd4397 hs hperm hm hb hsm hsep hv hret hov with
          ⟨evm', cA', σ', locals', mem', aw', ptr', out, _, _, hsrc, hs', hr, hm', hp,
            hlo, hhi, hg⟩ | ⟨hbad, hr⟩
        · exact Or.inl ⟨evm', cA', σ', locals', mem', aw', ptr', out, _, _,
            ExecBlock.consNormal (ExecStmt.requireTrue he0)
              (ExecBlock.consNormal (ExecStmt.requireTrue he1)
                (ExecBlock.consNormal (ExecStmt.requireTrue he2) hsrc)),
            hs', hr, hm', hp, hlo, hhi, hg⟩
        · exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.requireTrue he0)
            (ExecBlock.consNormal (ExecStmt.requireTrue he1)
              (ExecBlock.consNormal (ExecStmt.requireTrue he2) hbad)), hr⟩
      · rw [decide_eq_false ht] at he2
        exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.requireTrue he0)
          (ExecBlock.consNormal (ExecStmt.requireTrue he1)
            (ExecBlock.consRevert (ExecStmt.requireFalse he2))),
          settleNotEnded rd4313 hsm (by omega) (by omega)⟩
    · rw [decide_eq_false hz1] at he1
      exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.requireTrue he0)
        (ExecBlock.consRevert (ExecStmt.requireFalse he1)),
        settleAlreadySettled rd4231 hsm hz1 (by omega)⟩

end Auction

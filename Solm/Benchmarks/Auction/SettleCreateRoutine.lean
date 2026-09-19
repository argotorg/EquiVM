import Solm.Benchmarks.Auction.SettleCreateEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def settleCreateStmts : List Stmt := settleAndCreateTransition.body.drop 1

theorem settleCreateRoutine {I g s0 ret R mem aw rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨2573⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ⟨128⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 27 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm
        settleCreateStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C') ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleCreateStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  have hstatus := statusGuardSource (locals := ∅) hs (by simp)
  by_cases hentered : storedWord σ I ⟨101⟩ = ⟨2⟩
  · rw [decide_eq_false (not_not_intro hentered)] at hstatus
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.requireFalse hstatus),
      reentrancyDenied 2 h hentered (by evm_ov)⟩
  · rw [decide_eq_true hentered] at hstatus
    obtain ⟨_, _, rd2607⟩ := reentrancyAllowed 2 h hentered (by evm_ov)
    obtain ⟨_, _, rd2623⟩ := settleCreateEnter rd2607 hperm (by evm_ov)
    have hs2 := hs.status ⟨2⟩
    have hstore := statusStoreSource (evm := evm) (locals := ∅) (word := ⟨2⟩)
      (e := entered) (by simp) (by simp only [entered, evalExpr?, pure]; rfl)
    have hprefix : ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm
        [.require (.binary .ne (.storage statusRef) entered), .assign .storage statusRef entered]
        (.ok { contract := auctionContract, locals := ∅ } (statusState evm ⟨2⟩)) :=
      ExecBlock.consNormal (ExecStmt.requireTrue hstatus) (ExecBlock.consNormal hstore
        ExecBlock.nil)
    by_cases hp : pausedWord (sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨2⟩) I = ⟨0⟩
    · have hpaused := readNotPausedTrue (statusState evm ⟨2⟩) ∅ (by simp) (by
        rw [hs2.env, ← pausedWord_equiv hs2.accounts]
        exact hp)
      obtain ⟨_, _, rd4086⟩ := settleCreateUnpaused rd2623 hp (by evm_ov)
      have hargs : evalExprs? auctionConfig { contract := auctionContract, locals := ∅ }
          (statusState evm ⟨2⟩) [.intLit 128] =
          .ok [.int (Int.ofNat (⟨128⟩ : UInt256).toNat)] := by
        simp only [evalExprs?, evalExpr?, pure, bind, EvalResult.bind]
        rfl
      rcases settleInternalRoutine rd4086 hs2 hperm hm
          (by change 128 + 2 ^ 142 ≤ 2 ^ 200; decide) hargs (retVar := "_s")
          (by jump_dest) (by evm_ov) with
        ⟨evmS, cAS, σS, memS, awS, ptrS, outS, _, _, hsettle, hsS, rd2690,
          hmS, _, _, hhi, _⟩ | ⟨hsettle, hrev⟩
      · obtain ⟨_, _, rd3000⟩ := settleCreateNext rd2690 (by evm_ov)
        have hargsC : evalExprs? auctionConfig
            { contract := auctionContract
              locals := (∅ : Store).insert "_s" (.int (Int.ofNat ptrS.toNat)) }
            evmS [.var "_s"] = .ok [.int (Int.ofNat ptrS.toNat)] := by
          simp only [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption,
            pure, bind, EvalResult.bind]
        rcases createInternalRoutine rd3000 hsS hperm hmS (by
            change ptrS.toNat ≤ 128 + 2 ^ 141 at hhi
            omega) hargsC (retVar := "_c") (by jump_dest) (by evm_ov) with
          ⟨evmC, cAC, σC, memC, awC, outC, _, _, hcreate, hsC, rd2471⟩ | ⟨hcreate, hrev⟩
        · obtain ⟨_, _, rdret⟩ := settleExit rd2471 hperm hret (by evm_ov)
          have hexit := statusStoreSource (evm := evmC)
            (locals := ((∅ : Store).insert "_s" (.int (Int.ofNat ptrS.toNat))).insert "_c" .unit)
            (word := ⟨1⟩) (e := notEntered) (by simp)
            (by simp only [notEntered, evalExpr?, pure]; rfl)
          refine Or.inl ⟨statusState evmC ⟨1⟩, cAC, _,
            ((∅ : Store).insert "_s" (.int (Int.ofNat ptrS.toNat))).insert "_c" .unit,
            memC, awC, outC, _, _, ?_,
            hsC.status ⟨1⟩, rdret⟩
          exact execBlock_append hprefix (ExecBlock.consNormal (ExecStmt.requireTrue hpaused)
            (ExecBlock.consNormal hsettle (ExecBlock.consNormal hcreate
              (ExecBlock.consNormal hexit ExecBlock.nil))))
        · exact Or.inr ⟨execBlock_append hprefix
            (ExecBlock.consNormal (ExecStmt.requireTrue hpaused)
              (ExecBlock.consNormal hsettle (ExecBlock.consRevert hcreate))), hrev⟩
      · exact Or.inr ⟨execBlock_append hprefix (ExecBlock.consNormal (ExecStmt.requireTrue hpaused)
          (ExecBlock.consRevert hsettle)), hrev⟩
    · have hpaused := readNotPausedFalse (statusState evm ⟨2⟩) ∅ (by simp) (by
        rw [hs2.env, ← pausedWord_equiv hs2.accounts]
        exact hp)
      exact Or.inr ⟨execBlock_append hprefix (ExecBlock.consRevert (ExecStmt.requireFalse hpaused)),
        settleCreatePaused rd2623 hp (by evm_ov)⟩

end Auction

import Benchmarks.Auction.SettleEntry
import Benchmarks.Auction.Events

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem settleAuctionBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 13))
    (hreach : EntryReached 13 σ σ₀ A I g) :
    runtimeEquivalenceFor auctionConfig auctionContract σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 13 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 13) (entryBytes_size 13) hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hs0 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I σ evm0 := SourceState.init
    obtain ⟨_, _, rd765⟩ := hreach
    obtain ⟨_, _, rd778⟩ := entryGuardZero 13 (by decide) rd765 hwv
    have rd2351 := evm_run rd778 with [push2 ⟨413⟩, push2 ⟨2351⟩, jump (by jump_dest)]
    by_cases hp : pausedWord σ I = ⟨0⟩
    · have he := readPausedFalse evm0 ∅ (by simp) hp
      have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
          settleAuctionTransition.body .reverted := by
        apply ExecFuncBody.execBlockRevert
        exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
          (ExecBlock.consRevert (ExecStmt.requireFalse he))
      exact (settleNotPaused rd2351 hp (by evm_ov)).reEquivExecutionRevert hcode hd hdec hbody
    · obtain ⟨_, _, rd2424⟩ := settlePaused rd2351 hp (by evm_ov)
      have hpaused := readPausedTrue evm0 ∅ (by simp) hp
      have hstatus := statusGuardSource (locals := ∅) hs0 (by simp)
      by_cases hentered : solcSlotWord σ I ⟨101⟩ = ⟨2⟩
      · rw [decide_eq_false (not_not_intro hentered)] at hstatus
        have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
            settleAuctionTransition.body .reverted := by
          apply ExecFuncBody.execBlockRevert
          exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
            (ExecBlock.consNormal (ExecStmt.requireTrue hpaused)
              (ExecBlock.consRevert (ExecStmt.requireFalse hstatus)))
        exact (reentrancyDenied 1 rd2424 hentered (by evm_ov)).reEquivExecutionRevert
          hcode hd hdec hbody
      · rw [decide_eq_true hentered] at hstatus
        obtain ⟨_, _, rd2458⟩ := reentrancyAllowed 1 rd2424 hentered (by evm_ov)
        obtain ⟨_, _, rd4086⟩ := settleEnter rd2458 hperm (by evm_ov)
        have hstore := statusStoreSource (evm := evm0) (locals := ∅) (word := ⟨2⟩)
          (e := entered) (by simp) (by simp only [entered, evalExpr?, pure]; rfl)
        have hargs : evalExprs? auctionConfig { contract := auctionContract, locals := ∅ }
            (statusState evm0 ⟨2⟩) [.intLit 128] = .ok [.int (Int.ofNat (⟨128⟩ :
              UInt256).toNat)] := by
          simp only [evalExprs?, evalExpr?, pure, bind, EvalResult.bind]
          rfl
        rcases settleInternalRoutine rd4086 ((SourceState.status hs0) ⟨2⟩) hperm freshHeapMemory
            (by change 128 + 2 ^ 142 ≤ 2 ^ 200; decide) hargs (retVar := "_s")
            (by jump_dest) (by evm_ov) with
          ⟨evm', σ', mem', aw', ptr', out, _, _, hcall, hs', rd2471, _, _, _, _, _⟩ |
            ⟨hcall, hr⟩
        · obtain ⟨_, _, rd413⟩ := settleExit rd2471 hperm (by jump_dest) (by evm_ov)
          have hexit := statusStoreSource (evm := evm')
            (locals := (∅ : Store).insert "_s" (.int (Int.ofNat ptr'.toNat))) (word := ⟨1⟩)
            (e := notEntered) (by simp) (by simp only [notEntered, evalExpr?, pure]; rfl)
          have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
              settleAuctionTransition.body
              (.returned
                { contract := auctionContract
                  locals := (∅ : Store).insert "_s" (.int (Int.ofNat ptr'.toNat)) }
                (statusState evm' ⟨1⟩) none) := by
            apply ExecFuncBody.execBlockOK
            exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
              (ExecBlock.consNormal (ExecStmt.requireTrue hpaused)
                (ExecBlock.consNormal (ExecStmt.requireTrue hstatus)
                  (ExecBlock.consNormal hstore (ExecBlock.consNormal hcall
                    (ExecBlock.consNormal hexit ExecBlock.nil)))))
          have hsFinal := (SourceState.status hs') ⟨1⟩
          exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGen
            hcode hd hdec hbody hsFinal.accounts
            (.fallthrough rfl rfl (by native_decide))
        · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
              settleAuctionTransition.body .reverted := by
            apply ExecFuncBody.execBlockRevert
            exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
              (ExecBlock.consNormal (ExecStmt.requireTrue hpaused)
                (ExecBlock.consNormal (ExecStmt.requireTrue hstatus)
                  (ExecBlock.consNormal hstore (ExecBlock.consRevert hcall))))
          exact hr.reEquivExecutionRevert hcode hd hdec hbody
  · exact entryNonpayableRevert 13 (by decide) hcode hsel hreach hwv

end Auction

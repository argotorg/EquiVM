import Benchmarks.Auction.UnpauseRoutine
import Benchmarks.Auction.UnpauseAfter
import Benchmarks.Auction.Events

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem unpauseBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 3))
    (hreach : EntryReached 3 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 3 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 3) (entryBytes_size 3) hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (unpauseTransition.params.map Param.name)
        (transitionSignature unpauseTransition).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hs0 : SourceState (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        I cA σ_evm evm0 := SourceState.init hAccounts
    obtain ⟨_, _, rd415⟩ := hreach
    obtain ⟨_, _, rd428⟩ := entryGuardZero 3 (by decide) rd415 hwv
    have rd1076 := evm_run rd428 with [push2 ⟨413⟩, push2 ⟨1076⟩, jump (by jump_dest)]
    by_cases ho : solcSourceWord I = ownerWord σ_evm I
    · obtain ⟨_, _, rd1118⟩ := ownerAllowed 1 rd1076 ho (by evm_ov)
      have rd2853 := evm_run rd1118 with [jumpdest, push2 ⟨1126⟩, push2 ⟨2853⟩,
        jump (by jump_dest)]
      have howner := evalOwnerEq_true evm0 ∅ (by simp) (by
        change solcSourceWord I = ownerWord σ_solm I
        rw [← ownerWord_equiv hAccounts I]
        exact ho)
      by_cases hp : pausedWord σ_evm I = ⟨0⟩
      · have hpaused := readPausedFalse evm0 ∅ (by simp) (by
          change pausedWord σ_solm I = ⟨0⟩
          rw [← pausedWord_equiv hAccounts I]
          exact hp)
        have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
            unpauseTransition.body .reverted :=
          ExecFuncBody.execBlockRevert (ExecBlock.consNormal
            (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
            (ExecBlock.consNormal (ExecStmt.requireTrue howner)
              (ExecBlock.consRevert (ExecStmt.requireFalse hpaused))))
        exact (unpauseRoutineRevert rd2853 hp (by evm_ov)).reEquivExecutionRevert
          hcode hd hdec hbody
      · obtain ⟨_, _, rd1126⟩ := unpauseRoutineOk rd2853 hp hperm (by jump_dest) (by evm_ov)
        have hpaused := readPausedTrue evm0 ∅ (by simp) (by
          change pausedWord σ_solm I ≠ ⟨0⟩
          rw [← pausedWord_equiv hAccounts I]
          exact hp)
        have hprefix : ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm0
            [nonpayable, .require (.binary .eq sender (.storage ownerRef)),
              .require (.storage pausedRef), .assign .storage pausedRef (.boolLit false)]
            (.ok { contract := auctionContract, locals := ∅ } (unpauseState evm0)) :=
          ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
            (ExecBlock.consNormal (ExecStmt.requireTrue howner)
              (ExecBlock.consNormal (ExecStmt.requireTrue hpaused)
                (ExecBlock.consNormal (unpauseStoreSource (by simp)) ExecBlock.nil)))
        rcases unpauseAfterRoutine rd1126 hs0.unpause hperm
            (addressEventHeap freshHeapMemory (solcSourceWord I) (by decide))
            (by jump_dest) (by evm_ov) with
          ⟨evm', cA', σ', locals', mem', aw', out, _, _, hafter, hs', rd413⟩ | ⟨hafter, hr⟩
        · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
              unpauseTransition.body
              (.returned { contract := auctionContract, locals := locals' } evm' none) :=
            ExecFuncBody.execBlockOK (execBlock_append hprefix
              (ExecBlock.consNormal hafter ExecBlock.nil))
          exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
            hcode hd hdec hbody hs'.created.symm hs'.accounts
            (.fallthrough rfl rfl (by native_decide))
        · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
              unpauseTransition.body .reverted :=
            ExecFuncBody.execBlockRevert (execBlock_append hprefix (ExecBlock.consRevert hafter))
          exact hr.reEquivExecutionRevert hcode hd hdec hbody
    · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
          unpauseTransition.body .reverted := by
        apply ownerBodyReverts _ _ _ hwv
        · change solcSourceWord I ≠ ownerWord σ_solm I
          rw [← ownerWord_equiv hAccounts I]
          exact ho
        · simp
      exact (ownerDenied 1 rd1076 ho (by evm_ov)).reEquivExecutionRevert hcode hd hdec hbody
  · exact entryNonpayableRevert 3 (by decide) hcode hsel hreach hwv

end Auction

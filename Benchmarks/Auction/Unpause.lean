import Benchmarks.Auction.UnpauseRoutine
import Benchmarks.Auction.UnpauseAfter
import Benchmarks.Auction.Events

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem unpauseBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 3))
    (hreach : EntryReached 3 σ σ₀ A I g) :
    runtimeEquivalenceFor auctionConfig auctionContract σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 3 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 3) (entryBytes_size 3) hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (unpauseTransition.params.map Param.name)
        (transitionSignature unpauseTransition).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hs0 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I σ evm0 := SourceState.init
    obtain ⟨_, _, rd415⟩ := hreach
    obtain ⟨_, _, rd428⟩ := entryGuardZero 3 (by decide) rd415 hwv
    have rd1076 := evm_run rd428 with [push2 ⟨413⟩, push2 ⟨1076⟩, jump (by jump_dest)]
    by_cases ho : solcSourceWord I = ownerWord σ I
    · obtain ⟨_, _, rd1118⟩ := ownerAllowed 1 rd1076 ho (by evm_ov)
      have rd2853 := evm_run rd1118 with [jumpdest, push2 ⟨1126⟩, push2 ⟨2853⟩,
        jump (by jump_dest)]
      have howner := evalOwnerEq_true evm0 ∅ (by simp) ho
      by_cases hp : pausedWord σ I = ⟨0⟩
      · have hpaused := readPausedFalse evm0 ∅ (by simp) hp
        have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
            unpauseTransition.body .reverted :=
          ExecFuncBody.execBlockRevert (ExecBlock.consNormal
            (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
            (ExecBlock.consNormal (ExecStmt.requireTrue howner)
              (ExecBlock.consRevert (ExecStmt.requireFalse hpaused))))
        exact (unpauseRoutineRevert rd2853 hp (by evm_ov)).reEquivExecutionRevert
          hcode hd hdec hbody
      · have hpaused := readPausedTrue evm0 ∅ (by simp) hp
        have hstoreSplit := unpauseStoreSourceSplit (evm := evm0) (locals := ∅) (by simp)
        have hprefix {result : ExecResult}
            (hwrite : ExecBlock auctionConfig { contract := auctionContract, locals := ∅ }
              evm0 [.assign .storage pausedRef (.boolLit false)] result) :
            ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm0
              [nonpayable, .require (.binary .eq sender (.storage ownerRef)),
                .require (.storage pausedRef), .assign .storage pausedRef (.boolLit false)]
              result :=
          ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
            (ExecBlock.consNormal (ExecStmt.requireTrue howner)
              (ExecBlock.consNormal (ExecStmt.requireTrue hpaused) hwrite))
        rcases unpauseRoutineOkSplit rd2853 hp (by jump_dest) (by evm_ov) with
          ⟨hperm, _, _, rd1126⟩ | ⟨hperm, hstatic⟩
        swap
        · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
              unpauseTransition.body .staticViolation := by
            apply ExecFuncBody.execBlockStatic
            exact execBlock_append_term
              (hprefix (ExecBlock.consStatic (hstoreSplit.2 hperm))) (by intro _ _ h; cases h)
          exact hstatic.reEquivStaticHalt hcode hd hdec hbody
        have hprefixOK := hprefix (ExecBlock.consNormal hstoreSplit.1 ExecBlock.nil)
        rcases unpauseAfterRoutine rd1126 (SourceState.unpause hs0) hperm
            (addressEventHeap freshHeapMemory (solcSourceWord I) (by decide))
            (by jump_dest) (by evm_ov) with
          ⟨evm', σ', locals', mem', aw', out, _, _, hafter, hs', rd413⟩ | ⟨hafter, hr⟩
        · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
              unpauseTransition.body
              (.returned { contract := auctionContract, locals := locals' } evm' none) :=
            ExecFuncBody.execBlockOK (execBlock_append hprefixOK
              (ExecBlock.consNormal hafter ExecBlock.nil))
          exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGen
            hcode hd hdec hbody hs'.accounts
            (.fallthrough rfl rfl (by native_decide))
        · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
              unpauseTransition.body .reverted :=
            ExecFuncBody.execBlockRevert (execBlock_append hprefixOK (ExecBlock.consRevert hafter))
          exact hr.reEquivExecutionRevert hcode hd hdec hbody
    · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
          unpauseTransition.body .reverted := by
        apply ownerBodyReverts _ _ _ hwv
        · exact ho
        · simp
      exact (ownerDenied 1 rd1076 ho (by evm_ov)).reEquivExecutionRevert hcode hd hdec hbody
  · exact entryNonpayableRevert 3 (by decide) hcode hsel hreach hwv

end Auction

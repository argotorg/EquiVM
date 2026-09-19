import Solm.Benchmarks.Auction.SettleCreateRoutine
import Solm.Benchmarks.Auction.Events

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem settleCurrentAndCreateNewAuctionBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 18))
    (hreach : EntryReached 18 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 18 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 18) (entryBytes_size 18) hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAndCreateTransition.params.map Param.name)
        (transitionSignature settleAndCreateTransition).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hs0 : SourceState (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        I cA σ_evm evm0 := SourceState.init hAccounts
    obtain ⟨_, _, rd901⟩ := hreach
    obtain ⟨_, _, rd914⟩ := entryGuardZero 18 (by decide) rd901 hwv
    have rd2573 := evm_run rd914 with [push2 ⟨413⟩, push2 ⟨2573⟩, jump (by jump_dest)]
    rcases settleCreateRoutine rd2573 hs0 hperm freshHeapMemory (by jump_dest) (by evm_ov) with
      ⟨evm', cA', σ', locals', mem', aw', out, _, _, hsrc, hs', rd413⟩ | ⟨hsrc, hr⟩
    · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
          settleAndCreateTransition.body
          (.returned { contract := auctionContract, locals := locals' } evm' none) :=
        ExecFuncBody.execBlockOK (ExecBlock.consNormal
          (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) hsrc)
      exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
        hcode hd hdec hbody hs'.created.symm hs'.accounts
        (.fallthrough rfl rfl (by native_decide))
    · have hbody : ExecTransitionBody auctionConfig auctionContract evm0 ∅
          settleAndCreateTransition.body .reverted :=
        ExecFuncBody.execBlockRevert (ExecBlock.consNormal
          (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) hsrc)
      exact hr.reEquivExecutionRevert hcode hd hdec hbody
  · exact entryNonpayableRevert 18 (by decide) hcode hsel hreach hwv

end Auction

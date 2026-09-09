import Benchmarks.Auction.CreateBidRefund

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidTransitionReverts_refundReverted
    (evm : EVM.State) (I : ExecutionEnv) 
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hsafe : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore
          (AccountAddress.ofNat (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat)
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩) }
      (auctionCreateBidEnterState evm) safeTransferETHWithFallback.body
      .reverted) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consRevert
        (internalCallFunctionRevert
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (by simpa only [evmEnter, recipient, amount] using hsafe))))


set_option maxHeartbeats 1000000 in
theorem auctionCreateBidTransitionReverts_extensionOverflow_refundReturned
    (evm evmRefund : EVM.State) (I : ExecutionEnv) {csRefund : Frame}
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hsafe : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore
          (AccountAddress.ofNat (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat)
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩) }
      (auctionCreateBidEnterState evm) safeTransferETHWithFallback.body
      (.returned csRefund evmRefund none))
    (hle :
      (UInt256.ofNat
        (auctionCreateBidBidderState
          (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hextended :
      (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp)).toNat <
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat +
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let localsRefund := localsLast.insert "_refund" .unit
  let evmAmount := auctionCreateBidAmountState evmRefund
  let evmBidder := auctionCreateBidBidderState evmAmount
  let localsExtended := localsRefund.insert "extended" (.bool true)
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (by simpa only [evmEnter, recipient, amount] using hsafe))
        ExecBlock.nil)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmRefund localsRefund)
      (auctionCreateAuctionAssignUint256Field evmRefund localsRefund "amount" ⟨208⟩
        evmRefund.executionEnv.weiValue
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsRefund)
      (auctionCreateAuctionAssignAddressField evmAmount localsRefund "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_true_after_refund evmEnter evmBidder I
      (by simpa [evmBidder, evmAmount] using hle)
      (by simpa [evmEnter, evmBidder, evmAmount] using hextended))) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (result := .reverted)
    (by simp [evalExpr?, EvalResult.ofOption]) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (by
          simpa [localsExtended, localsRefund, localsLast, evmBidder, evmAmount] using
            evalExpr_createBid_extendedEndTime_revert_after_refund evmEnter evmBidder I
              (by simpa [evmBidder, evmAmount] using hover)))


set_option maxHeartbeats 1000000 in
theorem auctionCreateBidTransitionReturns_noExtension_refundReturned
    (evm evmRefund : EVM.State) (I : ExecutionEnv) {csRefund : Frame}
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hsafe : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore
          (AccountAddress.ofNat (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat)
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩) }
      (auctionCreateBidEnterState evm) safeTransferETHWithFallback.body
      (.returned csRefund evmRefund none))
    (hle :
      (UInt256.ofNat
        (auctionCreateBidBidderState
          (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hnotExtended :
      (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat ≤
        (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp)).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body
      (.returned
        { contract := auctionContract,
          locals :=
            ((auctionCreateBidLastBidderStore (auctionCreateBidEnterState evm) I).insert
              "_refund" .unit).insert "extended" (.bool false) }
        (auctionCreateBidUnlockedState
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund)))
        none) := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let localsRefund := localsLast.insert "_refund" .unit
  let evmAmount := auctionCreateBidAmountState evmRefund
  let evmBidder := auctionCreateBidBidderState evmAmount
  let localsExtended := localsRefund.insert "extended" (.bool false)
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (by simpa only [evmEnter, recipient, amount] using hsafe))
        ExecBlock.nil)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmRefund localsRefund)
      (auctionCreateAuctionAssignUint256Field evmRefund localsRefund "amount" ⟨208⟩
        evmRefund.executionEnv.weiValue
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsRefund)
      (auctionCreateAuctionAssignAddressField evmAmount localsRefund "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_false_after_refund evmEnter evmBidder I
      (by simpa [evmBidder, evmAmount] using hle)
      (by simpa [evmEnter, evmBidder, evmAmount] using hnotExtended))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (by simp [evalExpr?, EvalResult.ofOption])
      ExecBlock.nil) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_notEntered evmBidder localsExtended)
      (auctionCreateBidAssignStatusNotEntered evmBidder localsExtended
        (by
          simp [localsExtended, localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])))
    ExecBlock.nil


set_option maxHeartbeats 1000000 in
theorem auctionCreateBidTransitionReturns_extension_refundReturned
    (evm evmRefund : EVM.State) (I : ExecutionEnv) {csRefund : Frame}
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hsafe : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore
          (AccountAddress.ofNat (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat)
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩) }
      (auctionCreateBidEnterState evm) safeTransferETHWithFallback.body
      (.returned csRefund evmRefund none))
    (hle :
      (UInt256.ofNat
        (auctionCreateBidBidderState
          (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hextended :
      (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp)).toNat <
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat)
    (haddExtFit :
      (UInt256.ofNat
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat +
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat <
        UInt256.size) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body
      (.returned
        { contract := auctionContract,
          locals :=
            ((auctionCreateBidLastBidderStore (auctionCreateBidEnterState evm) I).insert
              "_refund" .unit).insert "extended" (.bool true) }
        (auctionCreateBidUnlockedState
          (auctionCreateBidExtendedState
            (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))))
        none) := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let localsRefund := localsLast.insert "_refund" .unit
  let evmAmount := auctionCreateBidAmountState evmRefund
  let evmBidder := auctionCreateBidBidderState evmAmount
  let evmExtended := auctionCreateBidExtendedState evmBidder
  let localsExtended := localsRefund.insert "extended" (.bool true)
  have hassignEnd :
      assignStorageRef? auctionConfig
          { contract := auctionContract, locals := localsExtended }
          evmBidder .storage (aField "endTime")
          (.int (Int.ofNat
            (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
              (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩)).toNat)) =
        .ok ({ contract := auctionContract, locals := localsExtended }, evmExtended) := by
    exact auctionCreateAuctionAssignUint256Field evmBidder localsExtended "endTime" ⟨210⟩
      (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
        (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩))
      (by
        simp [localsExtended, localsRefund, localsLast, auctionCreateBidLastBidderStore,
          auctionCreateBidSnapshotStore, auctionCreateBidStore])
      (by decide) (by rfl)
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (by simpa only [evmEnter, recipient, amount] using hsafe))
        ExecBlock.nil)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmRefund localsRefund)
      (auctionCreateAuctionAssignUint256Field evmRefund localsRefund "amount" ⟨208⟩
        evmRefund.executionEnv.weiValue
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsRefund)
      (auctionCreateAuctionAssignAddressField evmAmount localsRefund "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_true_after_refund evmEnter evmBidder I
      (by simpa [evmBidder, evmAmount] using hle)
      (by simpa [evmEnter, evmBidder, evmAmount] using hextended))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := auctionContract, locals := localsExtended } evmExtended)
      (by simp [evalExpr?, EvalResult.ofOption]) ?_) ?_
  · exact ExecBlock.consNormal
      (ExecStmt.assign
        (by
          simpa [localsExtended, localsRefund, localsLast, evmBidder, evmAmount] using
            evalExpr_createBid_extendedEndTime_after_refund evmEnter evmBidder I
              (by simpa [evmBidder, evmAmount] using haddExtFit))
        hassignEnd)
      ExecBlock.nil
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_notEntered evmExtended localsExtended)
      (auctionCreateBidAssignStatusNotEntered evmExtended localsExtended
        (by
          simp [localsExtended, localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])))
    ExecBlock.nil


end Auction

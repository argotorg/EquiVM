import Benchmarks.Auction.SafeTransferWithMemorySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionSettleAuctionMemoryPayoutReverts
    (evm evmNoun : EVM.State) {ret : Ident} {tail : List Stmt}
    (hneAuction : (ret == "_auction") = false) (hneOwner : (ret == "_owner") = false)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpay : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore (auctionOwnerAddressAt evmNoun)
          (auctionSettleAuctionAmount evm) }
      evmNoun safeTransferETHWithMemory.body .reverted) :
    ExecBlock auctionConfig
      { contract := auctionContract,
        locals := (auctionSettleAuctionSnapshotStore evm).insert ret .unit }
      evmNoun
      (.ite (.binary .gt (auctionMemField "amount") (.intLit 0))
        auctionSettleAuctionMemoryPayout [] :: tail) .reverted := by
  refine ExecBlock.consRevert (ExecStmt.iteTrue
    (evalExpr_settleAuction_amount_positive_true_after_callResult
      evm evmNoun .unit hneAuction hamount) ?_)
  exact ExecBlock.consRevert
    (internalCallFunctionRevert (callee := safeTransferETHWithMemory)
      (evalExprs_settleAuction_pay_args_after_callResult
        evm evmNoun .unit hneAuction hneOwner) (by rfl) (by rfl) hpay)

theorem auctionSettleAuctionMemoryPayoutReturn
    (evm evmNoun evmPay : EVM.State) {ret : Ident} {payFrame : Frame} {free : UInt256}
    {tail : List Stmt}
    (hneAuction : (ret == "_auction") = false) (hneOwner : (ret == "_owner") = false)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpay : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore (auctionOwnerAddressAt evmNoun)
          (auctionSettleAuctionAmount evm) }
      evmNoun safeTransferETHWithMemory.body
      (.returned payFrame evmPay (some [.int (Int.ofNat free.toNat)]))) :
    ExecBlock auctionConfig
      { contract := auctionContract,
        locals := (auctionSettleAuctionSnapshotStore evm).insert ret .unit }
      evmNoun
      (.ite (.binary .gt (auctionMemField "amount") (.intLit 0))
        auctionSettleAuctionMemoryPayout [] :: tail)
      (.returned
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore evm).insert ret .unit }
          "_pay" (some [.int (Int.ofNat free.toNat)]))
        evmPay (some [.int (Int.ofNat free.toNat)])) := by
  refine ExecBlock.consReturn (ExecStmt.iteTrue
    (evalExpr_settleAuction_amount_positive_true_after_callResult
      evm evmNoun .unit hneAuction hamount) ?_)
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (callee := safeTransferETHWithMemory) (calleeSolm := payFrame)
      (evalExprs_settleAuction_pay_args_after_callResult
        evm evmNoun .unit hneAuction hneOwner)
      (by rfl) (by rfl) hpay) ?_
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
    simp [resumeAfterInternalCall, evalExpr?, EvalResult.ofOption, collapseReturns])))

theorem auctionSettleAuctionWithMemoryReturns_burnNoPayout
    (evm evmBurn : EVM.State) {out : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩ = ⟨0⟩) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionWithMemoryFn.body
      (.returned
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert "_burn" .unit }
        evmBurn (some [.int 320])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine auctionSettleAuctionBlock_burn evm evmBurn
    (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_settleAuction_amount_positive_false_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      ExecBlock.nil)
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by simp only [evalExpr?, pure]))))

theorem auctionSettleAuctionWithMemoryReturns_transferFromNoPayout
    (evm evmTransfer : EVM.State) {out : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩ = ⟨0⟩) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionWithMemoryFn.body
      (.returned
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert "_tf" .unit }
        evmTransfer (some [.int 320])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine auctionSettleAuctionBlock_transferFrom evm evmTransfer
    (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_settleAuction_amount_positive_false_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      ExecBlock.nil)
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by simp only [evalExpr?, pure]))))

theorem auctionSettleAuctionWithMemoryReturns_burnPayout
    (evm evmBurn evmPay : EVM.State) {out : ByteArray}
    {payFrame : Frame} {free : UInt256}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpay : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore (auctionOwnerAddressAt evmBurn)
          (auctionSettleAuctionAmount evm) }
      evmBurn safeTransferETHWithMemory.body
      (.returned payFrame evmPay (some [.int (Int.ofNat free.toNat)]))) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionWithMemoryFn.body
      (.returned
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore evm).insert "_burn" .unit }
          "_pay" (some [.int (Int.ofNat free.toNat)]))
        evmPay (some [.int (Int.ofNat free.toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine auctionSettleAuctionBlock_burn evm evmBurn
    (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact auctionSettleAuctionMemoryPayoutReturn evm evmBurn evmPay
    (by decide) (by decide) hamount hpay

theorem auctionSettleAuctionWithMemoryReturns_transferFromPayout
    (evm evmTransfer evmPay : EVM.State) {out : ByteArray}
    {payFrame : Frame} {free : UInt256}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpay : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore (auctionOwnerAddressAt evmTransfer)
          (auctionSettleAuctionAmount evm) }
      evmTransfer safeTransferETHWithMemory.body
      (.returned payFrame evmPay (some [.int (Int.ofNat free.toNat)]))) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionWithMemoryFn.body
      (.returned
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore evm).insert "_tf" .unit }
          "_pay" (some [.int (Int.ofNat free.toNat)]))
        evmPay (some [.int (Int.ofNat free.toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine auctionSettleAuctionBlock_transferFrom evm evmTransfer
    (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact auctionSettleAuctionMemoryPayoutReturn evm evmTransfer evmPay
    (by decide) (by decide) hamount hpay

theorem auctionSettleAuctionWithMemoryReverts_burnPayout
    (evm evmBurn : EVM.State) {out : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpay : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore (auctionOwnerAddressAt evmBurn)
          (auctionSettleAuctionAmount evm) }
      evmBurn safeTransferETHWithMemory.body
      .reverted) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionWithMemoryFn.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine auctionSettleAuctionBlock_burn evm evmBurn
    (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact auctionSettleAuctionMemoryPayoutReverts evm evmBurn
    (by decide) (by decide) hamount hpay

theorem auctionSettleAuctionWithMemoryReverts_transferFromPayout
    (evm evmTransfer : EVM.State) {out : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpay : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore (auctionOwnerAddressAt evmTransfer)
          (auctionSettleAuctionAmount evm) }
      evmTransfer safeTransferETHWithMemory.body
      .reverted) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionWithMemoryFn.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine auctionSettleAuctionBlock_transferFrom evm evmTransfer
    (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact auctionSettleAuctionMemoryPayoutReverts evm evmTransfer
    (by decide) (by decide) hamount hpay

end Auction

import Benchmarks.Auction.SettleAuctionSnapshotSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionSettleAuctionBlockAfterNounCall
    (evm evmCall : EVM.State) {frame : Frame} {payout tail : List Stmt} {result : ExecResult}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hcall : ExecStmt auctionConfig
      { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
      (auctionSettleAuctionMarkSettledState evm)
      (.ite (.binary .eq (auctionMemField "bidder") zeroAddr)
        (checkedExternalCallStmts (.storage nounsRef) "burn" (.intLit 0)
          [auctionMemField "nounId"] "_burn")
        (checkedExternalCallStmts (.storage nounsRef) "transferFrom" (.intLit 0)
          [.env .this, auctionMemField "bidder", auctionMemField "nounId"] "_tf"))
      (.ok frame evmCall))
    (hrest : ExecBlock auctionConfig frame evmCall
      (.ite (.binary .gt (auctionMemField "amount") (.intLit 0)) payout [] :: tail) result) :
    ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) result := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp only [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  exact ExecBlock.consNormal hcall hrest

theorem auctionSettleAuctionBlock_burn
    (evm evmBurn : EVM.State) {out : ByteArray} {payout tail : List Stmt} {result : ExecResult}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder : AccountAddress.ofNat
      (auctionPackedBidderWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
      AccountAddress.ofNat 0)
    (hnounsCode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
      (auctionSettleAuctionMarkSettledState evm)
      (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat)) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hrest : ExecBlock auctionConfig
      { contract := auctionContract,
        locals := (auctionSettleAuctionSnapshotStore evm).insert "_burn" .unit }
      evmBurn
      (.ite (.binary .gt (auctionMemField "amount") (.intLit 0)) payout [] :: tail) result) :
    ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) result := by
  apply auctionSettleAuctionBlockAfterNounCall evm evmBurn hstart hsettled htime
    (hrest := hrest)
  exact ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
    (checkedExternalCallSuccess hnounsCode (evalExpr_settleAuction_nouns_after_markSettled evm)
      (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall
      (auctionExternalABI_decode_burn out))

theorem auctionSettleAuctionBlock_transferFrom
    (evm evmTransfer : EVM.State) {out : ByteArray} {payout tail : List Stmt}
    {result : ExecResult}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder : AccountAddress.ofNat
      (auctionPackedBidderWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
      AccountAddress.ofNat 0)
    (hnounsCode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
      (auctionSettleAuctionMarkSettledState evm)
      (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat)) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hrest : ExecBlock auctionConfig
      { contract := auctionContract,
        locals := (auctionSettleAuctionSnapshotStore evm).insert "_tf" .unit }
      evmTransfer
      (.ite (.binary .gt (auctionMemField "amount") (.intLit 0)) payout [] :: tail) result) :
    ExecBlock auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) result := by
  apply auctionSettleAuctionBlockAfterNounCall evm evmTransfer hstart hsettled htime
    (hrest := hrest)
  exact ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
    (checkedExternalCallSuccess hnounsCode (evalExpr_settleAuction_nouns_after_markSettled evm)
      (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
      (auctionExternalABI_decode_transferFrom out))

end Auction

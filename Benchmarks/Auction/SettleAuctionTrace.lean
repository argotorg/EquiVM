import Benchmarks.Auction.SettleAuctionSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Auction

def auctionSafeTransferStore (recipient : AccountAddress) (amount : UInt256) : Store :=
  ((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert "to"
    (.address recipient)

def auctionSafeTransferFailureStore
    (recipient : AccountAddress) (amount : UInt256) (out : ByteArray) : Store :=
  ((auctionSafeTransferStore recipient amount).insert "success" (.bool false)).insert "_data"
    (.bytes out)

theorem bindParams_safeTransfer
    (recipient : AccountAddress) (amount : UInt256) :
    bindParams? safeTransferETHWithFallback.params
        [.address recipient, .int (Int.ofNat amount.toNat)] =
      some (auctionSafeTransferStore recipient amount) := by
  rfl

theorem evalExpr_safeTransfer_to
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
        evm (.var "to") =
      .ok (.address recipient) := by
  simp [auctionSafeTransferStore, evalExpr?, EvalResult.ofOption]

theorem evalExpr_safeTransfer_amount
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
        evm (.var "amount") =
      .ok (.int (Int.ofNat amount.toNat)) := by
  simp [auctionSafeTransferStore, evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem evalExpr_safeTransfer_emptyBytes
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
        evm (.newBytes (.intLit 0)) =
      .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, EvalResult.bind, bind]
  rfl

theorem evalExpr_safeTransfer_not_success_false
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) (out : ByteArray) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := ((auctionSafeTransferStore recipient amount).insert "success" (.bool true)).insert
            "_data" (.bytes out) }
        evm (.unary .not (.var "success")) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.ofOption, evalUnaryOp?, auctionSafeTransferStore,
    Std.HashMap.getElem_insert, Std.HashMap.getElem_insert_self, EvalResult.bind, bind]

theorem evalExpr_safeTransfer_not_success_true
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) (out : ByteArray) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
        evm (.unary .not (.var "success")) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.ofOption, evalUnaryOp?, auctionSafeTransferFailureStore,
    auctionSafeTransferStore, Std.HashMap.getElem_insert, Std.HashMap.getElem_insert_self,
    EvalResult.bind, bind]

theorem evalExpr_safeTransfer_weth
    (evm : EVM.State) (locals : Store) (hbase : locals.get? wethRef.base = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm (.storage wethRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals }
      evm wethRef = .ok { base := "weth", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, wethRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "weth", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    have hload := auctionStorageLocLoad_address_offset0 evm ⟨202⟩
    simpa [auctionAddrLoc] using hload)

theorem evalExpr_safeTransfer_wethCode
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) (out : ByteArray)
    (hcode :
      0 < (UInt256.ofNat (((evm.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
        evm (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool true) := by
  have hweth := evalExpr_safeTransfer_weth evm (auctionSafeTransferFailureStore recipient amount out)
    (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef])
  simp [evalExpr?, EvalResult.bind, bind, hweth, evalBinaryOp?, EVM.Word.ofNat]
  exact hcode

theorem evalExpr_safeTransfer_amount_after_failure
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) (out : ByteArray) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
        evm (.var "amount") = .ok (.int (Int.ofNat amount.toNat)) := by
  simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, evalExpr?, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem evalExprs_safeTransfer_transfer_args_after_deposit
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) (out : ByteArray) :
    evalExprs? auctionConfig
        { contract := auctionContract,
          locals := (auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit }
        evm [.var "to", .var "amount"] =
      .ok [.address recipient, .int (Int.ofNat amount.toNat)] := by
  simp [evalExprs?, auctionSafeTransferFailureStore, auctionSafeTransferStore, evalExpr?,
    EvalResult.ofOption, Std.HashMap.getElem_insert, EvalResult.bind, bind, pure]

theorem auctionExternalABI_decode_deposit (out : ByteArray) :
    auctionConfig.externalABI.decode? "deposit" out = some [] := by
  simp [auctionConfig, auctionExternalABI, isVoidExternal, decodeVoid?]

theorem auctionSafeTransferBodyReturns_lowLevelSuccess
    (evm evmCall : EVM.State) (recipient : AccountAddress) (amount : UInt256) {out : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (true, evmCall, out)) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount } evm
      safeTransferETHWithFallback.body
      (.returned
        { contract := auctionContract,
          locals := ((auctionSafeTransferStore recipient amount).insert "success" (.bool true)).insert
            "_data" (.bytes out) }
        evmCall none) := by
  dsimp [safeTransferETHWithFallback]
  refine ExecFuncBody.execBlockOK ?_
  exact ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount)
      hcall)
    (ExecBlock.consNormal
      (ExecStmt.iteFalse (evalExpr_safeTransfer_not_success_false evmCall recipient amount out)
        ExecBlock.nil) ExecBlock.nil)

theorem auctionSafeTransferBodyReturns_lowLevelFailureWethSuccess
    (evm evmCall evmDeposit evmTransfer : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit outTransfer : ByteArray}
    {transferOk : Bool}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmCall.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmCall
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat amount.toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address recipient, .int (Int.ofNat amount.toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
      some [.bool transferOk]) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount } evm
      safeTransferETHWithFallback.body
      (.returned
        { contract := auctionContract,
          locals := ((auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit).insert
            "_xfer" (.bool transferOk) }
        evmTransfer none) := by
  dsimp [safeTransferETHWithFallback, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount)
      hcall) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_safeTransfer_not_success_true evmCall recipient amount out) ?_)
    ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_safeTransfer_wethCode evmCall recipient amount out hwethCode)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_safeTransfer_weth evmCall (auctionSafeTransferFailureStore recipient amount out)
        (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
      (evalExpr_safeTransfer_amount_after_failure evmCall recipient amount out)
      (by rfl) hdeposit (auctionExternalABI_decode_deposit outDeposit)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_safeTransfer_weth evmDeposit
        ((auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit)
        (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
      (by simp [evalExpr?, pure])
      (evalExprs_safeTransfer_transfer_args_after_deposit evmDeposit recipient amount out)
      htransfer htransferDec)
    ExecBlock.nil

theorem auctionSettleAuctionBodyReverts_burnNoCode (evm : EVM.State)
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
    (hnounsNoCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool false))
    (payout : List Stmt := auctionSettleAuctionDefaultPayout)
    (tail : List Stmt := []) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) .reverted := by
  dsimp [settleAuctionBody, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallNoCode (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsNoCode))

theorem auctionSettleAuctionBodyReverts_transferFromNoCode (evm : EVM.State)
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
    (hnounsNoCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool false))
    (payout : List Stmt := auctionSettleAuctionDefaultPayout)
    (tail : List Stmt := []) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) .reverted := by
  dsimp [settleAuctionBody, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallNoCode (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsNoCode))

theorem auctionSettleAuctionBodyReverts_burnCallFailure
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
      (false, evmBurn, out) true)
    (payout : List Stmt := auctionSettleAuctionDefaultPayout)
    (tail : List Stmt := []) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) .reverted := by
  dsimp [settleAuctionBody, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallFailure (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall))

theorem auctionSettleAuctionBodyReverts_transferFromCallFailure
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
      (false, evmTransfer, out) true)
    (payout : List Stmt := auctionSettleAuctionDefaultPayout)
    (tail : List Stmt := []) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      (settleAuctionBody payout ++ tail) .reverted := by
  dsimp [settleAuctionBody, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallFailure (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall))

theorem auctionSettleAuctionBodyReturns_burnNoPayout
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
      settleAuctionFn.body
      (.returned
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert "_burn" .unit }
        evmBurn none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine auctionSettleAuctionBlock_burn evm evmBurn
    (payout := auctionSettleAuctionDefaultPayout) (tail := [])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_settleAuction_amount_positive_false_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      ExecBlock.nil) ExecBlock.nil

theorem auctionSettleAuctionBodyReturns_transferFromNoPayout
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
      settleAuctionFn.body
      (.returned
        { contract := auctionContract,
          locals := (auctionSettleAuctionSnapshotStore evm).insert "_tf" .unit }
        evmTransfer none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine auctionSettleAuctionBlock_transferFrom evm evmTransfer
    (payout := auctionSettleAuctionDefaultPayout) (tail := [])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_settleAuction_amount_positive_false_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      ExecBlock.nil) ExecBlock.nil

theorem auctionSettleAuctionBodyReturns_burnPayoutLowLevelSuccess
    (evm evmBurn evmPay : EVM.State) {out outPay : ByteArray}
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
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (true, evmPay, outPay) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body
      (.returned
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore evm).insert "_burn" .unit }
          "_pay" none)
        evmPay none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine auctionSettleAuctionBlock_burn evm evmBurn
    (payout := auctionSettleAuctionDefaultPayout) (tail := [])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
              evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                (ret := "_burn") .unit (by decide) (by decide))
          auctionLookupCallable_safeTransfer
          (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
            (auctionSettleAuctionAmount evm))
          (auctionSafeTransferBodyReturns_lowLevelSuccess evmBurn evmPay
            (auctionOwnerAddressAt evmBurn) (auctionSettleAuctionAmount evm) hpayCall))
        ExecBlock.nil))
    ExecBlock.nil

theorem auctionSettleAuctionBodyReturns_burnPayoutLowLevelFailureWethSuccess
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray} {transferOk : Bool}
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
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
      some [.bool transferOk]) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body
      (.returned
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore evm).insert "_burn" .unit }
          "_pay" none)
        evmTransfer none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine auctionSettleAuctionBlock_burn evm evmBurn
    (payout := auctionSettleAuctionDefaultPayout) (tail := [])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
              evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                (ret := "_burn") .unit (by decide) (by decide))
          auctionLookupCallable_safeTransfer
          (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
            (auctionSettleAuctionAmount evm))
          (auctionSafeTransferBodyReturns_lowLevelFailureWethSuccess evmBurn evmPay
            evmDeposit evmTransfer (auctionOwnerAddressAt evmBurn)
            (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer
            htransferDec))
        ExecBlock.nil))
    ExecBlock.nil

theorem auctionSettleAuctionBodyReturns_transferFromPayoutLowLevelSuccess
    (evm evmTransfer evmPay : EVM.State) {out outPay : ByteArray}
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
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (true, evmPay, outPay) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body
      (.returned
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore evm).insert "_tf" .unit }
          "_pay" none)
        evmPay none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine auctionSettleAuctionBlock_transferFrom evm evmTransfer
    (payout := auctionSettleAuctionDefaultPayout) (tail := [])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
              evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                (ret := "_tf") .unit (by decide) (by decide))
          auctionLookupCallable_safeTransfer
          (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
            (auctionSettleAuctionAmount evm))
          (auctionSafeTransferBodyReturns_lowLevelSuccess evmTransfer evmPay
            (auctionOwnerAddressAt evmTransfer) (auctionSettleAuctionAmount evm) hpayCall))
        ExecBlock.nil))
    ExecBlock.nil

theorem auctionSettleAuctionBodyReturns_transferFromPayoutLowLevelFailureWethSuccess
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray} {transferOk : Bool}
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
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (true, evmWethTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
      some [.bool transferOk]) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body
      (.returned
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore evm).insert "_tf" .unit }
          "_pay" none)
        evmWethTransfer none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine auctionSettleAuctionBlock_transferFrom evm evmTransfer
    (payout := auctionSettleAuctionDefaultPayout) (tail := [])
    hstart hsettled htime hbidder hnounsCode hcall ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
              evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                (ret := "_tf") .unit (by decide) (by decide))
          auctionLookupCallable_safeTransfer
          (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
            (auctionSettleAuctionAmount evm))
          (auctionSafeTransferBodyReturns_lowLevelFailureWethSuccess evmTransfer evmPay
            evmDeposit evmWethTransfer (auctionOwnerAddressAt evmTransfer)
            (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer
            htransferDec))
        ExecBlock.nil))
    ExecBlock.nil

end Auction

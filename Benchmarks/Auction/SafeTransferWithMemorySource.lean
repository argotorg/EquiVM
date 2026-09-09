import Benchmarks.Auction.MemoryAllocationSource
import Benchmarks.Auction.SettleAuctionTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionSafeTransferBlock_afterETHFailure
    (evm evmCall : EVM.State) (recipient : AccountAddress) (amount : UInt256)
    {out : ByteArray} {onETHSuccess transfer : List Stmt} {result : ExecResult}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hbranch : ExecBlock auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall
      (checkedExternalCallStmts (.storage wethRef) "deposit" (.var "amount") [] "_dep" ++ transfer)
      result) :
    ExecBlock auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm (safeTransferETHWithFallbackBody onETHSuccess transfer) result := by
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount) hcall) ?_
  have hite := ExecStmt.iteTrue (elseB := onETHSuccess)
    (evalExpr_safeTransfer_not_success_true evmCall recipient amount out) hbranch
  cases result with
  | ok frame evm' => exact ExecBlock.consNormal hite ExecBlock.nil
  | returned frame evm' value => exact ExecBlock.consReturn hite
  | reverted => exact ExecBlock.consRevert hite
  | «break» frame evm' => exact ExecBlock.consBreak hite
  | «continue» frame evm' => exact ExecBlock.consContinue hite

theorem auctionSafeTransferWithMemoryReturns_lowLevelSuccess
    (evm evmCall : EVM.State) (recipient : AccountAddress) (amount : UInt256) {out : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (true, evmCall, out)) (hsize : out.size + 63 < UInt256.size) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount } evm
      safeTransferETHWithMemory.body
      (.returned
        { contract := auctionContract,
          locals := ((auctionSafeTransferStore recipient amount).insert "success" (.bool true)).insert
            "_data" (.bytes out) }
        evmCall (some [.int (Int.ofNat (auctionPayoutFreeNat out.size))])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount) hcall) ?_
  refine ExecBlock.consReturn
    (ExecStmt.iteFalse (evalExpr_safeTransfer_not_success_false evmCall recipient amount out) ?_)
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton
    (evalExpr_payoutFreePtrAfterETH (by simp) hsize)))

theorem auctionSafeTransferBlockAfterDeposit
    (evm evmCall evmDeposit : EVM.State) (recipient : AccountAddress) (amount : UInt256)
    {out outDeposit : ByteArray} {onETHSuccess transfer : List Stmt} {result : ExecResult}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool true))
    (hdeposit : typedCallViaEVM auctionConfig evmCall
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat amount.toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : ExecBlock auctionConfig
      { contract := auctionContract,
        locals := (auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit }
      evmDeposit transfer result) :
    ExecBlock auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm (safeTransferETHWithFallbackBody onETHSuccess transfer) result := by
  refine auctionSafeTransferBlock_afterETHFailure evm evmCall recipient amount hcall ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hcode)
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess (args := [])
          (evalExpr_safeTransfer_weth evmCall
            (auctionSafeTransferFailureStore recipient amount out)
            (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
          (evalExpr_safeTransfer_amount_after_failure evmCall recipient amount out)
          (by rfl) hdeposit (auctionExternalABI_decode_deposit outDeposit)) htransfer)

theorem auctionSafeTransferWithMemoryReverts_noWethCode
    (evm evmCall : EVM.State) (recipient : AccountAddress) (amount : UInt256) {out : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool false)) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithMemory.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine auctionSafeTransferBlock_afterETHFailure evm evmCall recipient amount hcall ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hcode)

theorem auctionSafeTransferWithMemoryReverts_depositFailure
    (evm evmCall evmDeposit : EVM.State) (recipient : AccountAddress) (amount : UInt256)
    {out outDeposit : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool true))
    (hdeposit : typedCallViaEVM auctionConfig evmCall
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat amount.toNat) []
      (false, evmDeposit, outDeposit) true) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithMemory.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine auctionSafeTransferBlock_afterETHFailure evm evmCall recipient amount hcall ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hcode) ?_
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure
    (evalExpr_safeTransfer_weth evmCall (auctionSafeTransferFailureStore recipient amount out)
      (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
    (evalExpr_safeTransfer_amount_after_failure evmCall recipient amount out) (by rfl) hdeposit)

def auctionSafeTransferWethMemoryStore (recipient : AccountAddress) (amount : UInt256)
    (out : ByteArray) (success : Bool) (outTransfer : ByteArray) : Store :=
  (((auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit).insert
    "_xferSuccess" (.bool success)).insert "_xferData" (.bytes outTransfer)

theorem auctionSafeTransferBlock_afterWethTransfer
    (evm evmCall evmDeposit evmTransfer : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit outTransfer : ByteArray}
    {success : Bool} {onETHSuccess tail : List Stmt} {result : ExecResult}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool true))
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
      (success, evmTransfer, outTransfer) true)
    (hrest : ExecBlock auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferWethMemoryStore recipient amount out success outTransfer }
      evmTransfer tail result) :
    ExecBlock auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm (safeTransferETHWithFallbackBody onETHSuccess
        (.lowLevelCall (.storage wethRef) (.intLit 0)
          (.abiEncodeCall "transfer" [.var "to", .var "amount"])
          "_xferSuccess" "_xferData" :: tail)) result := by
  refine auctionSafeTransferBlockAfterDeposit evm evmCall evmDeposit recipient amount
    hcall hcode hdeposit ?_
  obtain ⟨calldata, hencode, htransferCall⟩ := htransfer
  simp only [Int.ofNat_eq_natCast] at hencode
  have hcalldata : evalExpr? auctionConfig
      { contract := auctionContract,
        locals := (auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit }
      evmDeposit (.abiEncodeCall "transfer" [.var "to", .var "amount"]) =
        .ok (.bytes calldata) := by
    simp [evalExpr?, evalExprList?, auctionSafeTransferFailureStore, auctionSafeTransferStore,
      EvalResult.ofOption, Std.HashMap.getElem_insert, EvalResult.bind, bind, pure]
    rw [hencode]
  have htarget := evalExpr_safeTransfer_weth evmDeposit
    ((auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit)
    (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef])
  have hzero : evalExpr? auctionConfig
      { contract := auctionContract,
        locals := (auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit }
      evmDeposit (.intLit 0) = .ok (.int 0) := by simp only [evalExpr?, pure]
  cases success with
  | false =>
    exact ExecBlock.consNormal
      (ExecStmt.lowLevelCallFailure htarget hzero hcalldata htransferCall) hrest
  | true =>
    exact ExecBlock.consNormal
      (ExecStmt.lowLevelCallSuccess htarget hzero hcalldata htransferCall) hrest

theorem auctionSafeTransferWithMemoryReturns_wethSuccess
    (evm evmCall evmDeposit evmTransfer : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit outTransfer : ByteArray}
    {transferOk : Bool}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool true))
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
    (hdecode : auctionConfig.externalABI.decode? "transfer" outTransfer = some [.bool transferOk])
    (hsize : out.size + 63 < UInt256.size) (htransferSize : outTransfer.size + 31 < UInt256.size) :
    ∃ frame, ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithMemory.body
      (.returned frame evmTransfer (some [.int (Int.ofNat
        (auctionPayoutFreeNat out.size + auctionRoundedMemoryNat outTransfer.size))])) := by
  let frame : Frame :=
    { contract := auctionContract,
      locals := (auctionSafeTransferWethMemoryStore recipient amount out true outTransfer).insert
        "_xfer" (.bool transferOk) }
  refine ⟨frame, ExecFuncBody.execBlockRet ?_⟩
  refine auctionSafeTransferBlock_afterWethTransfer evm evmCall evmDeposit evmTransfer
    recipient amount hcall hcode hdeposit htransfer ?_
  dsimp only [auctionSafeTransferWethMemoryStore]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by
    simp [evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert])) ?_
  have hdecoded : ABI.decodeReturnValueWithMode? auctionConfig.abiDecodeMode boolTy outTransfer =
      some (.bool transferOk) := by
    simpa [auctionConfig, auctionExternalABI, isVoidExternal, decodeReturn?,
      ABI.decodeReturnValueWithMode?] using hdecode
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bool transferOk) (by
    simp [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, hdecoded, pure])) ?_
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (evalExpr_add_nat
    (evalExpr_payoutFreePtrAfterETH (by
      simp [auctionSafeTransferFailureStore, Std.HashMap.getElem_insert]) hsize)
    (evalExpr_roundedMemoryAllocation (evalExpr_localBytesLength (by
      simp [Std.HashMap.getElem_insert])) htransferSize))))

theorem auctionSafeTransferWithMemoryReverts_transferFailure
    (evm evmCall evmDeposit evmTransfer : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit outTransfer : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool true))
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
      (false, evmTransfer, outTransfer) true) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithMemory.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine auctionSafeTransferBlock_afterWethTransfer evm evmCall evmDeposit evmTransfer
    recipient amount hcall hcode hdeposit htransfer ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    simp [auctionSafeTransferWethMemoryStore, evalExpr?, EvalResult.ofOption,
      Std.HashMap.getElem_insert]))

theorem auctionSafeTransferWithMemoryReverts_transferDecodeFailure
    (evm evmCall evmDeposit evmTransfer : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit outTransfer : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
      evmCall (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool true))
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
    (hdecode : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithMemory.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine auctionSafeTransferBlock_afterWethTransfer evm evmCall evmDeposit evmTransfer
    recipient amount hcall hcode hdeposit htransfer ?_
  dsimp only [auctionSafeTransferWethMemoryStore]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by
    simp [evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert])) ?_
  have hdecoded : ABI.decodeReturnValueWithMode? auctionConfig.abiDecodeMode boolTy outTransfer =
      none := by
    simpa [auctionConfig, auctionExternalABI, decodeReturn?, ABI.decodeReturnValueWithMode?]
      using hdecode
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert (by
    simp [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, hdecoded]))

end Auction

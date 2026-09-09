import Benchmarks.Auction.SettleAuctionTransferReturnBase

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 1000000
namespace Auction

theorem auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
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
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (false, evmTransfer, outTransfer) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
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
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_burn out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                  (ret := "_burn") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferFailure
              evmBurn evmPay evmDeposit evmTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer))))

theorem auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (false, evmTransfer, outTransfer) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferFailure
        (auctionSettleAuctionEnterState evm) evmBurn evmPay evmDeposit evmTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer))

theorem auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
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
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
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
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_burn out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                  (ret := "_burn") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferDecodeFailure
              evmBurn evmPay evmDeposit evmTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer
              htransferDec))))

theorem auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
        (auctionSettleAuctionEnterState evm) evmBurn evmPay evmDeposit evmTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer htransferDec))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethNoCode
    (evm evmTransfer evmPay : EVM.State) {out outPay : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
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
      (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
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
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethNoCode evmTransfer evmPay
              (auctionOwnerAddressAt evmTransfer) (auctionSettleAuctionAmount evm)
              hpayCall hwethCode))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethNoCode
    (evm evmTransfer evmPay : EVM.State) {out outPay : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethNoCode
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethDepositFailure
    (evm evmTransfer evmPay evmDeposit : EVM.State) {out outPay outDeposit : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
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
      (false, evmDeposit, outDeposit) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
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
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethDepositFailure evmTransfer evmPay
              evmDeposit (auctionOwnerAddressAt evmTransfer) (auctionSettleAuctionAmount evm)
              hpayCall hwethCode hdeposit))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethDepositFailure
    (evm evmTransfer evmPay evmDeposit : EVM.State) {out outPay outDeposit : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (false, evmDeposit, outDeposit) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethDepositFailure
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay evmDeposit
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
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
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (false, evmWethTransfer, outTransfer) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
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
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferFailure
              evmTransfer evmPay evmDeposit evmWethTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (false, evmWethTransfer, outTransfer) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferFailure
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay evmDeposit evmWethTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
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
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (true, evmWethTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
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
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferDecodeFailure
              evmTransfer evmPay evmDeposit evmWethTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer
              htransferDec))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (true, evmWethTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay evmDeposit evmWethTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer htransferDec))

theorem auctionExternalABI_decode_transfer_false {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hsize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) :
    auctionConfig.externalABI.decode? "transfer" out = some [.bool false] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hzero : ABI.bytesToWord ((out.toList.drop 0).take 32) = ⟨0⟩ := by
    simpa [List.drop_zero, hwordList] using hword
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = some (.bool false, 0 + 32) := by
      simpa [decodeScalarWordWithMode?] using
        (decodeScalarWord_bool_ok_zero (bytes := out.toList) (start := 0) htake0 hzero)
    rw [hscalar]
    rfl
  · simpa using hsmall

theorem auctionExternalABI_decode_transfer_true {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hsize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨1⟩) :
    auctionConfig.externalABI.decode? "transfer" out = some [.bool true] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hone : ABI.bytesToWord ((out.toList.drop 0).take 32) = ⟨1⟩ := by
    simpa [List.drop_zero, hwordList] using hword
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = some (.bool true, 0 + 32) := by
      simpa [decodeScalarWordWithMode?] using
        (decodeScalarWord_bool_ok_one (bytes := out.toList) (start := 0) htake0 hone)
    rw [hscalar]
    rfl
  · simpa using hsmall

theorem auctionExternalABI_decode_transfer_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    auctionConfig.externalABI.decode? "transfer" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = none := by
      rw [← decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.modern)
        (ty := ABIType.elem ElemType.bool) (bytes := out.toList) (start := 0) (by decide)]
      simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
      rw [if_neg htake0]
    rw [hscalar]
    rfl
  · simpa using hsmall

theorem auctionExternalABI_decode_transfer_none_huge {out : ByteArray}
    (hhuge : (2 : Nat) ^ 255 ≤ out.size) :
    auctionConfig.externalABI.decode? "transfer" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhuge⟩)]

theorem auctionExternalABI_decode_transfer_none_noncanon {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hsize : out.size < 2 ^ 255)
    (hnz : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (hno : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨1⟩) :
    auctionConfig.externalABI.decode? "transfer" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hnzList : ABI.bytesToWord ((out.toList.drop 0).take 32) ≠ ⟨0⟩ := by
    intro h
    exact hnz (by simpa [List.drop_zero, hwordList] using h)
  have hnoList : ABI.bytesToWord ((out.toList.drop 0).take 32) ≠ ⟨1⟩ := by
    intro h
    exact hno (by simpa [List.drop_zero, hwordList] using h)
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = none := by
      rw [← decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.modern)
        (ty := ABIType.elem ElemType.bool) (bytes := out.toList) (start := 0) (by decide)]
      simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
      rw [if_pos htake0]
      have hnzNat : ¬ (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat = 0 := by
        intro h
        exact hnzList (uint256_toNat_eq_zero h)
      have hnoNat : ¬ (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat = 1 := by
        intro h
        apply hnoList
        apply u256_inj
        simpa [UInt256.toNat] using h
      dsimp only [Option.bind]
      rw [if_neg (by simpa [UInt256.toNat] using hnzNat),
        if_neg (by simpa [UInt256.toNat] using hnoNat)]
    rw [hscalar]
    rfl
  · simpa using hsmall

end Auction

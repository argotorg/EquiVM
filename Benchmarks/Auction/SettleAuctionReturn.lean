import Benchmarks.Auction.SettleAuctionTransitions

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionTransferSuccessReturnRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evm evmBurn evmPay evmDeposit evmTransfer : EVM.State}
    {out outPay outDeposit outTransfer : ByteArray} {transferOk : Bool}
    {cATransfer : Batteries.RBSet AccountAddress compare} {σTransfer : AccountMap}
    (hcode : I.code = auctionBytecode)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hevm : evm = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
    (hret :
      RDret auctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cATransfer, auctionSettleAuctionExitMap σTransfer I) ByteArray.empty)
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
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
      some [.bool transferOk])
    (hcreated : cATransfer = (auctionSettleAuctionExitState evmTransfer).createdAccounts)
    (htransferOwner : evmTransfer.executionEnv.codeOwner = I.codeOwner)
    (hpostTransferAccounts : accountMapEquiv σTransfer evmTransfer.accountMap) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hbodyEvm :
      ExecTransitionBody auctionConfig auctionContract evm ∅
        settleAuctionTransition.body
        (.returned
          (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
          (auctionSettleAuctionExitState evmTransfer) none) :=
    auctionSettleAuctionTransitionReturns_burnPayoutLowLevelFailureWethSuccess
      evm evmBurn evmPay evmDeposit evmTransfer
      hwv hpaused hstatus hstart hsettled htime hbidder hnounsCode hcall hamount hpayCall
      hwethCode hdeposit htransfer htransferDec
  have hbody :
      ExecTransitionBody auctionConfig auctionContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        settleAuctionTransition.body
        (.returned
          (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
          (auctionSettleAuctionExitState evmTransfer) none) := by
    simpa [hevm] using hbodyEvm
  have hpostAccounts :
      accountMapEquiv (auctionSettleAuctionExitMap σTransfer I)
        (auctionSettleAuctionExitState evmTransfer).accountMap := by
    have hstore :=
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hpostTransferAccounts
    simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
      storageStore_accountMap, htransferOwner] using hstore
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody hcreated
    hpostAccounts (returnEquiv.fallthrough rfl rfl (by native_decide))

theorem auctionSettleAuctionTransferFromSuccessReturnRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evm evmTransferFrom evmPay evmDeposit evmTransfer : EVM.State}
    {out outPay outDeposit outTransfer : ByteArray} {transferOk : Bool}
    {cATransfer : Batteries.RBSet AccountAddress compare} {σTransfer : AccountMap}
    (hcode : I.code = auctionBytecode)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hevm : evm = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
    (hret :
      RDret auctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cATransfer, auctionSettleAuctionExitMap σTransfer I) ByteArray.empty)
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
      (true, evmTransferFrom, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransferFrom
      (EVM.address (auctionOwnerAddressAt evmTransferFrom))
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
      [.address (auctionOwnerAddressAt evmTransferFrom),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
      some [.bool transferOk])
    (hcreated : cATransfer = (auctionSettleAuctionExitState evmTransfer).createdAccounts)
    (htransferOwner : evmTransfer.executionEnv.codeOwner = I.codeOwner)
    (hpostTransferAccounts : accountMapEquiv σTransfer evmTransfer.accountMap) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hbodyEvm :
      ExecTransitionBody auctionConfig auctionContract evm ∅
        settleAuctionTransition.body
        (.returned
          (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
          (auctionSettleAuctionExitState evmTransfer) none) :=
    auctionSettleAuctionTransitionReturns_transferFromPayoutLowLevelFailureWethSuccess
      evm evmTransferFrom evmPay evmDeposit evmTransfer
      hwv hpaused hstatus hstart hsettled htime hbidder hnounsCode hcall hamount hpayCall
      hwethCode hdeposit htransfer htransferDec
  have hbody :
      ExecTransitionBody auctionConfig auctionContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        settleAuctionTransition.body
        (.returned
          (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
          (auctionSettleAuctionExitState evmTransfer) none) := by
    simpa [hevm] using hbodyEvm
  have hpostAccounts :
      accountMapEquiv (auctionSettleAuctionExitMap σTransfer I)
        (auctionSettleAuctionExitState evmTransfer).accountMap := by
    have hstore :=
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hpostTransferAccounts
    simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
      storageStore_accountMap, htransferOwner] using hstore
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody hcreated
    hpostAccounts (returnEquiv.fallthrough rfl rfl (by native_decide))

end Auction

import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyFromCallCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutFailureEmptyFromCallTransferCallCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmS evmTf evmPay evmDeposit evmDepositE : EVM.State}
    {outTf outPay outDeposit outTransferIn : ByteArray}
    {cADep : Batteries.RBSet AccountAddress compare}
    {noun amount start finish bidder settled caller owner wethTransfer : UInt256}
    {gasTransfer : UInt256} {kTransferCall CTransferCall : ℕ}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hevmS : evmS = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
    (hwvS : evmS.executionEnv.weiValue = ⟨0⟩)
    (hpausedSolm :
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatusSolm : Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstartSolm : Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettledSolm :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htimeSolmLe :
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat)
    (hbidderSolm :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCodeSolmEval :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evmS) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evmS))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcallSolm :
      typedCallViaEVM auctionConfig
        (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evmS))
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evmS)
              (auctionSettleAuctionEnterState evmS).executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "transferFrom" 0
        [.address (auctionSettleAuctionEnterState evmS).executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evmS)
                (auctionSettleAuctionEnterState evmS).executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evmS)
              (auctionSettleAuctionEnterState evmS).executionEnv.codeOwner ⟨207⟩).toNat)]
        (true, evmTf, outTf) true)
    (hamountSolm : 0 < (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)
    (hdepth : I.depth.val < 1024)
    (hpaySolm :
      callViaEVM evmTf (EVM.address (auctionOwnerAddressAt evmTf))
        (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)
        ByteArray.empty (false, evmPay, outPay) true)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (hwethCodeSolmTransfer :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdepositOwner : evmDeposit.executionEnv.codeOwner = I.codeOwner)
    (hdepEEnv : evmDepositE.executionEnv = I)
    (hdepECreated : evmDepositE.createdAccounts = cADep)
    (hdepEGenesis :
      evmDepositE.genesisBlockHeader =
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
    (hdepEBlocks :
      evmDepositE.blocks =
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks)
    (hdepESigma0 :
      evmDepositE.σ₀ =
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀)
    (hdepEDepth : evmDepositE.executionEnv.depth ≠ 1024)
    (hdepAccounts : accountMapEquiv evmDepositE.accountMap evmDeposit.accountMap)
    (hdepSigma0 : evmDepositE.σ₀ = evmDeposit.σ₀)
    (hdepCreated : evmDeposit.createdAccounts = evmDepositE.createdAccounts)
    (hdepGenesis : evmDeposit.genesisBlockHeader = evmDepositE.genesisBlockHeader)
    (hdepBlocks : evmDeposit.blocks = evmDepositE.blocks)
    (hdepEnv : evmDeposit.executionEnv = evmDepositE.executionEnv)
    (htransferEncode :
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller
      let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      auctionConfig.externalABI.encode? "transfer"
        [.address (auctionOwnerAddressAt evmTf),
          .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)] =
        some (memTransfer.readWithPadding freePtr.toNat 68))
    (hwethTargetTransfer :
      EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat)) =
        AccountAddress.ofUInt256 wethTransfer)
    (hrdTransferCall :
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller
      let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3517⟩
        [gasTransfer, wethTransfer, ⟨0⟩, freePtr, ⟨68⟩, freePtr, ⟨32⟩,
          ⟨68⟩ + freePtr, ⟨2835717307⟩, wethTransfer, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memTransfer
        (auctionSettleAuctionDynTransferAwAfterMload64
          (auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)) freePtr)
        outTransferIn (cADep, evmDepositE.accountMap) kTransferCall CTransferCall) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder settled caller
  let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  obtain ⟨cATransfer, σTransfer, zTransfer, outTransfer, AInTransfer,
      callGasTransfer, kAfterTransfer, CAfterTransfer, hThetaTransferPack,
      hrdAfterTransferRaw, houtTransferSize⟩ :=
    RD.call
      (by simpa [memLoop, freePtr, memDeposit, memTransfer] using hrdTransferCall)
      (by native_decide) hdepth
      (by
        change 10 + 1 ≤ 1024
        native_decide)
  obtain ⟨gTransfer'', ATransfer, hThetaTransfer⟩ := hThetaTransferPack
  let evmTransferE :=
    { evmDepositE with
        accountMap := σTransfer,
        substate := ATransfer,
        createdAccounts := cATransfer }
  obtain ⟨σTransferSolm, ATransferSolm, htransferSolmRaw, hpostTransfer⟩ :=
    transferBranchCallTransport
      (evmE := evmDepositE) (evmS := evmDeposit)
      (cA' := cATransfer) (σ' := σTransfer)
      (AIn := AInTransfer) (A' := ATransfer)
      (z := zTransfer) (out := outTransfer)
      (calldata := memTransfer.readWithPadding freePtr.toNat (⟨68⟩ : UInt256).toNat)
      (g'' := gTransfer'') (callGas := callGasTransfer)
      (valueWord := ⟨0⟩) (targetWord := wethTransfer)
      (by
        simpa [evmTransferE, memTransfer, freePtr, _hperm, hdepEEnv, hdepECreated,
          hdepEGenesis, hdepEBlocks, hdepESigma0] using hThetaTransfer)
      (by
        show (⟨0⟩ : UInt256) ≤
          (evmDepositE.accountMap.find?
              evmDepositE.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
        exact Fin.zero_le _)
      hdepEDepth
      hdepAccounts hdepSigma0 hdepCreated hdepGenesis hdepBlocks hdepEnv
  let evmTransfer :=
    { evmDeposit with
      accountMap := σTransferSolm,
      substate := ATransferSolm,
      createdAccounts := cATransfer }
  have htransferRaw :
      callViaEVM evmDeposit (AccountAddress.ofUInt256 wethTransfer) 0
        (memTransfer.readWithPadding freePtr.toNat (⟨68⟩ : UInt256).toNat)
        (zTransfer, evmTransfer, outTransfer) true := by
    simpa [evmTransfer] using htransferSolmRaw
  have htransfer :
      typedCallViaEVM auctionConfig evmDeposit
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "transfer" 0
        [.address (auctionOwnerAddressAt evmTf),
          .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)]
        (zTransfer, evmTransfer, outTransfer) true := by
    refine ⟨memTransfer.readWithPadding freePtr.toNat 68, ?_, ?_⟩
    · simpa [memLoop, freePtr, memDeposit, memTransfer] using htransferEncode
    · rw [hwethTargetTransfer]
      simpa [memTransfer] using htransferRaw
  cases zTransfer
  · have htransferFalse :
        typedCallViaEVM auctionConfig evmDeposit
          (EVM.address (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))) "transfer" 0
          [.address (auctionOwnerAddressAt evmTf),
            .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)]
          (false, evmTransfer, outTransfer) true := by
      simpa using htransfer
    exact transferBranchPayoutFailureEmptyFromCallTransferFailureCase
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (evmS := evmS) (evmTf := evmTf) (evmPay := evmPay)
      (evmDeposit := evmDeposit) (evmTransfer := evmTransfer)
      (outTf := outTf) (outPay := outPay) (outDeposit := outDeposit)
      (outTransfer := outTransfer) (cATransfer := cATransfer)
      (σTransfer := σTransfer)
      (noun := noun) (amount := amount) (start := start) (finish := finish)
      (bidder := bidder) (settled := settled) (caller := caller) (owner := owner)
      (weth := wethTransfer) (kAfterTransfer := kAfterTransfer)
      (CAfterTransfer := CAfterTransfer)
      _hcode _hperm hdispatch hdecode hevmS hwvS hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsCodeSolmEval
      hcallSolm hamountSolm hpaySolm hwethCodeSolmTransfer hdeposit
      htransferFalse houtTransferSize
      (by
        have hpc : (⟨3517⟩ : UInt256) + ⟨1⟩ = ⟨3518⟩ := by
          native_decide
        have hlen68 : ((⟨68⟩ : UInt256).toNat) = 68 := by
          native_decide
        have hlen32 : ((⟨32⟩ : UInt256).toNat) = 32 := by
          native_decide
        have hawReturnEq :=
          transferBranchTransferFromPayoutLoopDynTransferReturnAwAfterCallEqAw14
            noun amount start finish bidder settled caller
        simpa only [memLoop, freePtr, memDeposit, memTransfer,
          hpc, hlen68, hlen32, if_true, hawReturnEq] using hrdAfterTransferRaw)
  · have htransferTrue :
        typedCallViaEVM auctionConfig evmDeposit
          (EVM.address (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))) "transfer" 0
          [.address (auctionOwnerAddressAt evmTf),
            .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)]
          (true, evmTransfer, outTransfer) true := by
      simpa using htransfer
    exact transferBranchPayoutFailureEmptyFromCallTransferReturnCase
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (evmS := evmS) (evmTf := evmTf) (evmPay := evmPay)
      (evmDeposit := evmDeposit) (evmTransfer := evmTransfer)
      (outTf := outTf) (outPay := outPay) (outDeposit := outDeposit)
      (outTransfer := outTransfer) (cATransfer := cATransfer)
      (σTransfer := σTransfer)
      (noun := noun) (amount := amount) (start := start) (finish := finish)
      (bidder := bidder) (settled := settled) (caller := caller) (owner := owner)
      (weth := wethTransfer) (kAfterTransfer := kAfterTransfer)
      (CAfterTransfer := CAfterTransfer)
      _hcode _hperm hdispatch hdecode hevmS hwvS hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsCodeSolmEval
      hcallSolm hamountSolm hpaySolm hwethCodeSolmTransfer hdeposit
      htransferTrue
      (by
        simp [auctionSettleAuctionExitState, evmTransfer,
          storageStore_createdAccounts])
      (by
        simp [evmTransfer, hdepositOwner])
      (by simpa [evmTransferE, evmTransfer] using hpostTransfer)
      houtTransferSize
      (by
        have hpc : (⟨3517⟩ : UInt256) + ⟨1⟩ = ⟨3518⟩ := by
          native_decide
        have hlen68 : ((⟨68⟩ : UInt256).toNat) = 68 := by
          native_decide
        have hlen32 : ((⟨32⟩ : UInt256).toNat) = 32 := by
          native_decide
        have hawReturnEq :=
          transferBranchTransferFromPayoutLoopDynTransferReturnAwAfterCallEqAw14
            noun amount start finish bidder settled caller
        simpa only [memLoop, freePtr, memDeposit, memTransfer,
          hpc, hlen68, hlen32, if_true, hawReturnEq] using hrdAfterTransferRaw)


end Auction

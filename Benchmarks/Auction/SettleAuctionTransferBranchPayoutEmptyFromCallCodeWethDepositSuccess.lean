import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyFromCallCodeWethTransfer

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutFailureEmptyFromCallDepositMadeSuccessCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmS evmTf evmPay evmDeposit evmDepositE : EVM.State}
    {outTf outPay outDeposit : ByteArray}
    {cADep : Batteries.RBSet AccountAddress compare}
    {noun amount start finish bidder settled caller owner wethBefore : UInt256}
    {kAfterDep CAfterDep : ℕ}
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
        AccountAddress.ofUInt256
          (UInt256.land (auctionSlotWord ⟨202⟩ evmDepositE.accountMap I) solcAddrMask))
    (hrdAfterDep :
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller
      let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3432⟩
        [⟨1⟩, ⟨4⟩ + freePtr, amount, ⟨3504541104⟩,
          wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memDeposit (auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14))
        outDeposit (cADep, evmDepositE.accountMap) kAfterDep CAfterDep) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  obtain ⟨gasTransfer, kTransferCall, CTransferCall, hrdTransferCall⟩ :=
    transferBranchPayoutFailureEmptyFromCallDepositSuccessToTransferCall
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (cADep := cADep) (σDep := evmDepositE.accountMap)
      (noun := noun) (amount := amount) (start := start) (finish := finish)
      (bidder := bidder) (settled := settled) (caller := caller) (owner := owner)
      (wethBefore := wethBefore) (outDep := outDeposit)
      (kAfterDep := kAfterDep) (CAfterDep := CAfterDep) hrdAfterDep
  exact transferBranchPayoutFailureEmptyFromCallTransferCallCase
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmS := evmS) (evmTf := evmTf) (evmPay := evmPay)
    (evmDeposit := evmDeposit) (evmDepositE := evmDepositE)
    (outTf := outTf) (outPay := outPay) (outDeposit := outDeposit)
    (outTransferIn := outDeposit) (cADep := cADep)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) (caller := caller) (owner := owner)
    (wethTransfer := UInt256.land (auctionSlotWord ⟨202⟩ evmDepositE.accountMap I) solcAddrMask)
    (gasTransfer := gasTransfer)
    (kTransferCall := kTransferCall) (CTransferCall := CTransferCall)
    _hcode _hperm hdispatch hdecode hevmS hwvS hpausedSolm hstatusSolm
    hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsCodeSolmEval
    hcallSolm hamountSolm hdepth hpaySolm hdeposit hwethCodeSolmTransfer
    hdepositOwner hdepEEnv hdepECreated hdepEGenesis hdepEBlocks hdepESigma0
    hdepEDepth hdepAccounts hdepSigma0 hdepCreated hdepGenesis hdepBlocks hdepEnv
    htransferEncode hwethTargetTransfer hrdTransferCall

end Auction

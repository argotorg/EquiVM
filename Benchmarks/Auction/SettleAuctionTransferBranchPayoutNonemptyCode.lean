import Benchmarks.Auction.SettleAuctionTransferBranchPayoutNonempty

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutFailureNonemptyTransferReturnCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmS evmTf evmPay evmDeposit evmTransfer : EVM.State}
    {outTf outPay outDeposit outTransfer : ByteArray}
    {cATransfer : Batteries.RBSet AccountAddress compare} {σTransfer : AccountMap}
    {noun amount start finish bidder settled caller owner weth : UInt256}
    {kAfterTransfer CAfterTransfer : ℕ}
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
    (hpaySolm :
      callViaEVM evmTf (EVM.address (auctionOwnerAddressAt evmTf))
        (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)
        ByteArray.empty (false, evmPay, outPay) true)
    (hwethCodeSolmTransfer :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransferTrue : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTf),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)]
      (true, evmTransfer, outTransfer) true)
    (hcreated : cATransfer = (auctionSettleAuctionExitState evmTransfer).createdAccounts)
    (htransferOwner : evmTransfer.executionEnv.codeOwner = I.codeOwner)
    (hpostTransferAccounts : accountMapEquiv σTransfer evmTransfer.accountMap)
    (houtPaySmall : outPay.size < 2 ^ 138)
    (houtZero : outPay.size ≠ 0)
    (houtTransferSize : outTransfer.size < UInt256.size)
    (hrdAfterTransfer :
      let memCopy :=
        auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
      let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
      let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
      let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
      let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3518⟩
        [⟨1⟩, (⟨68⟩ : UInt256) + freePtr, ⟨2835717307⟩, weth, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer (cATransfer, σTransfer) kAfterTransfer CAfterTransfer) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let transferRetWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
  by_cases hshortTransfer : outTransfer.size < 32
  · have htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none :=
      auctionExternalABI_decode_transfer_none_short hshortTransfer
    have hrdTransferDecodeRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      exact
        auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnShortRevertDyn
          noun amount start finish bidder settled caller owner weth
          houtPaySmall houtZero hshortTransfer houtTransferSize hrdAfterTransfer
    have hbody :
        ExecTransitionBody auctionConfig auctionContract evmS ∅
          settleAuctionTransition.body .reverted :=
      auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
        evmS evmTf evmPay evmDeposit evmTransfer
        hwvS hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval hcallSolm hamountSolm hpaySolm
        hwethCodeSolmTransfer hdeposit htransferTrue htransferDec
    exact hrdTransferDecodeRev.reEquivExecutionRevert _hcode hdispatch hdecode
      (by simpa [hevmS] using hbody)
  · have houtTransfer32 : 32 ≤ outTransfer.size := by
      omega
    by_cases hhugeTransfer : (2 : Nat) ^ 255 ≤ outTransfer.size
    · have htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none :=
        auctionExternalABI_decode_transfer_none_huge hhugeTransfer
      have hrdTransferDecodeRev :
          RDrev auctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
        exact
          auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnHugeRevertDyn
            noun amount start finish bidder settled caller owner weth
            houtPaySmall houtZero hhugeTransfer houtTransferSize hrdAfterTransfer
      have hbody :
          ExecTransitionBody auctionConfig auctionContract evmS ∅
            settleAuctionTransition.body .reverted :=
        auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
          evmS evmTf evmPay evmDeposit evmTransfer
          hwvS hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
          hbidderSolm hnounsCodeSolmEval hcallSolm hamountSolm hpaySolm
          hwethCodeSolmTransfer hdeposit htransferTrue htransferDec
      exact hrdTransferDecodeRev.reEquivExecutionRevert _hcode hdispatch hdecode
        (by simpa [hevmS] using hbody)
    · have houtTransferHi : outTransfer.size < (2 : Nat) ^ 255 :=
        Nat.lt_of_not_ge hhugeTransfer
      have hfinishReturn {transferOk : Bool}
          (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
            some [.bool transferOk])
          (hret :
            RDret auctionBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (cATransfer, auctionSettleAuctionExitMap σTransfer I) ByteArray.empty) := by
        exact
          auctionSettleAuctionTransferFromSuccessReturnRuntime
            (evm := evmS) (evmTransferFrom := evmTf) (evmPay := evmPay)
            (evmDeposit := evmDeposit) (evmTransfer := evmTransfer)
            (transferOk := transferOk)
            _hcode hdispatch hdecode hevmS hret hwvS hpausedSolm hstatusSolm
            hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsCodeSolmEval
            hcallSolm hamountSolm hpaySolm hwethCodeSolmTransfer hdeposit
            htransferTrue htransferDec hcreated htransferOwner hpostTransferAccounts
      by_cases htransferZero : transferRetWord = ⟨0⟩
      · have htransferDec :
            auctionConfig.externalABI.decode? "transfer" outTransfer = some [.bool false] :=
          auctionExternalABI_decode_transfer_false houtTransfer32 houtTransferHi htransferZero
        obtain ⟨_, _, _, _, hrdEvent⟩ :=
          auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnBoolToEventDyn
            noun amount start finish bidder settled caller owner weth
            houtPaySmall houtZero houtTransfer32 houtTransferHi houtTransferSize
            (by
              simpa [transferRetWord] using
                (Or.inl htransferZero : transferRetWord = ⟨0⟩ ∨ transferRetWord = ⟨1⟩))
            hrdAfterTransfer
        have hret :
            RDret auctionBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (cATransfer, auctionSettleAuctionExitMap σTransfer I) ByteArray.empty :=
          auctionSettleAuctionEventToReturn _hperm hrdEvent
        exact hfinishReturn htransferDec hret
      · by_cases htransferOne : transferRetWord = ⟨1⟩
        · have htransferDec :
              auctionConfig.externalABI.decode? "transfer" outTransfer = some [.bool true] :=
            auctionExternalABI_decode_transfer_true houtTransfer32 houtTransferHi htransferOne
          obtain ⟨_, _, _, _, hrdEvent⟩ :=
            auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnBoolToEventDyn
              noun amount start finish bidder settled caller owner weth
              houtPaySmall houtZero houtTransfer32 houtTransferHi houtTransferSize
              (by
                simpa [transferRetWord] using
                  (Or.inr htransferOne : transferRetWord = ⟨0⟩ ∨ transferRetWord = ⟨1⟩))
              hrdAfterTransfer
          have hret :
              RDret auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (cATransfer, auctionSettleAuctionExitMap σTransfer I) ByteArray.empty :=
            auctionSettleAuctionEventToReturn _hperm hrdEvent
          exact hfinishReturn htransferDec hret
        · have htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none :=
            auctionExternalABI_decode_transfer_none_noncanon houtTransfer32 houtTransferHi
              htransferZero htransferOne
          have hrdTransferDecodeRev :
              RDrev auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
            exact
              auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnNoncanonRevertDyn
                noun amount start finish bidder settled caller owner weth
                houtPaySmall houtZero houtTransfer32 houtTransferHi houtTransferSize
                (by simpa [transferRetWord] using htransferZero)
                (by simpa [transferRetWord] using htransferOne)
                hrdAfterTransfer
          have hbody :
              ExecTransitionBody auctionConfig auctionContract evmS ∅
                settleAuctionTransition.body .reverted :=
            auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
              evmS evmTf evmPay evmDeposit evmTransfer
              hwvS hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
              hbidderSolm hnounsCodeSolmEval hcallSolm hamountSolm hpaySolm
              hwethCodeSolmTransfer hdeposit htransferTrue htransferDec
          exact hrdTransferDecodeRev.reEquivExecutionRevert _hcode hdispatch hdecode
            (by simpa [hevmS] using hbody)

theorem transferBranchPayoutFailureNonemptyWethNoCodeCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm : AccountMap}
    {A' A'_solm APay APaySolm : Substate}
    {o outPay : ByteArray} {kPay CPay : ℕ}
    (_hcode : I.code = auctionBytecode)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hwv : I.weiValue = ⟨0⟩)
    (hpausedSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩)
    (hstatusSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstartSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettledSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htimeSolmLe :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat)
    (hbidderSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCodeSolmEval :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evmS) }
          (auctionSettleAuctionMarkSettledState
            (auctionSettleAuctionEnterState evmS))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
        .ok (.bool true))
    (hcallSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      let evmTf :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (true, evmTf, o) true)
    (hamountSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      0 < (auctionSettleAuctionAmount evmEnter).toNat)
    (hpaySolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      let evmTf :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      let evmTfE :=
        { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ' } with
            substate := A',
            createdAccounts := cA' }
      let evmPayE :=
        { evmTfE with
            accountMap := σPay,
            substate := APay,
            createdAccounts := cAPay }
      let evmPay :=
        { evmTf with
          accountMap := σPaySolm,
          substate := APaySolm,
          createdAccounts := evmPayE.createdAccounts }
      callViaEVM evmTf (EVM.address (auctionOwnerAddressAt evmTf))
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
        ByteArray.empty (false, evmPay, outPay) true)
    (hpostPay : accountMapEquiv σPay σPaySolm)
    (houtPaySize : outPay.size < UInt256.size)
    (houtZero : outPay.size ≠ 0)
    (hrdAfterPayRaw :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let amountWord := auctionAuctionAmountWord σ1 I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4828⟩
        [⟨0⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩,
          amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord, ⟨4688⟩,
          ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        (auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord σ1 I)
          amountWord
          (auctionAuctionStartWord σ1 I)
          (auctionAuctionEndWord σ1 I)
          (auctionPackedBidderWord (auctionAuctionPackedWord σ1 I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ1 I))
          (UInt256.ofNat ↑I.codeOwner))
        (UInt256.ofNat 14) outPay (cAPay, σPay) kPay CPay)
    (hwethCodeZero :
      Reasoning.Theory.uniswapExtCodeSizeWord σPay
          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask) =
        ⟨0⟩) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  let evmTf :=
    { evmMark with
      accountMap := σ'_solm,
      substate := A'_solm,
      createdAccounts := cA' }
  let evmTfE :=
    { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ' } with
        substate := A',
        createdAccounts := cA' }
  let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
  let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  let evmPayE :=
    { evmTfE with
        accountMap := σPay,
        substate := APay,
        createdAccounts := cAPay }
  let evmPay :=
    { evmTf with
      accountMap := σPaySolm,
      substate := APaySolm,
      createdAccounts := evmPayE.createdAccounts }
  have htfOwner : evmTf.executionEnv.codeOwner = I.codeOwner := by
    simp [evmTf, evmMark, evmEnter, evmS,
      auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState,
      storageStore_executionEnv]
  obtain ⟨_, _, _, _, hrdFallback⟩ :=
    auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallback
      houtPaySize houtZero
      (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
  let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
  have hrdNoCodeRev :
      RDrev auctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    auctionSettleAuctionPayoutFallbackWethNoCodeRevertAnyMem
      hwethCodeZero hrdFallback
  have hpostPayAccounts :
      accountMapEquiv σPay σPaySolm := by
    simpa [evmPay] using hpostPay
  have hwethSlotPay :
      auctionSlotWord ⟨202⟩ σPay I =
        auctionSlotWord ⟨202⟩ σPaySolm I := by
    exact accountMapEquiv_storage_findD hpostPayAccounts
      I.codeOwner ⟨202⟩ ⟨0⟩
  have hwethWordPayEq :
      UInt256.land
          (Solm.EVM.storageLoad evmPay
            evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask =
        wethWord := by
    have hslot :
        Solm.EVM.storageLoad evmPay
            evmPay.executionEnv.codeOwner ⟨202⟩ =
          auctionSlotWord ⟨202⟩ σPaySolm I := by
      simp [evmPay, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, auctionSlotWord, htfOwner]
    unfold wethWord
    rw [hslot, ← hwethSlotPay]
  have hwethCodeSolm :
      (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0
          (fun acc => acc.code.size)))).toNat = 0 := by
    have hwethCodePay :
        (UInt256.ofNat
          ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
            0 (fun acc => acc.code.size))).toNat = 0 := by
      exact auctionUniswapExtCodeSizeWord_zero_lookup_code_zero
        (σ := σPay) (target := wethWord)
        (addr := AccountAddress.ofUInt256 wethWord) rfl
        (by simpa [wethWord] using hwethCodeZero)
    have hcodeEq :
        UInt256.ofNat
            ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
              0 (fun acc => acc.code.size)) =
          UInt256.ofNat
            ((σPaySolm.find?
              (AccountAddress.ofUInt256 wethWord)).option
              0 (fun acc => acc.code.size)) := by
      let wethAddr := AccountAddress.ofUInt256 wethWord
      have hpayOpt :
          UInt256.ofNat
              ((σPay.find? wethAddr).option 0
                (fun acc => acc.code.size)) =
            ((σPay.find? wethAddr).option (⟨0⟩ : UInt256)
              (fun acc => UInt256.ofNat acc.code.size)) := by
        cases σPay.find? wethAddr <;> rfl
      have hsolmOpt :
          UInt256.ofNat
              ((σPaySolm.find? wethAddr).option 0
                (fun acc => acc.code.size)) =
            ((σPaySolm.find? wethAddr).option (⟨0⟩ : UInt256)
              (fun acc => UInt256.ofNat acc.code.size)) := by
        cases σPaySolm.find? wethAddr <;> rfl
      rw [hpayOpt, hsolmOpt]
      exact accountMapEquiv_code_size_word hpostPayAccounts wethAddr
    have hcodeNatEq := congrArg UInt256.toNat hcodeEq
    have hcodeSolm :
        (UInt256.ofNat
          ((σPaySolm.find?
            (AccountAddress.ofUInt256 wethWord)).option
            0 (fun acc => acc.code.size))).toNat = 0 := by
      rw [← hcodeNatEq]
      exact hwethCodePay
    simpa [evmPay, State.lookupAccount, hwethWordPayEq,
      accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeSolm
  have hbody :
      ExecTransitionBody auctionConfig auctionContract evmS ∅
        settleAuctionTransition.body .reverted :=
    auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethNoCode
      evmS evmTf evmPay
      (by simpa [evmS, initState] using hwv) hpausedSolm
      hstatusSolm hstartSolm hsettledSolm htimeSolmLe
      hbidderSolm hnounsCodeSolmEval
      (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
      hamountSolm hpaySolm hwethCodeSolm
  exact hrdNoCodeRev.reEquivExecutionRevert _hcode hdispatch hdecode hbody

theorem transferBranchPayoutFailureNonemptyWethCodeCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm : AccountMap}
    {A' A'_solm APay APaySolm : Substate}
    {o outPay : ByteArray} {kPay CPay : ℕ}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hwv : I.weiValue = ⟨0⟩)
    (hpausedSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩)
    (hstatusSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstartSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettledSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htimeSolmLe :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat)
    (hbidderSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCodeSolmEval :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evmS) }
          (auctionSettleAuctionMarkSettledState
            (auctionSettleAuctionEnterState evmS))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
        .ok (.bool true))
    (hcallSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      let evmTf :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (true, evmTf, o) true)
    (hpostTf : accountMapEquiv σ' σ'_solm)
    (hamountEq :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      amountWord = auctionSettleAuctionAmount evmEnter)
    (hamountSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      0 < (auctionSettleAuctionAmount evmEnter).toNat)
    (hdepth : I.depth.val < 1024)
    (hpaySolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      let evmTf :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      let evmTfE :=
        { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ' } with
            substate := A',
            createdAccounts := cA' }
      let evmPayE :=
        { evmTfE with
            accountMap := σPay,
            substate := APay,
            createdAccounts := cAPay }
      let evmPay :=
        { evmTf with
          accountMap := σPaySolm,
          substate := APaySolm,
          createdAccounts := evmPayE.createdAccounts }
      callViaEVM evmTf (EVM.address (auctionOwnerAddressAt evmTf))
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
        ByteArray.empty (false, evmPay, outPay) true)
    (hpostPay : accountMapEquiv σPay σPaySolm)
    (houtPaySize : outPay.size < UInt256.size)
    (houtZero : outPay.size ≠ 0)
    (houtPaySmall : outPay.size < 2 ^ 138)
    (hrdAfterPayRaw :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let amountWord := auctionAuctionAmountWord σ1 I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4828⟩
        [⟨0⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩,
          amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord, ⟨4688⟩,
          ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        (auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord σ1 I)
          amountWord
          (auctionAuctionStartWord σ1 I)
          (auctionAuctionEndWord σ1 I)
          (auctionPackedBidderWord (auctionAuctionPackedWord σ1 I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ1 I))
          (UInt256.ofNat ↑I.codeOwner))
        (UInt256.ofNat 14) outPay (cAPay, σPay) kPay CPay)
    (hwethCodeE :
      Reasoning.Theory.uniswapExtCodeSizeWord σPay
          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask) ≠
        ⟨0⟩) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  let evmTf :=
    { evmMark with
      accountMap := σ'_solm,
      substate := A'_solm,
      createdAccounts := cA' }
  let evmTfE :=
    { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ' } with
        substate := A',
        createdAccounts := cA' }
  let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
  let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  let evmPayE :=
    { evmTfE with
        accountMap := σPay,
        substate := APay,
        createdAccounts := cAPay }
  let evmPay :=
    { evmTf with
      accountMap := σPaySolm,
      substate := APaySolm,
      createdAccounts := evmPayE.createdAccounts }
  have htfOwner : evmTf.executionEnv.codeOwner = I.codeOwner := by
    simp [evmTf, evmMark, evmEnter, evmS,
      auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState,
      storageStore_executionEnv]
  have hownerWordMasked :
      UInt256.land
          (UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask)
          solcAddrMask =
        UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask := by
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (auctionSlotWord ⟨151⟩ σ' I))
  have hownerLoad :
      auctionSlotWord ⟨151⟩ σ' I =
        Solm.EVM.storageLoad evmTf evmTf.executionEnv.codeOwner ⟨151⟩ := by
    have hslot := accountMapEquiv_storage_findD hpostTf I.codeOwner ⟨151⟩
      (⟨0⟩ : UInt256)
    rw [htfOwner]
    simpa [evmTf, auctionSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hslot
  have hownerEq :
      EVM.address (auctionOwnerAddressAt evmTf) = AccountAddress.ofUInt256 ownerWord := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    apply Fin.ext
    simp [auctionOwnerAddressAt, ownerWord, hownerLoad, EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt
      (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
          solcAddrMask_result_canonical
            (Solm.EVM.storageLoad evmTf evmTf.executionEnv.codeOwner ⟨151⟩))
  let callerWord := UInt256.ofNat ↑I.codeOwner
  obtain ⟨kFallbackDyn, CFallbackDyn, hrdFallbackDyn⟩ :=
    auctionSettleAuctionTransferFromPayoutCallFailureNonemptyReturnToFallbackFixed
      (noun :=
        auctionAuctionNounWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
      (amount := amountWord)
      (start :=
        auctionAuctionStartWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
      (finish :=
        auctionAuctionEndWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
      (bidder :=
        auctionPackedBidderWord
          (auctionAuctionPackedWord
            (auctionSettleAuctionEnterMap σ_evm I) I))
      (settled :=
        auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord
            (auctionSettleAuctionEnterMap σ_evm I) I))
      (caller := callerWord)
      (owner := ownerWord)
      houtPaySize houtZero
      (by simpa [amountWord, ownerWord, callerWord] using hrdAfterPayRaw)
  let memPayRetDyn :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy
      (auctionAuctionNounWord
        (auctionSettleAuctionEnterMap σ_evm I) I)
      amountWord
      (auctionAuctionStartWord
        (auctionSettleAuctionEnterMap σ_evm I) I)
      (auctionAuctionEndWord
        (auctionSettleAuctionEnterMap σ_evm I) I)
      (auctionPackedBidderWord
        (auctionAuctionPackedWord
          (auctionSettleAuctionEnterMap σ_evm I) I))
      (auctionPackedSettledEVMReturnWord
        (auctionAuctionPackedWord
          (auctionSettleAuctionEnterMap σ_evm I) I))
      callerWord outPay
  let awPayRetDyn :=
    auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
  have hfreeStable :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn)
          (auctionSettleAuctionDynDepositAw memPayRetDyn awPayRetDyn) =
        auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn := by
    simpa [memPayRetDyn, awPayRetDyn, callerWord] using
      auctionSettleAuctionTransferFromPayoutNonemptyDepositFreeStable
        (auctionAuctionNounWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
        amountWord
        (auctionAuctionStartWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
        (auctionAuctionEndWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
        (auctionPackedBidderWord
          (auctionAuctionPackedWord
            (auctionSettleAuctionEnterMap σ_evm I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord
            (auctionSettleAuctionEnterMap σ_evm I) I))
        callerWord houtPaySmall houtZero
  have hdepositLen :
      UInt256.sub
          (⟨4⟩ +
            auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn)
          (auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn) =
        ⟨4⟩ := by
    simpa [memPayRetDyn, awPayRetDyn, callerWord] using
      auctionSettleAuctionTransferFromPayoutNonemptyDepositLen
        (auctionAuctionNounWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
        amountWord
        (auctionAuctionStartWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
        (auctionAuctionEndWord
          (auctionSettleAuctionEnterMap σ_evm I) I)
        (auctionPackedBidderWord
          (auctionAuctionPackedWord
            (auctionSettleAuctionEnterMap σ_evm I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord
            (auctionSettleAuctionEnterMap σ_evm I) I))
        callerWord houtPaySmall houtZero
  obtain ⟨gasWord, kDep, CDep, hrdDepositCall⟩ :=
    auctionSettleAuctionPayoutFallbackToDepositCallAnyMem
      hwethCodeE hfreeStable hdepositLen hrdFallbackDyn
  let freePtrDyn :=
    auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
  let memDeposit :=
    auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
  let wethWord :=
    UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
  have hpostPayAccounts :
      accountMapEquiv σPay σPaySolm := by
    simpa [evmPayE, evmPay] using hpostPay
  by_cases hdepositBalance :
      amountWord ≤
        (σPay.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
  · obtain ⟨cADep, σDep, zDep, outDep, AInDep, callGasDep,
        kAfterDep, CAfterDep, hThetaDepPack, hrdAfterDepRaw,
        houtDepSize⟩ :=
      RD.callValueMade hrdDepositCall (by native_decide) _hperm
        (by simpa [amountWord] using hdepositBalance) hdepth
        (by
          change 12 ≤ 1024
          native_decide)
    obtain ⟨gDep'', ADep, hThetaDep⟩ := hThetaDepPack
    let evmDepositE :=
      { evmPayE with
          accountMap := σDep,
          substate := ADep,
          createdAccounts := cADep }
    obtain ⟨σDepSolm, ADepSolm, hdepositSolmRaw, hpostDep⟩ :=
      transferBranchCallTransport
        (evmE := evmPayE) (evmS := evmPay)
        (cA' := cADep) (σ' := σDep)
        (AIn := AInDep) (A' := ADep) (z := zDep)
        (out := outDep)
        (calldata := memDeposit.readWithPadding freePtrDyn.toNat 4)
        (g'' := gDep'') (callGas := callGasDep)
        (valueWord := amountWord) (targetWord := wethWord)
        (by
          simpa [evmPayE, initState, accountAddress_roundtrip,
            _hperm, memDeposit, memPayRetDyn, awPayRetDyn,
            freePtrDyn, wethWord] using hThetaDep)
        (by simpa [evmPayE, initState] using hdepositBalance)
        (by
          simp [evmPayE, evmTfE, initState]
          intro hbad
          have hbadVal : I.depth.val = 1024 := by
            exact congrArg Fin.val hbad
          omega)
        (by simpa [evmPayE, evmPay] using hpostPayAccounts)
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark,
            evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState,
            auctionStorageStore_σ₀])
        (by simp [evmPayE, evmPay])
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark,
            evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState,
            auctionStorageStore_genesisBlockHeader])
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark,
            evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState,
            auctionStorageStore_blocks])
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark,
            evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState,
            storageStore_executionEnv])
    let evmDeposit :=
      { evmPay with
          accountMap := σDepSolm,
          substate := ADepSolm,
          createdAccounts := cADep }
    cases zDep
    · have hdepositRawFalse :
          callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
            (Int.ofNat amountWord.toNat)
            (memDeposit.readWithPadding freePtrDyn.toNat 4)
            (false, evmDeposit, outDep) true := by
        simpa [evmDeposit] using hdepositSolmRaw
      have hwethSlotPay :
          auctionSlotWord ⟨202⟩ σPay I =
            auctionSlotWord ⟨202⟩ σPaySolm I := by
        exact accountMapEquiv_storage_findD hpostPayAccounts
          I.codeOwner ⟨202⟩ ⟨0⟩
      have hwethWordEq :
          UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask =
            wethWord := by
        have hslot :
            Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩ =
              auctionSlotWord ⟨202⟩ σPaySolm I := by
          simp [evmPay, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, auctionSlotWord, htfOwner]
        unfold wethWord
        rw [hslot, ← hwethSlotPay]
      have hwethTarget :
          EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat)) =
            AccountAddress.ofUInt256 wethWord := by
        exact transferBranchWethTarget
          (σ := σPay) (I := I) hwethWordEq (by simp [wethWord])
      have hwethCodeSolm :
          0 < (UInt256.ofNat (((evmPay.lookupAccount
            (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat))).option 0
              (fun acc => acc.code.size)))).toNat := by
        have hwethCodePay :
            0 < (UInt256.ofNat
              ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
                0 (fun acc => acc.code.size))).toNat := by
          exact auctionUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
            (σ := σPay) (target := wethWord)
            (addr := AccountAddress.ofUInt256 wethWord) rfl
            (by simpa [wethWord] using hwethCodeE)
        have hcodeEq :
            UInt256.ofNat
                ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
                  0 (fun acc => acc.code.size)) =
              UInt256.ofNat
                ((σPaySolm.find?
                  (AccountAddress.ofUInt256 wethWord)).option
                  0 (fun acc => acc.code.size)) := by
          let wethAddr := AccountAddress.ofUInt256 wethWord
          have hpayOpt :
              UInt256.ofNat
                  ((σPay.find? wethAddr).option 0
                    (fun acc => acc.code.size)) =
                ((σPay.find? wethAddr).option (⟨0⟩ : UInt256)
                  (fun acc => UInt256.ofNat acc.code.size)) := by
            cases σPay.find? wethAddr <;> rfl
          have hsolmOpt :
              UInt256.ofNat
                  ((σPaySolm.find? wethAddr).option 0
                    (fun acc => acc.code.size)) =
                ((σPaySolm.find? wethAddr).option (⟨0⟩ : UInt256)
                  (fun acc => UInt256.ofNat acc.code.size)) := by
            cases σPaySolm.find? wethAddr <;> rfl
          rw [hpayOpt, hsolmOpt]
          exact accountMapEquiv_code_size_word hpostPayAccounts
            wethAddr
        have hcodeNatEq := congrArg UInt256.toNat hcodeEq
        have hcodeSolm :
            0 < (UInt256.ofNat
              ((σPaySolm.find?
                (AccountAddress.ofUInt256 wethWord)).option
                0 (fun acc => acc.code.size))).toNat := by
          rw [← hcodeNatEq]
          exact hwethCodePay
        simpa [evmPay, State.lookupAccount, hwethWordEq,
          accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeSolm
      have hdeposit :
          typedCallViaEVM auctionConfig evmPay
            (EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat))) "deposit"
            (Int.ofNat
              (auctionSettleAuctionAmount evmEnter).toNat) []
            (false, evmDeposit, outDep) true := by
        refine ⟨memDeposit.readWithPadding freePtrDyn.toNat 4,
          ?_, ?_⟩
        · simpa [memDeposit, memPayRetDyn, awPayRetDyn,
            freePtrDyn] using
            auctionSettleAuctionTransferFromPayoutNonemptyDepositEncode_eq
              (auctionAuctionNounWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              amountWord
              (auctionAuctionStartWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionAuctionEndWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionPackedBidderWord
                (auctionAuctionPackedWord
                  (auctionSettleAuctionEnterMap σ_evm I) I))
              (auctionPackedSettledEVMReturnWord
                (auctionAuctionPackedWord
                  (auctionSettleAuctionEnterMap σ_evm I) I))
              callerWord houtPaySmall houtZero
        · rw [hwethTarget, ← hamountEq]
          exact hdepositRawFalse
      have hrdDepositFailRev :
          RDrev auctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
              A I) := by
        exact auctionCallSuccessGuardMissingPush0
          (pc := ⟨3432⟩) (okPc := ⟨3446⟩)
          (status := ⟨0⟩)
          (R := [⟨4⟩ + freePtrDyn, amountWord,
            ⟨3504541104⟩, wethWord, amountWord, ownerWord,
            ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
          (by
            simpa [amountWord, ownerWord, memDeposit, wethWord,
              freePtrDyn] using hrdAfterDepRaw)
          rfl
          (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)
          houtDepSize
          (by
            change 11 + 5 ≤ 1024
            native_decide)
      have hbody :
          ExecTransitionBody auctionConfig auctionContract evmS ∅
            settleAuctionTransition.body .reverted :=
        auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethDepositFailure
          evmS evmTf evmPay evmDeposit
          (by simpa [evmS, initState] using hwv) hpausedSolm
          hstatusSolm hstartSolm hsettledSolm htimeSolmLe
          hbidderSolm hnounsCodeSolmEval
          (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
          hamountSolm hpaySolm hwethCodeSolm hdeposit
      exact hrdDepositFailRev.reEquivExecutionRevert _hcode
        hdispatch hdecode hbody
    · have hdepositRawTrue :
          callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
            (Int.ofNat amountWord.toNat)
            (memDeposit.readWithPadding freePtrDyn.toNat 4)
            (true, evmDeposit, outDep) true := by
        simpa [evmDeposit] using hdepositSolmRaw
      have hwethSlotPay :
          auctionSlotWord ⟨202⟩ σPay I =
            auctionSlotWord ⟨202⟩ σPaySolm I := by
        exact accountMapEquiv_storage_findD hpostPayAccounts
          I.codeOwner ⟨202⟩ ⟨0⟩
      have hwethTarget :
          EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat)) =
            AccountAddress.ofUInt256 wethWord := by
        exact transferBranchWethTarget
          (σ := σPay) (I := I)
          (by
            have hslot :
                Solm.EVM.storageLoad evmPay
                    evmPay.executionEnv.codeOwner ⟨202⟩ =
                  auctionSlotWord ⟨202⟩ σPaySolm I := by
              simp [evmPay, Solm.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage,
                auctionSlotWord, htfOwner]
            unfold wethWord
            rw [hslot, ← hwethSlotPay])
          (by simp [wethWord])
      have hdeposit :
          typedCallViaEVM auctionConfig evmPay
            (EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat))) "deposit"
            (Int.ofNat
              (auctionSettleAuctionAmount evmEnter).toNat) []
            (true, evmDeposit, outDep) true := by
        refine ⟨memDeposit.readWithPadding freePtrDyn.toNat 4,
          ?_, ?_⟩
        · simpa [memDeposit, memPayRetDyn, awPayRetDyn,
            freePtrDyn] using
            auctionSettleAuctionTransferFromPayoutNonemptyDepositEncode_eq
              (auctionAuctionNounWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              amountWord
              (auctionAuctionStartWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionAuctionEndWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionPackedBidderWord
                (auctionAuctionPackedWord
                  (auctionSettleAuctionEnterMap σ_evm I) I))
              (auctionPackedSettledEVMReturnWord
                (auctionAuctionPackedWord
                  (auctionSettleAuctionEnterMap σ_evm I) I))
              callerWord houtPaySmall houtZero
        · rw [hwethTarget, ← hamountEq]
          exact hdepositRawTrue
      obtain ⟨kLoadWeth, CLoadWeth, hrdLoadWeth⟩ :=
        auctionSettleAuctionDepositSuccessToTransferLoadWethAnyMem
          (freePtr := freePtrDyn)
          (by
            have hmin :
                (min (⟨0⟩ : UInt256)
                    (UInt256.ofNat outDep.size)).toNat =
                  0 := by
              have hle :
                  (⟨0⟩ : UInt256) ≤
                    UInt256.ofNat outDep.size := by
                show (0 : Nat) ≤
                  (UInt256.ofNat outDep.size).val.val
                exact Nat.zero_le _
              simp [min, hle]
            have hrdAfterDep := hrdAfterDepRaw
            rw [hmin, byteArray_write_len_zero] at hrdAfterDep
            simpa [amountWord, ownerWord, memDeposit, wethWord,
              freePtrDyn] using hrdAfterDep)
      have hfreeAfterDepCall :
          auctionSettleAuctionDynMload64 memDeposit
              (auctionSettleAuctionDynDepositCallAw
                memPayRetDyn awPayRetDyn) =
            freePtrDyn := by
        calc
          auctionSettleAuctionDynMload64 memDeposit
              (auctionSettleAuctionDynDepositCallAw
                memPayRetDyn awPayRetDyn) =
              auctionSettleAuctionDynMload64
                memPayRetDyn awPayRetDyn := by
            simpa [memDeposit, memPayRetDyn, awPayRetDyn] using
              auctionSettleAuctionTransferFromPayoutNonemptyDepositCallFreeStable
                (auctionAuctionNounWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                amountWord
                (auctionAuctionStartWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                (auctionAuctionEndWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                (auctionPackedBidderWord
                  (auctionAuctionPackedWord
                    (auctionSettleAuctionEnterMap σ_evm I) I))
                (auctionPackedSettledEVMReturnWord
                  (auctionAuctionPackedWord
                    (auctionSettleAuctionEnterMap σ_evm I) I))
                callerWord houtPaySmall houtZero
          _ = freePtrDyn := by
            rfl
      obtain ⟨kLoadFree, CLoadFree, hrdLoadFree⟩ :=
        auctionSettleAuctionAfterDepositLoadFreePtrAnyMem
          (freePtr := freePtrDyn)
          (by
            simpa [memDeposit, memPayRetDyn, awPayRetDyn,
              freePtrDyn, auctionSettleAuctionDynDepositCallAw]
              using hfreeAfterDepCall)
          hrdLoadWeth
      obtain ⟨kStoreTransferSel, CStoreTransferSel,
          hrdStoreTransferSel⟩ :=
        auctionSettleAuctionAfterDepositStoreTransferSelectorAnyMem
          hrdLoadFree
      obtain ⟨kStoreTransferOwner, CStoreTransferOwner,
          hrdStoreTransferOwner⟩ :=
        auctionSettleAuctionAfterDepositStoreTransferOwnerAnyMem
          hrdStoreTransferSel
      obtain ⟨kStoreTransferAmount, CStoreTransferAmount,
          hrdStoreTransferAmount⟩ :=
        auctionSettleAuctionAfterDepositStoreTransferAmountAnyMem
          hrdStoreTransferOwner
      have hfreeTransfer :
          auctionSettleAuctionDynMload64
              (auctionSettleAuctionDynTransferMem memDeposit
                freePtrDyn amountWord ownerWord)
              (auctionSettleAuctionDynTransferAw
                (auctionSettleAuctionDynDepositCallAw
                  memPayRetDyn awPayRetDyn)
                freePtrDyn) =
            freePtrDyn := by
        calc
          auctionSettleAuctionDynMload64
              (auctionSettleAuctionDynTransferMem memDeposit
                freePtrDyn amountWord ownerWord)
              (auctionSettleAuctionDynTransferAw
                (auctionSettleAuctionDynDepositCallAw
                  memPayRetDyn awPayRetDyn)
                freePtrDyn) =
              auctionSettleAuctionDynMload64
                memPayRetDyn awPayRetDyn := by
            simpa [memDeposit, memPayRetDyn, awPayRetDyn,
              freePtrDyn] using
              auctionSettleAuctionTransferFromPayoutNonemptyTransferFreeStable
                (auctionAuctionNounWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                amountWord
                (auctionAuctionStartWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                (auctionAuctionEndWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                (auctionPackedBidderWord
                  (auctionAuctionPackedWord
                    (auctionSettleAuctionEnterMap σ_evm I) I))
                (auctionPackedSettledEVMReturnWord
                  (auctionAuctionPackedWord
                    (auctionSettleAuctionEnterMap σ_evm I) I))
                callerWord ownerWord houtPaySmall houtZero
          _ = freePtrDyn := by
            rfl
      have htransferLen :
          UInt256.sub ((⟨68⟩ : UInt256) + freePtrDyn)
              freePtrDyn =
            ⟨68⟩ := by
        simpa [memPayRetDyn, awPayRetDyn, freePtrDyn] using
          auctionSettleAuctionTransferFromPayoutNonemptyTransferLen
            (auctionAuctionNounWord
              (auctionSettleAuctionEnterMap σ_evm I) I)
            amountWord
            (auctionAuctionStartWord
              (auctionSettleAuctionEnterMap σ_evm I) I)
            (auctionAuctionEndWord
              (auctionSettleAuctionEnterMap σ_evm I) I)
            (auctionPackedBidderWord
              (auctionAuctionPackedWord
                (auctionSettleAuctionEnterMap σ_evm I) I))
            (auctionPackedSettledEVMReturnWord
              (auctionAuctionPackedWord
                (auctionSettleAuctionEnterMap σ_evm I) I))
            callerWord houtPaySmall houtZero
      obtain ⟨gasTransfer, kTransferCall, CTransferCall,
          hrdTransferCall⟩ :=
        auctionSettleAuctionAfterDepositPrepTransferCallAnyMem
          hfreeTransfer htransferLen hrdStoreTransferAmount
      let memTransfer :=
        auctionSettleAuctionDynTransferMem memDeposit freePtrDyn
          amountWord ownerWord
      obtain ⟨cATransfer, σTransfer, zTransfer, outTransfer,
          AInTransfer, callGasTransfer, kAfterTransfer,
          CAfterTransfer, hThetaTransferPack,
          hrdAfterTransferRaw, houtTransferSize⟩ :=
        RD.call hrdTransferCall (by native_decide) hdepth
          (by
            change 10 + 1 ≤ 1024
            native_decide)
      obtain ⟨gTransfer'', ATransfer, hThetaTransfer⟩ :=
        hThetaTransferPack
      let wethTransferWord :=
        UInt256.land (auctionSlotWord ⟨202⟩ σDep I) solcAddrMask
      let evmTransferE :=
        { evmDepositE with
            accountMap := σTransfer,
            substate := ATransfer,
            createdAccounts := cATransfer }
      obtain ⟨σTransferSolm, ATransferSolm,
          htransferSolmRaw, hpostTransfer⟩ :=
        transferBranchCallTransport
          (evmE := evmDepositE) (evmS := evmDeposit)
          (cA' := cATransfer) (σ' := σTransfer)
          (AIn := AInTransfer) (A' := ATransfer)
          (z := zTransfer) (out := outTransfer)
          (calldata := memTransfer.readWithPadding
            freePtrDyn.toNat (⟨68⟩ : UInt256).toNat)
          (g'' := gTransfer'') (callGas := callGasTransfer)
          (valueWord := ⟨0⟩) (targetWord := wethTransferWord)
          (by
            simpa [evmTransferE, evmDepositE, evmPayE,
              evmTfE, initState, memTransfer, freePtrDyn,
              wethTransferWord, _hperm] using hThetaTransfer)
          (by
            show (⟨0⟩ : UInt256) ≤
              (evmDepositE.accountMap.find?
                  evmDepositE.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance))
            exact Fin.zero_le _)
          (by
            simp [evmDepositE, evmPayE, evmTfE, initState]
            intro hbad
            have hbadVal : I.depth.val = 1024 := by
              exact congrArg Fin.val hbad
            omega)
          (by simpa [evmDepositE, evmDeposit] using hpostDep)
          (by
            simp [evmDepositE, evmDeposit, evmPayE, evmPay,
              evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              auctionStorageStore_σ₀])
          (by simp [evmDepositE, evmDeposit])
          (by
            simp [evmDepositE, evmDeposit, evmPayE, evmPay,
              evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              auctionStorageStore_genesisBlockHeader])
          (by
            simp [evmDepositE, evmDeposit, evmPayE, evmPay,
              evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              auctionStorageStore_blocks])
          (by
            simp [evmDepositE, evmDeposit, evmPayE, evmPay,
              evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              storageStore_executionEnv])
      let evmTransfer :=
        { evmDeposit with
            accountMap := σTransferSolm,
            substate := ATransferSolm,
            createdAccounts := cATransfer }
      have htransferRaw :
          callViaEVM evmDeposit
            (AccountAddress.ofUInt256 wethTransferWord) 0
            (memTransfer.readWithPadding freePtrDyn.toNat
              (⟨68⟩ : UInt256).toNat)
            (zTransfer, evmTransfer, outTransfer) true := by
        simpa [evmTransfer] using htransferSolmRaw
      have hwethSlotDep :
          auctionSlotWord ⟨202⟩ σDep I =
            auctionSlotWord ⟨202⟩ σDepSolm I := by
        exact accountMapEquiv_storage_findD hpostDep
          I.codeOwner ⟨202⟩ ⟨0⟩
      have hdepositOwner :
          evmDeposit.executionEnv.codeOwner = I.codeOwner := by
        simp [evmDeposit, evmPay, evmTf, evmMark, evmEnter,
          evmS, auctionSettleAuctionMarkSettledState,
          auctionSettleAuctionEnterState, initState,
          storageStore_executionEnv]
      have hpayOwnerTransfer :
          evmPay.executionEnv.codeOwner = I.codeOwner := by
        simp [evmPay, evmTf, evmMark, evmEnter, evmS,
          auctionSettleAuctionMarkSettledState,
          auctionSettleAuctionEnterState, initState,
          storageStore_executionEnv]
      have hwethTargetTransfer :
          EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmDeposit
                  evmDeposit.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat)) =
            AccountAddress.ofUInt256 wethTransferWord := by
        exact transferBranchWethTarget
          (σ := σDep) (I := I)
          (by
            have hslot :
                Solm.EVM.storageLoad evmDeposit
                    evmDeposit.executionEnv.codeOwner ⟨202⟩ =
                  auctionSlotWord ⟨202⟩ σDepSolm I := by
              simp [evmDeposit, Solm.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage,
                auctionSlotWord, hpayOwnerTransfer]
            unfold wethTransferWord
            rw [hslot, ← hwethSlotDep])
          (by simp [wethTransferWord])
      have hownerMask :
          UInt256.land solcAddrMask ownerWord = ownerWord := by
        rw [u256_land_comm solcAddrMask ownerWord]
        simpa [ownerWord] using hownerWordMasked
      have hownerCanon :
          (UInt256.land solcAddrMask ownerWord).toNat <
            EVM.addressModulus := by
        rw [u256_land_comm solcAddrMask ownerWord]
        exact solcAddrMask_result_canonical ownerWord
      have hownerAddr :
          auctionOwnerAddressAt evmTf =
            AccountAddress.ofUInt256 ownerWord := by
        have hownerAddressId :
            EVM.address (auctionOwnerAddressAt evmTf) =
              auctionOwnerAddressAt evmTf := by
          apply Fin.ext
          simp [EVM.address, EVM.uintN, EVM.twoPow,
            AccountAddress.size]
        exact hownerAddressId.symm.trans hownerEq
      have htransfer :
          typedCallViaEVM auctionConfig evmDeposit
            (EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmDeposit
                  evmDeposit.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat))) "transfer" 0
            [.address (auctionOwnerAddressAt evmTf),
              .int (Int.ofNat
                (auctionSettleAuctionAmount evmEnter).toNat)]
            (zTransfer, evmTransfer, outTransfer) true := by
        refine ⟨memTransfer.readWithPadding freePtrDyn.toNat 68,
          ?_, ?_⟩
        · have henc :=
            auctionSettleAuctionTransferFromPayoutNonemptyTransferEncode_eq
              (auctionAuctionNounWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              amountWord
              (auctionAuctionStartWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionAuctionEndWord
                (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionPackedBidderWord
                (auctionAuctionPackedWord
                  (auctionSettleAuctionEnterMap σ_evm I) I))
              (auctionPackedSettledEVMReturnWord
                (auctionAuctionPackedWord
                  (auctionSettleAuctionEnterMap σ_evm I) I))
              callerWord ownerWord houtPaySmall houtZero hownerCanon
          rw [hownerMask] at henc
          rw [← hamountEq]
          simpa [memTransfer, memDeposit, memPayRetDyn,
            awPayRetDyn, freePtrDyn, hownerAddr] using henc
        · rw [hwethTargetTransfer]
          simpa [memTransfer] using htransferRaw
      have hwethCodeSolmTransfer :
          0 < (UInt256.ofNat (((evmPay.lookupAccount
            (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat))).option 0
              (fun acc => acc.code.size)))).toNat := by
        have hwethWordPayEq :
            UInt256.land
                (Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask =
              wethWord := by
          have hslot :
              Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩ =
                auctionSlotWord ⟨202⟩ σPaySolm I := by
            simp [evmPay, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage,
              auctionSlotWord, htfOwner]
          unfold wethWord
          rw [hslot, ← hwethSlotPay]
        have hwethCodePay :
            0 < (UInt256.ofNat
              ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
                0 (fun acc => acc.code.size))).toNat := by
          exact auctionUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
            (σ := σPay) (target := wethWord)
            (addr := AccountAddress.ofUInt256 wethWord) rfl
            (by simpa [wethWord] using hwethCodeE)
        have hcodeEq :
            UInt256.ofNat
                ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
                  0 (fun acc => acc.code.size)) =
              UInt256.ofNat
                ((σPaySolm.find?
                  (AccountAddress.ofUInt256 wethWord)).option
                  0 (fun acc => acc.code.size)) := by
          let wethAddr := AccountAddress.ofUInt256 wethWord
          have hpayOpt :
              UInt256.ofNat
                  ((σPay.find? wethAddr).option 0
                    (fun acc => acc.code.size)) =
                ((σPay.find? wethAddr).option (⟨0⟩ : UInt256)
                  (fun acc => UInt256.ofNat acc.code.size)) := by
            cases σPay.find? wethAddr <;> rfl
          have hsolmOpt :
              UInt256.ofNat
                  ((σPaySolm.find? wethAddr).option 0
                    (fun acc => acc.code.size)) =
                ((σPaySolm.find? wethAddr).option (⟨0⟩ : UInt256)
                  (fun acc => UInt256.ofNat acc.code.size)) := by
            cases σPaySolm.find? wethAddr <;> rfl
          rw [hpayOpt, hsolmOpt]
          exact accountMapEquiv_code_size_word hpostPayAccounts
            wethAddr
        have hcodeNatEq := congrArg UInt256.toNat hcodeEq
        have hcodeSolm :
            0 < (UInt256.ofNat
              ((σPaySolm.find?
                (AccountAddress.ofUInt256 wethWord)).option
                0 (fun acc => acc.code.size))).toNat := by
          rw [← hcodeNatEq]
          exact hwethCodePay
        simpa [evmPay, State.lookupAccount, hwethWordPayEq,
          accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeSolm
      cases zTransfer
      · have htransferFalse :
            typedCallViaEVM auctionConfig evmDeposit
              (EVM.address (AccountAddress.ofNat
                ((UInt256.land
                  (Solm.EVM.storageLoad evmDeposit
                    evmDeposit.executionEnv.codeOwner ⟨202⟩)
                  solcAddrMask).toNat))) "transfer" 0
              [.address (auctionOwnerAddressAt evmTf),
                .int (Int.ofNat
                  (auctionSettleAuctionAmount evmEnter).toNat)]
              (false, evmTransfer, outTransfer) true := by
          simpa using htransfer
        have hrdTransferFailRev :
            RDrev auctionBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
                A I) := by
          exact auctionCallSuccessGuardMissingPush0
            (pc := ⟨3518⟩) (okPc := ⟨3532⟩)
            (status := ⟨0⟩)
            (R := [(⟨68⟩ : UInt256) + freePtrDyn,
              ⟨2835717307⟩, wethTransferWord, amountWord,
              ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
              auctionSelWord I])
            (by
              simpa only [amountWord, ownerWord, memTransfer,
                wethTransferWord, freePtrDyn] using
                hrdAfterTransferRaw)
            rfl
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            houtTransferSize
            (by
              change 10 + 5 ≤ 1024
              native_decide)
        have hbody :
            ExecTransitionBody auctionConfig auctionContract evmS ∅
              settleAuctionTransition.body .reverted :=
          auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferFailure
            evmS evmTf evmPay evmDeposit evmTransfer
            (by simpa [evmS, initState] using hwv) hpausedSolm
            hstatusSolm hstartSolm hsettledSolm htimeSolmLe
            hbidderSolm hnounsCodeSolmEval
            (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
            hamountSolm hpaySolm hwethCodeSolmTransfer hdeposit
            htransferFalse
        exact hrdTransferFailRev.reEquivExecutionRevert _hcode
          hdispatch hdecode hbody
      · have htransferTrue :
            typedCallViaEVM auctionConfig evmDeposit
              (EVM.address (AccountAddress.ofNat
                ((UInt256.land
                  (Solm.EVM.storageLoad evmDeposit
                    evmDeposit.executionEnv.codeOwner ⟨202⟩)
                  solcAddrMask).toNat))) "transfer" 0
              [.address (auctionOwnerAddressAt evmTf),
                .int (Int.ofNat
                  (auctionSettleAuctionAmount evmEnter).toNat)]
              (true, evmTransfer, outTransfer) true := by simpa using htransfer
        exact transferBranchPayoutFailureNonemptyTransferReturnCase
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmS := evmS) (evmTf := evmTf) (evmPay := evmPay)
          (evmDeposit := evmDeposit) (evmTransfer := evmTransfer)
          (outTf := o) (outPay := outPay) (outDeposit := outDep)
          (outTransfer := outTransfer) (cATransfer := cATransfer)
          (σTransfer := σTransfer)
          (noun := auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (amount := amountWord)
          (start := auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (finish := auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (bidder := auctionPackedBidderWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (settled := auctionPackedSettledEVMReturnWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (caller := callerWord) (owner := ownerWord) (weth := wethTransferWord)
          (kAfterTransfer := kAfterTransfer) (CAfterTransfer := CAfterTransfer)
          _hcode _hperm hdispatch hdecode rfl
          (by simpa [evmS, initState] using hwv)
          hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
          hbidderSolm hnounsCodeSolmEval
          (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
          hamountSolm hpaySolm hwethCodeSolmTransfer hdeposit htransferTrue
          (by
            simp [auctionSettleAuctionExitState, evmTransfer,
              storageStore_createdAccounts])
          (by
            simp [evmTransfer, evmDeposit, evmPay, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
              initState, storageStore_executionEnv])
          (by simpa [evmTransferE, evmTransfer] using hpostTransfer)
          houtPaySmall houtZero houtTransferSize
          (by
            have hpc : (⟨3517⟩ : UInt256) + ⟨1⟩ = ⟨3518⟩ := by
              native_decide
            have hlen68 : ((⟨68⟩ : UInt256).toNat) = 68 := by
              native_decide
            have hlen32 : ((⟨32⟩ : UInt256).toNat) = 32 := by
              native_decide
            have hawReturnEq :=
              auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnAwAfterCall_eq
                (auctionAuctionNounWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                amountWord
                (auctionAuctionStartWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                (auctionAuctionEndWord
                  (auctionSettleAuctionEnterMap σ_evm I) I)
                (auctionPackedBidderWord
                  (auctionAuctionPackedWord
                    (auctionSettleAuctionEnterMap σ_evm I) I))
                (auctionPackedSettledEVMReturnWord
                  (auctionAuctionPackedWord
                    (auctionSettleAuctionEnterMap σ_evm I) I))
                callerWord ownerWord houtPaySmall houtZero
            simpa only [amountWord, ownerWord, memTransfer, memDeposit,
              wethTransferWord, freePtrDyn, memPayRetDyn, awPayRetDyn,
              hpc, hlen68, hlen32, if_true, hawReturnEq]
              using hrdAfterTransferRaw)
  · obtain ⟨kAfterDep, CAfterDep, hrdAfterDepRaw⟩ :=
      RD.callValueInsufficientBalance hrdDepositCall _hperm
        (by native_decide)
        (by simpa [amountWord] using hdepositBalance)
        hdepth
        (by
          change 12 ≤ 1024
          native_decide)
    let evmDeposit :=
      { evmPay with
        substate :=
          (evmPay.addAccessedAccount
            (AccountAddress.ofUInt256 wethWord)).substate }
    have hbalanceEq :
        ((σPay.find? I.codeOwner).elim (⟨0⟩ : UInt256)
            (fun acc => acc.balance)) =
          ((σPaySolm.find? I.codeOwner).elim
            (⟨0⟩ : UInt256) (fun acc => acc.balance)) := by
      have hmap := hpostPayAccounts I.codeOwner
      cases hσ : σPay.find? I.codeOwner <;>
        cases hτ : σPaySolm.find? I.codeOwner <;>
        simp [hσ, hτ] at hmap ⊢
      exact hmap.2.1
    have hbalanceSolm :
        ¬ amountWord ≤
          (evmPay.accountMap.find? evmPay.executionEnv.codeOwner
            |>.elim ⟨0⟩ (·.balance)) := by
      intro hbal
      apply hdepositBalance
      rw [hbalanceEq]
      simpa [evmPay, evmTf, evmMark, evmEnter, evmS,
        auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState,
        storageStore_executionEnv] using hbal
    have hdepositRawFalse :
        callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
          (Int.ofNat amountWord.toNat)
          (memDeposit.readWithPadding freePtrDyn.toNat 4)
          (false, evmDeposit, ByteArray.empty) true := by
      apply callViaEVM.callNotMade
      · rfl
      · rfl
      · intro hmade
        have hmadeBalance := hmade.1
        rw [wordOfInt_ofNat_toNat amountWord] at hmadeBalance
        exact hbalanceSolm hmadeBalance
    have hwethSlotPay :
        auctionSlotWord ⟨202⟩ σPay I =
          auctionSlotWord ⟨202⟩ σPaySolm I := by
      exact accountMapEquiv_storage_findD hpostPayAccounts
        I.codeOwner ⟨202⟩ ⟨0⟩
    have hwethTarget :
        EVM.address (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat)) =
          AccountAddress.ofUInt256 wethWord := by
      exact transferBranchWethTarget
        (σ := σPay) (I := I)
        (by
          have hslot :
              Solm.EVM.storageLoad evmPay
                  evmPay.executionEnv.codeOwner ⟨202⟩ =
                auctionSlotWord ⟨202⟩ σPaySolm I := by
            simp [evmPay, Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, auctionSlotWord, htfOwner]
          unfold wethWord
          rw [hslot, ← hwethSlotPay])
        (by simp [wethWord])
    have hwethCodeSolm :
        0 < (UInt256.ofNat (((evmPay.lookupAccount
          (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))).option 0
            (fun acc => acc.code.size)))).toNat := by
      have hwethWordPayEq :
          UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask =
            wethWord := by
        have hslot :
            Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩ =
              auctionSlotWord ⟨202⟩ σPaySolm I := by
          simp [evmPay, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, auctionSlotWord, htfOwner]
        unfold wethWord
        rw [hslot, ← hwethSlotPay]
      have hwethCodePay :
          0 < (UInt256.ofNat
            ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
              0 (fun acc => acc.code.size))).toNat := by
        exact auctionUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
          (σ := σPay) (target := wethWord)
          (addr := AccountAddress.ofUInt256 wethWord) rfl
          (by simpa [wethWord] using hwethCodeE)
      have hcodeEq :
          UInt256.ofNat
              ((σPay.find? (AccountAddress.ofUInt256 wethWord)).option
                0 (fun acc => acc.code.size)) =
            UInt256.ofNat
              ((σPaySolm.find?
                (AccountAddress.ofUInt256 wethWord)).option
                0 (fun acc => acc.code.size)) := by
        let wethAddr := AccountAddress.ofUInt256 wethWord
        have hpayOpt :
            UInt256.ofNat
                ((σPay.find? wethAddr).option 0
                  (fun acc => acc.code.size)) =
              ((σPay.find? wethAddr).option (⟨0⟩ : UInt256)
                (fun acc => UInt256.ofNat acc.code.size)) := by
          cases σPay.find? wethAddr <;> rfl
        have hsolmOpt :
            UInt256.ofNat
                ((σPaySolm.find? wethAddr).option 0
                  (fun acc => acc.code.size)) =
              ((σPaySolm.find? wethAddr).option (⟨0⟩ : UInt256)
                (fun acc => UInt256.ofNat acc.code.size)) := by
          cases σPaySolm.find? wethAddr <;> rfl
        rw [hpayOpt, hsolmOpt]
        exact accountMapEquiv_code_size_word hpostPayAccounts
          wethAddr
      have hcodeNatEq := congrArg UInt256.toNat hcodeEq
      have hcodeSolm :
          0 < (UInt256.ofNat
            ((σPaySolm.find?
              (AccountAddress.ofUInt256 wethWord)).option
              0 (fun acc => acc.code.size))).toNat := by
        rw [← hcodeNatEq]
        exact hwethCodePay
      simpa [evmPay, State.lookupAccount, hwethWordPayEq,
        accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeSolm
    have hdeposit :
        typedCallViaEVM auctionConfig evmPay
          (EVM.address (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))) "deposit"
          (Int.ofNat
            (auctionSettleAuctionAmount evmEnter).toNat) []
          (false, evmDeposit, ByteArray.empty) true := by
      refine ⟨memDeposit.readWithPadding freePtrDyn.toNat 4, ?_, ?_⟩
      · simpa [memDeposit, memPayRetDyn, awPayRetDyn,
          freePtrDyn] using
          auctionSettleAuctionTransferFromPayoutNonemptyDepositEncode_eq
            (auctionAuctionNounWord
              (auctionSettleAuctionEnterMap σ_evm I) I)
            amountWord
            (auctionAuctionStartWord
              (auctionSettleAuctionEnterMap σ_evm I) I)
            (auctionAuctionEndWord
              (auctionSettleAuctionEnterMap σ_evm I) I)
            (auctionPackedBidderWord
              (auctionAuctionPackedWord
                (auctionSettleAuctionEnterMap σ_evm I) I))
            (auctionPackedSettledEVMReturnWord
              (auctionAuctionPackedWord
                (auctionSettleAuctionEnterMap σ_evm I) I))
            callerWord houtPaySmall houtZero
      · rw [hwethTarget, ← hamountEq]
        exact hdepositRawFalse
    have hrdDepositFailRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I) := by
      exact auctionCallSuccessGuardMissingPush0
        (pc := ⟨3432⟩) (okPc := ⟨3446⟩)
        (status := ⟨0⟩)
        (R := [⟨4⟩ + freePtrDyn, amountWord,
          ⟨3504541104⟩, wethWord, amountWord, ownerWord,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
        (by
          simpa [amountWord, ownerWord, memDeposit, wethWord,
            freePtrDyn] using hrdAfterDepRaw)
        rfl
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by simp [UInt256.size])
        (by
          change 11 + 5 ≤ 1024
          native_decide)
    have hbody :
        ExecTransitionBody auctionConfig auctionContract evmS ∅
          settleAuctionTransition.body .reverted :=
      auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethDepositFailure
        evmS evmTf evmPay evmDeposit
        (by simpa [evmS, initState] using hwv) hpausedSolm
        hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
        hamountSolm hpaySolm hwethCodeSolm hdeposit
    exact hrdDepositFailRev.reEquivExecutionRevert _hcode
      hdispatch hdecode hbody
end Auction

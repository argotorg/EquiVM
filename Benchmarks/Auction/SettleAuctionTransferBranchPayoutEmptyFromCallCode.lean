import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyFromCall

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutFailureEmptyFromCallTransferReturnCase
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
    (houtTransferSize : outTransfer.size < UInt256.size)
    (hrdAfterTransfer :
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller
      let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      let awCall := auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)
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
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder settled caller
  let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
  let awCall := auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
  let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  let transferRetWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
  have hfreePtr : freePtr = (⟨352⟩ : UInt256) := by
    simpa [freePtr, memLoop] using
      transferBranchTransferFromPayoutLoopDynMload64Aw14
        noun amount start finish bidder settled caller
  have hbaseAddHi (hhi : outTransfer.size < 2 ^ 255) :
      freePtr.toNat + outTransfer.size < UInt256.size := by
    rw [hfreePtr]
    change 352 + outTransfer.size < UInt256.size
    norm_num [UInt256.size] at hhi ⊢
    omega
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      freePtr := by
    rw [hfreePtr]
    simpa [memLoop, freePtr, memDeposit, awCall, memTransfer, awTransfer, len, memReturn,
      awReturn, hfreePtr] using
      transferBranchTransferFromPayoutLoopDynTransferReturnMload64Aw14
        noun amount start finish bidder settled caller owner houtTransferSize
  have hword (houtTransfer32 : 32 ≤ outTransfer.size) :
      let osz := UInt256.ofNat outTransfer.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add freePtr rounded
      let aw64 := UInt256.ofNat (MachineState.M awReturn.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 memReturn (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if freePtr.toNat ≥ memRet.size ∨ freePtr ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding freePtr.toNat 32))) =
      transferRetWord := by
    rw [hfreePtr]
    simpa [transferRetWord, memLoop, freePtr, memDeposit, awCall, memTransfer, awTransfer, len,
      memReturn, awReturn, hfreePtr] using
      transferBranchTransferFromPayoutLoopDynTransferReturnMload352Aw14
        noun amount start finish bidder settled caller owner houtTransfer32 houtTransferSize
  by_cases hshortTransfer : outTransfer.size < 32
  · have htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none :=
      auctionExternalABI_decode_transfer_none_short hshortTransfer
    have hrdTransferDecodeRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      exact auctionSettleAuctionTransferReturnShortRevertAt
        (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
        (rd := hrdAfterTransfer) hshortTransfer (hbaseAddHi (by omega)) hfp
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
        exact auctionSettleAuctionTransferReturnHugeRevertAt
          (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
          (rd := hrdAfterTransfer) hhugeTransfer houtTransferSize hfp
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
          auctionExternalABI_decode_transfer_false
            houtTransfer32 houtTransferHi htransferZero
        obtain ⟨_, _, _, _, hrdEvent⟩ :=
          auctionSettleAuctionTransferReturnBoolToEventAt
            (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
            (retWord := transferRetWord) (rd := hrdAfterTransfer) houtTransfer32
            houtTransferHi (hbaseAddHi houtTransferHi) hfp (hword houtTransfer32)
            (Or.inl htransferZero)
        have hret :
            RDret auctionBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (cATransfer, auctionSettleAuctionExitMap σTransfer I) ByteArray.empty :=
          auctionSettleAuctionEventToReturn _hperm hrdEvent
        exact hfinishReturn htransferDec hret
      · by_cases htransferOne : transferRetWord = ⟨1⟩
        · have htransferDec :
              auctionConfig.externalABI.decode? "transfer" outTransfer = some [.bool true] :=
            auctionExternalABI_decode_transfer_true
              houtTransfer32 houtTransferHi htransferOne
          obtain ⟨_, _, _, _, hrdEvent⟩ :=
            auctionSettleAuctionTransferReturnBoolToEventAt
              (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
              (retWord := transferRetWord) (rd := hrdAfterTransfer) houtTransfer32
              houtTransferHi (hbaseAddHi houtTransferHi) hfp (hword houtTransfer32)
              (Or.inr htransferOne)
          have hret :
              RDret auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (cATransfer, auctionSettleAuctionExitMap σTransfer I) ByteArray.empty :=
            auctionSettleAuctionEventToReturn _hperm hrdEvent
          exact hfinishReturn htransferDec hret
        · have htransferDec :
              auctionConfig.externalABI.decode? "transfer" outTransfer = none :=
            auctionExternalABI_decode_transfer_none_noncanon
              houtTransfer32 houtTransferHi htransferZero htransferOne
          have hrdTransferDecodeRev :
              RDrev auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
            exact auctionSettleAuctionTransferReturnNoncanonRevertAt
              (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
              (retWord := transferRetWord) (rd := hrdAfterTransfer) houtTransfer32
              houtTransferHi (hbaseAddHi houtTransferHi) hfp (hword houtTransfer32)
              htransferZero htransferOne
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

theorem transferBranchPayoutFailureEmptyFromCallToDepositCall
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAPay : Batteries.RBSet AccountAddress compare} {σPay : AccountMap}
    {noun amount start finish bidder settled caller owner : UInt256}
    {outPay : ByteArray} {kFallback CFallback : ℕ}
    (hwethCodeE :
      Reasoning.Theory.uniswapExtCodeSizeWord σPay
          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask) ≠
        ⟨0⟩)
    (hrdFallbackDyn :
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3347⟩
        [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
          auctionSelWord I]
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14) outPay (cAPay, σPay) kFallback CFallback) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let weth := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
    let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let awAfterLoad :=
      auctionSettleAuctionDynDepositAwAfterMload64 memLoop (UInt256.ofNat 14)
    ∃ gasWord k' C',
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3431⟩
        [gasWord, weth, amount, freePtr, ⟨4⟩, freePtr, ⟨0⟩, ⟨4⟩ + freePtr,
          amount, ⟨3504541104⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memDeposit awAfterLoad outPay (cAPay, σPay) k' C' := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
      noun amount start finish bidder settled caller
  have hfreeStable :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14))
          (auctionSettleAuctionDynDepositAw memLoop (UInt256.ofNat 14)) =
        auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14) := by
    simpa [memLoop] using
      transferBranchTransferFromPayoutLoopDynDepositFreeStableAw14
        noun amount start finish bidder settled caller
  have hdepositLen :
      UInt256.sub
          (⟨4⟩ + auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14))
          (auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)) =
        ⟨4⟩ := by
    simpa [memLoop] using
      transferBranchTransferFromPayoutLoopDynDepositLenAw14
        noun amount start finish bidder settled caller
  simpa [memLoop] using
    auctionSettleAuctionPayoutFallbackToDepositCallAnyMem
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (cA' := cAPay) (σ' := σPay)
      (amount := amount) (owner := owner) (aw := UInt256.ofNat 14)
      (mem := memLoop) (o := outPay) hwethCodeE hfreeStable hdepositLen
      hrdFallbackDyn

theorem transferBranchPayoutFailureEmptyFromCallDepositInsufficientCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm : AccountMap}
    {A' A'_solm APay APaySolm : Substate}
    {o outPay : ByteArray} {gasWord : UInt256} {kDep CDep : ℕ}
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
    (hrdDepositCall :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let amountWord := auctionAuctionAmountWord σ1 I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      let callerWord := UInt256.ofNat ↑I.codeOwner
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord σ1 I)
          amountWord
          (auctionAuctionStartWord σ1 I)
          (auctionAuctionEndWord σ1 I)
          (auctionPackedBidderWord (auctionAuctionPackedWord σ1 I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ1 I))
          callerWord
      let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      let awAfterLoad :=
        auctionSettleAuctionDynDepositAwAfterMload64 memLoop (UInt256.ofNat 14)
      let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3431⟩
        [gasWord, wethWord, amountWord, freePtr, ⟨4⟩, freePtr, ⟨0⟩,
          ⟨4⟩ + freePtr, amountWord, ⟨3504541104⟩, wethWord, amountWord,
          ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memDeposit awAfterLoad outPay (cAPay, σPay) kDep CDep)
    (hwethCodeE :
      Reasoning.Theory.uniswapExtCodeSizeWord σPay
          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask) ≠
        ⟨0⟩)
    (hdepositBalance :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      ¬ amountWord ≤
        (σPay.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))) :
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
  let callerWord := UInt256.ofNat ↑I.codeOwner
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
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
      callerWord
  let awPayRetDyn := UInt256.ofNat 14
  let freePtrDyn := auctionSettleAuctionDynMload64 memLoop awPayRetDyn
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop awPayRetDyn
  let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
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
  have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
    simpa [evmPayE, evmPay] using hpostPay
  have hdepositGap :
      freePtrDyn.toNat - memLoop.size < USize.size := by
    simpa [memLoop, awPayRetDyn, freePtrDyn, callerWord] using
      transferBranchTransferFromPayoutLoopDynDepositGapAw14
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
        callerWord
  have hdepositEncode :
      auctionConfig.externalABI.encode? "deposit" [] =
        some (memDeposit.readWithPadding freePtrDyn.toNat 4) := by
    simpa [memDeposit, freePtrDyn] using
      auctionSettleAuctionDynDepositEncode_eq
        (mem := memLoop) (aw := awPayRetDyn) hdepositGap
  obtain ⟨kAfterDep, CAfterDep, hrdAfterDepRaw⟩ :=
    RD.callValueInsufficientBalance
      (by
        simpa [amountWord, ownerWord, callerWord, memLoop, awPayRetDyn,
          freePtrDyn, memDeposit, wethWord] using hrdDepositCall)
      _hperm
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
    · exact hdepositEncode
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
      (by simpa only [evmS, initState] using hwv) hpausedSolm
      hstatusSolm hstartSolm hsettledSolm htimeSolmLe
      hbidderSolm hnounsCodeSolmEval
      (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
      hamountSolm hpaySolm hwethCodeSolm hdeposit
  exact hrdDepositFailRev.reEquivExecutionRevert _hcode
    hdispatch hdecode hbody

theorem transferBranchPayoutFailureEmptyFromCallDepositMadeFailureCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay cADep : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm σDep σDepSolm : AccountMap}
    {A' A'_solm APay APaySolm ADepSolm : Substate}
    {o outPay outDep : ByteArray} {kAfterDep CAfterDep : ℕ}
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
    (hamountEq :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      amountWord = auctionSettleAuctionAmount evmEnter)
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
    (hdepositRawFalse :
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
      let callerWord := UInt256.ofNat ↑I.codeOwner
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          amountWord
          (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          callerWord
      let freePtrDyn := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
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
      let evmDeposit :=
        { evmPay with
          accountMap := σDepSolm,
          substate := ADepSolm,
          createdAccounts := cADep }
      callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
        (Int.ofNat amountWord.toNat) (memDeposit.readWithPadding freePtrDyn.toNat 4)
        (false, evmDeposit, outDep) true)
    (hrdAfterDepRaw :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let amountWord := auctionAuctionAmountWord σ1 I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      let callerWord := UInt256.ofNat ↑I.codeOwner
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord σ1 I)
          amountWord
          (auctionAuctionStartWord σ1 I)
          (auctionAuctionEndWord σ1 I)
          (auctionPackedBidderWord (auctionAuctionPackedWord σ1 I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ1 I))
          callerWord
      let freePtrDyn := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
      let len := (min (⟨0⟩ : UInt256) (UInt256.ofNat outDep.size)).toNat
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3432⟩
        [⟨0⟩, ⟨4⟩ + freePtrDyn, amountWord, ⟨3504541104⟩,
          wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        (outDep.write 0 memDeposit freePtrDyn.toNat len)
        (UInt256.ofNat
          (MachineState.M
            (MachineState.M
              (auctionSettleAuctionDynDepositAwAfterMload64 memLoop (UInt256.ofNat 14)).toNat
              freePtrDyn.toNat (⟨4⟩ : UInt256).toNat)
            freePtrDyn.toNat len))
        outDep (cADep, σDep) kAfterDep CAfterDep)
    (houtDepSize : outDep.size < UInt256.size)
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
  let callerWord := UInt256.ofNat ↑I.codeOwner
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
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
      callerWord
  let awPayRetDyn := UInt256.ofNat 14
  let freePtrDyn := auctionSettleAuctionDynMload64 memLoop awPayRetDyn
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop awPayRetDyn
  let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
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
  let evmDeposit :=
    { evmPay with
      accountMap := σDepSolm,
      substate := ADepSolm,
      createdAccounts := cADep }
  have htfOwner : evmTf.executionEnv.codeOwner = I.codeOwner := by
    simp [evmTf, evmMark, evmEnter, evmS,
      auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState,
      storageStore_executionEnv]
  have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
    simpa [evmPayE, evmPay] using hpostPay
  have hdepositGap :
      freePtrDyn.toNat - memLoop.size < USize.size := by
    simpa [memLoop, awPayRetDyn, freePtrDyn, callerWord] using
      transferBranchTransferFromPayoutLoopDynDepositGapAw14
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
        callerWord
  have hdepositEncode :
      auctionConfig.externalABI.encode? "deposit" [] =
        some (memDeposit.readWithPadding freePtrDyn.toNat 4) := by
    simpa [memDeposit, freePtrDyn] using
      auctionSettleAuctionDynDepositEncode_eq
        (mem := memLoop) (aw := awPayRetDyn) hdepositGap
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
        (false, evmDeposit, outDep) true := by
    refine ⟨memDeposit.readWithPadding freePtrDyn.toNat 4, ?_, ?_⟩
    · exact hdepositEncode
    · rw [hwethTarget, ← hamountEq]
      simpa [evmDeposit, memLoop, awPayRetDyn, freePtrDyn, memDeposit,
        wethWord, callerWord] using hdepositRawFalse
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
        simpa [amountWord, ownerWord, memLoop, awPayRetDyn, memDeposit, wethWord,
          freePtrDyn, callerWord] using hrdAfterDepRaw)
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
      (by simpa only [evmS, initState] using hwv) hpausedSolm
      hstatusSolm hstartSolm hsettledSolm htimeSolmLe
      hbidderSolm hnounsCodeSolmEval
      (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
      hamountSolm hpaySolm hwethCodeSolm hdeposit
  exact hrdDepositFailRev.reEquivExecutionRevert _hcode
    hdispatch hdecode hbody

theorem transferBranchPayoutFailureEmptyFromCallDepositSuccessToTransferCall
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cADep : Batteries.RBSet AccountAddress compare} {σDep : AccountMap}
    {noun amount start finish bidder settled caller owner wethBefore : UInt256}
    {outDep : ByteArray} {kAfterDep CAfterDep : ℕ}
    (hrdAfterDep :
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller
      let freePtrDyn := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3432⟩
        [⟨1⟩, ⟨4⟩ + freePtrDyn, amount, ⟨3504541104⟩,
          wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memDeposit (auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14))
        outDep (cADep, σDep) kAfterDep CAfterDep) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let freePtrDyn := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtrDyn amount owner
    let wethTransfer := UInt256.land (auctionSlotWord ⟨202⟩ σDep I) solcAddrMask
    ∃ gasTransfer kTransferCall CTransferCall,
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3517⟩
        [gasTransfer, wethTransfer, ⟨0⟩, freePtrDyn, ⟨68⟩, freePtrDyn, ⟨32⟩,
          ⟨68⟩ + freePtrDyn, ⟨2835717307⟩, wethTransfer, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memTransfer
        (auctionSettleAuctionDynTransferAwAfterMload64
          (auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)) freePtrDyn)
        outDep (cADep, σDep) kTransferCall CTransferCall := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
      noun amount start finish bidder settled caller
  let awPayRetDyn := UInt256.ofNat 14
  let freePtrDyn := auctionSettleAuctionDynMload64 memLoop awPayRetDyn
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop awPayRetDyn
  obtain ⟨kLoadWeth, CLoadWeth, hrdLoadWeth⟩ :=
    auctionSettleAuctionDepositSuccessToTransferLoadWethAnyMem
      (freePtr := freePtrDyn)
      (by
        simpa [memLoop, awPayRetDyn, memDeposit, freePtrDyn] using hrdAfterDep)
  have hfreeAfterDepCall :
      auctionSettleAuctionDynMload64 memDeposit
          (auctionSettleAuctionDynDepositCallAw memLoop awPayRetDyn) =
        freePtrDyn := by
    calc
      auctionSettleAuctionDynMload64 memDeposit
          (auctionSettleAuctionDynDepositCallAw memLoop awPayRetDyn) =
          auctionSettleAuctionDynMload64 memLoop awPayRetDyn := by
        simpa [memLoop, awPayRetDyn, memDeposit, freePtrDyn] using
          transferBranchTransferFromPayoutLoopDynDepositCallFreeStableAw14
            noun amount start finish bidder settled caller
      _ = freePtrDyn := by
        rfl
  obtain ⟨kLoadFree, CLoadFree, hrdLoadFree⟩ :=
    auctionSettleAuctionAfterDepositLoadFreePtrAnyMem
      (freePtr := freePtrDyn)
      (by
        simpa [memDeposit, memLoop, awPayRetDyn, freePtrDyn,
          auctionSettleAuctionDynDepositCallAw] using hfreeAfterDepCall)
      hrdLoadWeth
  obtain ⟨kStoreTransferSel, CStoreTransferSel, hrdStoreTransferSel⟩ :=
    auctionSettleAuctionAfterDepositStoreTransferSelectorAnyMem hrdLoadFree
  obtain ⟨kStoreTransferOwner, CStoreTransferOwner, hrdStoreTransferOwner⟩ :=
    auctionSettleAuctionAfterDepositStoreTransferOwnerAnyMem hrdStoreTransferSel
  obtain ⟨kStoreTransferAmount, CStoreTransferAmount, hrdStoreTransferAmount⟩ :=
    auctionSettleAuctionAfterDepositStoreTransferAmountAnyMem hrdStoreTransferOwner
  have hfreeTransfer :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynTransferMem memDeposit freePtrDyn amount owner)
          (auctionSettleAuctionDynTransferAw
            (auctionSettleAuctionDynDepositCallAw memLoop awPayRetDyn) freePtrDyn) =
        freePtrDyn := by
    calc
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynTransferMem memDeposit freePtrDyn amount owner)
          (auctionSettleAuctionDynTransferAw
            (auctionSettleAuctionDynDepositCallAw memLoop awPayRetDyn) freePtrDyn) =
          auctionSettleAuctionDynMload64 memLoop awPayRetDyn := by
        simpa [memLoop, awPayRetDyn, memDeposit, freePtrDyn] using
          transferBranchTransferFromPayoutLoopDynTransferFreeStableAw14
            noun amount start finish bidder settled caller owner
      _ = freePtrDyn := by
        rfl
  have htransferLen :
      UInt256.sub ((⟨68⟩ : UInt256) + freePtrDyn) freePtrDyn = ⟨68⟩ := by
    simpa [memLoop, awPayRetDyn, freePtrDyn] using
      transferBranchTransferFromPayoutLoopDynTransferLenAw14
        noun amount start finish bidder settled caller
  obtain ⟨gasTransfer, kTransferCall, CTransferCall, hrdTransferCall⟩ :=
    auctionSettleAuctionAfterDepositPrepTransferCallAnyMem
      hfreeTransfer htransferLen hrdStoreTransferAmount
  exact ⟨gasTransfer, kTransferCall, CTransferCall, hrdTransferCall⟩

theorem transferBranchPayoutFailureEmptyFromCallTransferFailureCase
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
    (htransferFalse : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTf),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evmS)).toNat)]
      (false, evmTransfer, outTransfer) true)
    (houtTransferSize : outTransfer.size < UInt256.size)
    (hrdAfterTransfer :
      let memLoop :=
        auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller
      let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
      let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
      let awCall := auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3518⟩
        [⟨0⟩, (⟨68⟩ : UInt256) + freePtr, ⟨2835717307⟩, weth, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer (cATransfer, σTransfer) kAfterTransfer CAfterTransfer) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder settled caller
  let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
  let awCall := auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
  let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  have hrdTransferFailRev :
      RDrev auctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact auctionCallSuccessGuardMissingPush0
      (pc := ⟨3518⟩) (okPc := ⟨3532⟩)
      (status := ⟨0⟩)
      (R := [(⟨68⟩ : UInt256) + freePtr, ⟨2835717307⟩, weth, amount, owner,
        ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      (by
        simpa [memLoop, freePtr, memDeposit, awCall, memTransfer, awTransfer,
          len, memReturn, awReturn] using hrdAfterTransfer)
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
      hwvS hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
      hbidderSolm hnounsCodeSolmEval hcallSolm hamountSolm hpaySolm
      hwethCodeSolmTransfer hdeposit htransferFalse
  exact hrdTransferFailRev.reEquivExecutionRevert _hcode hdispatch hdecode
    (by simpa [hevmS] using hbody)

end Auction

import Benchmarks.Auction.SettleAuctionBurnBranchPayoutNonemptyTransferReturn

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionBodyBurnPayoutFailureNonemptyTransferCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay cADep : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm σDep σDepSolm : AccountMap}
    {A' A'_solm APay APaySolm ADep ADepSolm : Substate}
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
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat =
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
      let evmBurn :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "burn" 0
        [.int (Int.ofNat
          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (true, evmBurn, o) true)
    (hpostBurn : accountMapEquiv σ' σ'_solm)
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
      let evmBurn :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      let evmBurnE :=
        { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ' } with
            substate := A',
            createdAccounts := cA' }
      let evmPayE :=
        { evmBurnE with
            accountMap := σPay,
            substate := APay,
            createdAccounts := cAPay }
      let evmPay :=
        { evmBurn with
          accountMap := σPaySolm,
          substate := APaySolm,
          createdAccounts := evmPayE.createdAccounts }
      callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
        ByteArray.empty (false, evmPay, outPay) true)
    (hpostPay : accountMapEquiv σPay σPaySolm)
    (houtZero : outPay.size ≠ 0)
    (houtPaySmall : outPay.size < 2 ^ 138)
    (hwethCodeE :
      Reasoning.Theory.uniswapExtCodeSizeWord σPay
          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I)
            solcAddrMask) ≠
        ⟨0⟩)
    (hpostDep : accountMapEquiv σDep σDepSolm)
    (hdeposit :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      let evmBurn :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      let evmBurnE :=
        { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ' } with
            substate := A',
            createdAccounts := cA' }
      let evmPayE :=
        { evmBurnE with
            accountMap := σPay,
            substate := APay,
            createdAccounts := cAPay }
      let evmPay :=
        { evmBurn with
          accountMap := σPaySolm,
          substate := APaySolm,
          createdAccounts := evmPayE.createdAccounts }
      let memPayRetDyn :=
        auctionSettleAuctionPayoutNonemptyMemCopy
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
          outPay
      let awPayRetDyn := auctionSettleAuctionPayoutNonemptyAwCopy outPay
      let freePtrDyn := auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
      let memDeposit := auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
      let evmDeposit :=
        { evmPay with
            accountMap := σDepSolm,
            substate := ADepSolm,
            createdAccounts := cADep }
      typedCallViaEVM auctionConfig evmPay
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "deposit"
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat) []
        (true, evmDeposit, outDep) true)
    (hrdLoadWethInput :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      let memPayRetDyn :=
        auctionSettleAuctionPayoutNonemptyMemCopy
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
          outPay
      let awPayRetDyn := auctionSettleAuctionPayoutNonemptyAwCopy outPay
      let freePtrDyn := auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
      let memDeposit := auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
      let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3432⟩
        [⟨1⟩, ⟨4⟩ + freePtrDyn, amountWord, ⟨3504541104⟩,
          wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
          ⟨413⟩, auctionSelWord I]
        memDeposit
        (auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn)
        outDep (cADep, σDep) kAfterDep CAfterDep) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  let evmBurn :=
    { evmMark with
      accountMap := σ'_solm,
      substate := A'_solm,
      createdAccounts := cA' }
  let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
  let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  let evmBurnE :=
    { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ' } with
        substate := A',
        createdAccounts := cA' }
  let evmPayE :=
    { evmBurnE with
        accountMap := σPay,
        substate := APay,
        createdAccounts := cAPay }
  let evmPay :=
    { evmBurn with
      accountMap := σPaySolm,
      substate := APaySolm,
      createdAccounts := evmPayE.createdAccounts }
  have hburnOwner : evmBurn.executionEnv.codeOwner = I.codeOwner := by
    simp [evmBurn, evmMark, evmEnter, evmS,
      auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState,
      storageStore_executionEnv]
  have hownerLoad :
      auctionSlotWord ⟨151⟩ σ' I =
        Solm.EVM.storageLoad evmBurn evmBurn.executionEnv.codeOwner
          ⟨151⟩ := by
    have hslot :=
      accountMapEquiv_storage_findD hpostBurn I.codeOwner ⟨151⟩
        (⟨0⟩ : UInt256)
    rw [hburnOwner]
    simpa [evmBurn, auctionSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hslot
  have hownerEq :
      EVM.address (auctionOwnerAddressAt evmBurn) =
        AccountAddress.ofUInt256 ownerWord := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    apply Fin.ext
    simp [auctionOwnerAddressAt, ownerWord, hownerLoad, EVM.address,
      EVM.uintN]
    exact Nat.mod_eq_of_lt
      (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
          solcAddrMask_result_canonical
            (Solm.EVM.storageLoad evmBurn
              evmBurn.executionEnv.codeOwner ⟨151⟩))
  have hownerWordMasked :
      UInt256.land ownerWord solcAddrMask = ownerWord := by
    simpa [ownerWord] using
      solcAddrMask_clean
        (solcAddrMask_result_canonical (auctionSlotWord ⟨151⟩ σ' I))
  have hamountEqLocal : amountWord = auctionSettleAuctionAmount evmEnter := by
    simpa [evmS, evmEnter, amountWord] using hamountEq
  let memPayRetDyn :=
    auctionSettleAuctionPayoutNonemptyMemCopy
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
      outPay
  let awPayRetDyn := auctionSettleAuctionPayoutNonemptyAwCopy outPay
  let freePtrDyn := auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
  let memDeposit := auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
  let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
  have hpostPayAccounts :
      accountMapEquiv σPay σPaySolm := by
    simpa [evmPayE, evmPay] using hpostPay
  let evmDepositE :=
    { evmPayE with
        accountMap := σDep,
        substate := ADep,
        createdAccounts := cADep }
  let evmDeposit :=
    { evmPay with
        accountMap := σDepSolm,
        substate := ADepSolm,
        createdAccounts := cADep }
  have hdepositLocal :
      typedCallViaEVM auctionConfig evmPay
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "deposit"
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat) []
        (true, evmDeposit, outDep) true := by
    simpa [evmS, evmEnter, evmMark, evmBurn, amountWord, evmBurnE,
      evmPayE, evmPay, memPayRetDyn, awPayRetDyn, freePtrDyn,
      memDeposit, evmDeposit] using hdeposit
  have hrdLoadWethInputLocal :
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3432⟩
        [⟨1⟩, ⟨4⟩ + freePtrDyn, amountWord, ⟨3504541104⟩,
          wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
          ⟨413⟩, auctionSelWord I]
        memDeposit
        (auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn)
        outDep (cADep, σDep) kAfterDep CAfterDep := by
    simpa [amountWord, ownerWord, memPayRetDyn, awPayRetDyn,
      freePtrDyn, memDeposit, wethWord] using hrdLoadWethInput
  obtain ⟨kLoadWeth, CLoadWeth, hrdLoadWeth⟩ :=
    auctionSettleAuctionDepositSuccessToTransferLoadWethAnyMem
      (freePtr := freePtrDyn) hrdLoadWethInputLocal
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
          auctionSettleAuctionPayoutNonemptyDepositCallFreeStable
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
            houtPaySmall houtZero
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
          auctionSettleAuctionPayoutNonemptyTransferFreeStable
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
            ownerWord houtPaySmall houtZero
      _ = freePtrDyn := by
        rfl
  have htransferLen :
      UInt256.sub ((⟨68⟩ : UInt256) + freePtrDyn)
          freePtrDyn =
        ⟨68⟩ := by
    simpa [memPayRetDyn, awPayRetDyn, freePtrDyn] using
      auctionSettleAuctionPayoutNonemptyTransferLen
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
        houtPaySmall houtZero
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
    auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
      (evm_evm := evmDepositE) (evm_solm := evmDeposit)
      (tgt := AccountAddress.ofUInt256 wethTransferWord)
      (value := 0)
      (calldata := memTransfer.readWithPadding
        freePtrDyn.toNat (⟨68⟩ : UInt256).toNat)
      (out := outTransfer) (cA' := cATransfer)
      (σ' := σTransfer) (A' := ATransfer)
      (A_in := AInTransfer) (z := zTransfer)
      (g'' := gTransfer'') (callGas := callGasTransfer)
      (valueWord := ⟨0⟩) (callPerm := true)
      (wordOfInt_zero).symm
      (by
        simpa [evmTransferE, evmDepositE, evmPayE,
          evmBurnE, initState, memTransfer, freePtrDyn,
          wethTransferWord, _hperm] using hThetaTransfer)
      (by
        show (⟨0⟩ : UInt256) ≤
          (evmDepositE.accountMap.find?
              evmDepositE.executionEnv.codeOwner |>.elim
                ⟨0⟩ (·.balance))
        exact Fin.zero_le _)
      (by
        simp [evmDepositE, evmPayE, evmBurnE, initState]
        intro hbad
        have hbadVal : I.depth.val = 1024 := by
          exact congrArg Fin.val hbad
        omega)
      (by simpa [evmDepositE, evmDeposit] using hpostDep)
      (by
        simp [evmDepositE, evmDeposit, evmPayE, evmPay,
          evmBurnE, evmBurn, evmMark, evmEnter, evmS,
          auctionSettleAuctionMarkSettledState,
          auctionSettleAuctionEnterState, initState,
          auctionStorageStore_σ₀])
      (by simp [evmDepositE, evmDeposit])
      (by
        simp [evmDepositE, evmDeposit, evmPayE, evmPay,
          evmBurnE, evmBurn, evmMark, evmEnter, evmS,
          auctionSettleAuctionMarkSettledState,
          auctionSettleAuctionEnterState, initState,
          auctionStorageStore_genesisBlockHeader])
      (by
        simp [evmDepositE, evmDeposit, evmPayE, evmPay,
          evmBurnE, evmBurn, evmMark, evmEnter, evmS,
          auctionSettleAuctionMarkSettledState,
          auctionSettleAuctionEnterState, initState,
          auctionStorageStore_blocks])
      (by
        simp [evmDepositE, evmDeposit, evmPayE, evmPay,
          evmBurnE, evmBurn, evmMark, evmEnter, evmS,
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
    simp [evmDeposit, evmPay, evmBurn, evmMark, evmEnter,
      evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState,
      storageStore_executionEnv]
  have hpayOwnerTransfer :
      evmPay.executionEnv.codeOwner = I.codeOwner := by
    simp [evmPay, evmBurn, evmMark, evmEnter, evmS,
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
    have hwethWordEq :
        UInt256.land
            (Solm.EVM.storageLoad evmDeposit
              evmDeposit.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask =
          wethTransferWord := by
      have hslot :
          Solm.EVM.storageLoad evmDeposit
              evmDeposit.executionEnv.codeOwner ⟨202⟩ =
            auctionSlotWord ⟨202⟩ σDepSolm I := by
        simp [evmDeposit, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage,
          auctionSlotWord, hpayOwnerTransfer]
      unfold wethTransferWord
      rw [hslot, ← hwethSlotDep]
    rw [hwethWordEq]
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    apply Fin.ext
    simp [EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt
      (by
        simpa [EVM.addressModulus, EVM.twoPow,
          AccountAddress.size, wethTransferWord] using
          solcAddrMask_result_canonical
            (auctionSlotWord ⟨202⟩ σDep I))
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
      auctionOwnerAddressAt evmBurn =
        AccountAddress.ofUInt256 ownerWord := by
    have hownerAddressId :
        EVM.address (auctionOwnerAddressAt evmBurn) =
          auctionOwnerAddressAt evmBurn := by
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
        [.address (auctionOwnerAddressAt evmBurn),
          .int (Int.ofNat
            (auctionSettleAuctionAmount evmEnter).toNat)]
        (zTransfer, evmTransfer, outTransfer) true := by
    refine ⟨memTransfer.readWithPadding freePtrDyn.toNat 68,
      ?_, ?_⟩
    · have henc :=
        auctionSettleAuctionPayoutNonemptyTransferEncode_eq
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
          ownerWord houtPaySmall houtZero hownerCanon
      rw [hownerMask] at henc
      rw [hownerAddr]
      rw [← hamountEqLocal]
      simpa [memTransfer, memDeposit, memPayRetDyn,
        awPayRetDyn, freePtrDyn] using henc
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
          auctionSlotWord, hburnOwner]
      have hwethSlotPay :
          auctionSlotWord ⟨202⟩ σPay I =
            auctionSlotWord ⟨202⟩ σPaySolm I := by
        exact accountMapEquiv_storage_findD hpostPayAccounts
          I.codeOwner ⟨202⟩ ⟨0⟩
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
          [.address (auctionOwnerAddressAt evmBurn),
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
      auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferFailure
        evmS evmBurn evmPay evmDeposit evmTransfer
        (by simpa only [evmS, initState] using hwv) hpausedSolm
        hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
        hamountSolm hpaySolm hwethCodeSolmTransfer hdepositLocal
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
          [.address (auctionOwnerAddressAt evmBurn),
            .int (Int.ofNat
            (auctionSettleAuctionAmount evmEnter).toNat)]
          (true, evmTransfer, outTransfer) true := by simpa using htransfer
    have hrdAfterTransfer :
        let awCall := auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn
        let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtrDyn
        let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
        let memReturn := outTransfer.write 0 memTransfer freePtrDyn.toNat len
        let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtrDyn.toNat 32)
        RD auctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3518⟩
          [⟨1⟩, (⟨68⟩ : UInt256) + freePtrDyn, ⟨2835717307⟩,
            wethTransferWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
            ⟨2471⟩, ⟨413⟩, auctionSelWord I]
          memReturn awReturn outTransfer (cATransfer, σTransfer)
          kAfterTransfer CAfterTransfer := by
      have hawAfterCall :=
        auctionSettleAuctionPayoutNonemptyTransferReturnAwAfterCall_eq
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
          ownerWord houtPaySmall houtZero
      have hawAfterCallLocal :
          UInt256.ofNat
              (MachineState.M
                (MachineState.M
                  (auctionSettleAuctionDynTransferAwAfterMload64
                    (auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn)
                    freePtrDyn).toNat
                  freePtrDyn.toNat (⟨68⟩ : UInt256).toNat)
                freePtrDyn.toNat (⟨32⟩ : UInt256).toNat) =
            UInt256.ofNat
              (MachineState.M
                (auctionSettleAuctionDynTransferAw
                  (auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn)
                  freePtrDyn).toNat
                freePtrDyn.toNat 32) := by
        simpa [memPayRetDyn, awPayRetDyn, freePtrDyn] using hawAfterCall
      have hrdAfterTransferNorm := hrdAfterTransferRaw
      rw [hawAfterCallLocal] at hrdAfterTransferNorm
      simpa only [amountWord, ownerWord, memTransfer,
        memDeposit, wethTransferWord, freePtrDyn,
        memPayRetDyn, awPayRetDyn, if_true,
        show ((⟨3517⟩ : UInt256) + ⟨1⟩ = ⟨3518⟩) by native_decide,
        show ((⟨68⟩ : UInt256).toNat = 68) by native_decide,
        show ((⟨32⟩ : UInt256).toNat = 32) by native_decide] using hrdAfterTransferNorm
    exact
      auctionSettleAuctionBodyBurnPayoutFailureNonemptyTransferReturnCase
        (cATransfer := cATransfer) (σTransfer := σTransfer)
        (σTransferSolm := σTransferSolm) (ATransferSolm := ATransferSolm)
        _hcode _hperm hdispatch hdecode hwv
        hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval hcallSolm hamountSolm hpaySolm
        houtZero houtPaySmall hpostTransfer hdepositLocal htransferTrue
        hwethCodeSolmTransfer hrdAfterTransfer houtTransferSize


end Auction

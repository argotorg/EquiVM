import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyFromCallCodeWethDepositSuccess

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction
theorem transferBranchPayoutFailureEmptyFromCallWethCodeCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm : AccountMap}
    {A' A'_solm APay APaySolm : Substate}
    {o outPay : ByteArray} {kFallback CFallback : ℕ}
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
    (hrdFallbackDyn :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let amountWord := auctionAuctionAmountWord σ1 I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      let callerWord := UInt256.ofNat ↑I.codeOwner
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3347⟩
        [⟨0⟩, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
          auctionSelWord I]
        (auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord σ1 I)
          amountWord
          (auctionAuctionStartWord σ1 I)
          (auctionAuctionEndWord σ1 I)
          (auctionPackedBidderWord (auctionAuctionPackedWord σ1 I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ1 I))
          callerWord)
        (UInt256.ofNat 14) outPay (cAPay, σPay) kFallback CFallback)
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
  let memPayRetDyn :=
    auctionSettleAuctionTransferFromPayoutLoopMem
      (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
      amountWord
      (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
      (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
      (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
      (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
      callerWord
  let awPayRetDyn := UInt256.ofNat 14
  let freePtrDyn := auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
  let memDeposit := auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
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
    simp [evmTf, evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
    simpa [evmPayE, evmPay] using hpostPay
  have hdepositGap : freePtrDyn.toNat - memPayRetDyn.size < USize.size := by
    simpa [memPayRetDyn, awPayRetDyn, freePtrDyn, callerWord] using
      transferBranchTransferFromPayoutLoopDynDepositGapAw14
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
        amountWord
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
        (auctionPackedBidderWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
        callerWord
  have hdepositEncode :
      auctionConfig.externalABI.encode? "deposit" [] =
        some (memDeposit.readWithPadding freePtrDyn.toNat 4) := by
    simpa [memDeposit, freePtrDyn] using
      auctionSettleAuctionDynDepositEncode_eq
        (mem := memPayRetDyn) (aw := awPayRetDyn) hdepositGap
  obtain ⟨gasWord, kDep, CDep, hrdDepositCall⟩ :=
    transferBranchPayoutFailureEmptyFromCallToDepositCall
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (cAPay := cAPay) (σPay := σPay)
      (noun := auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
      (amount := amountWord)
      (start := auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
      (finish := auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
      (bidder := auctionPackedBidderWord
        (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
      (settled := auctionPackedSettledEVMReturnWord
        (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
      (caller := callerWord) (owner := ownerWord) (outPay := outPay)
      (kFallback := kFallback) (CFallback := CFallback)
      hwethCodeE
      (by
        simpa [amountWord, ownerWord, callerWord, memPayRetDyn] using hrdFallbackDyn)
  by_cases hdepositBalance :
      amountWord ≤ (σPay.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
  · obtain ⟨cADep, σDep, zDep, outDep, AInDep, callGasDep,
        kAfterDep, CAfterDep, hThetaDepPack, hrdAfterDepRaw, houtDepSize⟩ :=
      RD.callValueMade
        (by
          simpa [amountWord, ownerWord, callerWord, memPayRetDyn, awPayRetDyn,
            freePtrDyn, memDeposit, wethWord] using hrdDepositCall)
        (by native_decide) _hperm
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
          simpa [evmPayE, initState, accountAddress_roundtrip, _hperm,
            memDeposit, memPayRetDyn, awPayRetDyn, freePtrDyn, wethWord] using hThetaDep)
        (by simpa [evmPayE, initState] using hdepositBalance)
        (by
          simp [evmPayE, evmTfE, initState]
          intro hbad
          have hbadVal : I.depth.val = 1024 := by
            exact congrArg Fin.val hbad
          omega)
        (by simpa [evmPayE, evmPay] using hpostPayAccounts)
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark, evmEnter, evmS,
            auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
            initState, auctionStorageStore_σ₀])
        (by simp [evmPayE, evmPay])
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark, evmEnter, evmS,
            auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
            initState, auctionStorageStore_genesisBlockHeader])
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark, evmEnter, evmS,
            auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
            initState, auctionStorageStore_blocks])
        (by
          simp [evmPayE, evmPay, evmTfE, evmTf, evmMark, evmEnter, evmS,
            auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
            initState, storageStore_executionEnv])
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
      exact transferBranchPayoutFailureEmptyFromCallDepositMadeFailureCase
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (cA' := cA') (cAPay := cAPay) (cADep := cADep)
        (σ' := σ') (σ'_solm := σ'_solm)
        (σPay := σPay) (σPaySolm := σPaySolm)
        (σDep := σDep) (σDepSolm := σDepSolm)
        (A' := A') (A'_solm := A'_solm)
        (APay := APay) (APaySolm := APaySolm) (ADepSolm := ADepSolm)
        (o := o) (outPay := outPay) (outDep := outDep)
        (kAfterDep := kAfterDep) (CAfterDep := CAfterDep)
        _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm
        hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsCodeSolmEval
        hcallSolm hamountEq hamountSolm hpaySolm hpostPay hdepositRawFalse
        (by
          simpa [amountWord, ownerWord, callerWord, memPayRetDyn, awPayRetDyn,
            freePtrDyn, memDeposit, wethWord] using hrdAfterDepRaw)
        houtDepSize hwethCodeE
    · have hdepositRawTrue :
          callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
            (Int.ofNat amountWord.toNat)
            (memDeposit.readWithPadding freePtrDyn.toNat 4)
            (true, evmDeposit, outDep) true := by
        simpa [evmDeposit] using hdepositSolmRaw
      have hwethSlotPay :
          auctionSlotWord ⟨202⟩ σPay I =
            auctionSlotWord ⟨202⟩ σPaySolm I := by
        exact accountMapEquiv_storage_findD hpostPayAccounts I.codeOwner ⟨202⟩ ⟨0⟩
      have hwethWordEq :
          UInt256.land
              (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask =
            wethWord := by
        have hslot :
            Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩ =
              auctionSlotWord ⟨202⟩ σPaySolm I := by
          simp [evmPay, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, auctionSlotWord, htfOwner]
        unfold wethWord
        rw [hslot, ← hwethSlotPay]
      have hwethTarget :
          EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat)) =
            AccountAddress.ofUInt256 wethWord := by
        exact transferBranchWethTarget (σ := σPay) (I := I) hwethWordEq
          (by simp [wethWord])
      have hdeposit :
          typedCallViaEVM auctionConfig evmPay
            (EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat))) "deposit"
            (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat) []
            (true, evmDeposit, outDep) true := by
        refine ⟨memDeposit.readWithPadding freePtrDyn.toNat 4, ?_, ?_⟩
        · exact hdepositEncode
        · rw [hwethTarget, ← hamountEq]
          exact hdepositRawTrue
      have hrdAfterDep :
          RD auctionBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3432⟩
            [⟨1⟩, ⟨4⟩ + freePtrDyn, amountWord, ⟨3504541104⟩,
              wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
              ⟨2471⟩, ⟨413⟩, auctionSelWord I]
            memDeposit (auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn)
            outDep (cADep, σDep) kAfterDep CAfterDep := by
        have hmin :
            (min (⟨0⟩ : UInt256) (UInt256.ofNat outDep.size)).toNat = 0 := by
          have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat outDep.size := by
            show (0 : Nat) ≤ (UInt256.ofNat outDep.size).val.val
            exact Nat.zero_le _
          simp [min, hle]
        simpa [amountWord, ownerWord, callerWord, memPayRetDyn, awPayRetDyn,
          freePtrDyn, memDeposit, wethWord, hmin, byteArray_write_len_zero]
          using hrdAfterDepRaw
      have hwethCodeSolmTransfer :
          0 < (UInt256.ofNat (((evmPay.lookupAccount
            (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat := by
        exact transferBranchWethLookupCodePos
          (σ := σPay) (τ := σPaySolm) (evm := evmPay)
          (wethWord := wethWord) hpostPayAccounts
          (by simp [evmPay]) hwethWordEq
          (by simpa [wethWord] using hwethCodeE)
      have hdepositOwner : evmDeposit.executionEnv.codeOwner = I.codeOwner := by
        simp [evmDeposit, evmPay, evmTf, evmMark, evmEnter, evmS,
          auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
          initState, storageStore_executionEnv]
      have hwethSlotDep :
          auctionSlotWord ⟨202⟩ σDep I =
            auctionSlotWord ⟨202⟩ σDepSolm I := by
        exact accountMapEquiv_storage_findD hpostDep I.codeOwner ⟨202⟩ ⟨0⟩
      let wethTransfer := UInt256.land (auctionSlotWord ⟨202⟩ σDep I) solcAddrMask
      have hwethTargetTransfer :
          EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
                solcAddrMask).toNat)) =
            AccountAddress.ofUInt256 wethTransfer := by
        exact transferBranchWethTarget
          (σ := σDep) (I := I)
          (by
            have hslot :
                Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩ =
                  auctionSlotWord ⟨202⟩ σDepSolm I := by
              rw [hdepositOwner]
              simp [evmDeposit, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, auctionSlotWord]
            unfold wethTransfer
            rw [hslot, ← hwethSlotDep])
          (by simp [wethTransfer])
      have hownerMask : UInt256.land solcAddrMask ownerWord = ownerWord := by
        rw [u256_land_comm solcAddrMask ownerWord]
        simpa [ownerWord] using
          solcAddrMask_clean
            (solcAddrMask_result_canonical (auctionSlotWord ⟨151⟩ σ' I))
      have hownerCanon :
          (UInt256.land solcAddrMask ownerWord).toNat < EVM.addressModulus := by
        rw [u256_land_comm solcAddrMask ownerWord]
        exact solcAddrMask_result_canonical ownerWord
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
      have hownerAddr :
          auctionOwnerAddressAt evmTf = AccountAddress.ofUInt256 ownerWord := by
        have hownerAddressId :
            EVM.address (auctionOwnerAddressAt evmTf) = auctionOwnerAddressAt evmTf := by
          apply Fin.ext
          simp [EVM.address, EVM.uintN, EVM.twoPow, AccountAddress.size]
        exact hownerAddressId.symm.trans hownerEq
      have htransferEncode :
          auctionConfig.externalABI.encode? "transfer"
            [.address (auctionOwnerAddressAt evmTf),
              .int (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)] =
            some
              ((auctionSettleAuctionDynTransferMem memDeposit freePtrDyn amountWord ownerWord)
                |>.readWithPadding freePtrDyn.toNat 68) := by
        have hfreePtrDyn : freePtrDyn = (⟨352⟩ : UInt256) := by
          simpa [memPayRetDyn, awPayRetDyn, freePtrDyn, callerWord] using
            transferBranchTransferFromPayoutLoopDynMload64Aw14
              (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
              amountWord
              (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
              (auctionPackedBidderWord
                (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
              (auctionPackedSettledEVMReturnWord
                (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
              callerWord
        have henc :=
          transferBranchTransferFromPayoutLoopDynTransferEncodeEqAw14
            (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
            amountWord
            (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
            (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
            (auctionPackedBidderWord
              (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
            (auctionPackedSettledEVMReturnWord
              (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
            callerWord ownerWord hownerCanon
        rw [hownerMask] at henc
        rw [← hamountEq]
        rw [hownerAddr]
        rw [hfreePtrDyn]
        simpa [memPayRetDyn, awPayRetDyn, memDeposit, callerWord] using henc
      exact transferBranchPayoutFailureEmptyFromCallDepositMadeSuccessCase
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmS := evmS) (evmTf := evmTf) (evmPay := evmPay)
        (evmDeposit := evmDeposit) (evmDepositE := evmDepositE)
        (outTf := o) (outPay := outPay) (outDeposit := outDep)
        (cADep := cADep)
        (noun := auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
        (amount := amountWord)
        (start := auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
        (finish := auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
        (bidder := auctionPackedBidderWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
        (settled := auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
        (caller := callerWord) (owner := ownerWord) (wethBefore := wethWord)
        (kAfterDep := kAfterDep) (CAfterDep := CAfterDep)
        _hcode _hperm hdispatch hdecode rfl (by simpa [evmS, initState] using hwv)
        hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
        hamountSolm hdepth hpaySolm hdeposit hwethCodeSolmTransfer hdepositOwner
        (by simp [evmDepositE, evmPayE, evmTfE, initState])
        (by simp [evmDepositE])
        (by simp [evmDepositE, evmPayE, evmTfE, initState])
        (by simp [evmDepositE, evmPayE, evmTfE, initState])
        (by simp [evmDepositE, evmPayE, evmTfE, initState])
        (by
          simp [evmDepositE, evmPayE, evmTfE, initState]
          intro hbad
          have hbadVal : I.depth.val = 1024 := by
            exact congrArg Fin.val hbad
          omega)
        (by simpa [evmDepositE, evmDeposit] using hpostDep)
        (by
          simp [evmDepositE, evmDeposit, evmPayE, evmPay, evmTfE, evmTf,
            evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState, auctionStorageStore_σ₀])
        (by simp [evmDepositE, evmDeposit])
        (by
          simp [evmDepositE, evmDeposit, evmPayE, evmPay, evmTfE, evmTf,
            evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState, auctionStorageStore_genesisBlockHeader])
        (by
          simp [evmDepositE, evmDeposit, evmPayE, evmPay, evmTfE, evmTf,
            evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState, auctionStorageStore_blocks])
        (by
          simp [evmDepositE, evmDeposit, evmPayE, evmPay, evmTfE, evmTf,
            evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
            auctionSettleAuctionEnterState, initState, storageStore_executionEnv])
        (by
          simpa [memPayRetDyn, awPayRetDyn, freePtrDyn, memDeposit] using
            htransferEncode)
        (by simpa [evmDepositE, wethTransfer] using hwethTargetTransfer)
        (by
          simpa [amountWord, ownerWord, callerWord, memPayRetDyn, awPayRetDyn,
            freePtrDyn, memDeposit, evmDepositE] using hrdAfterDep)
  · exact transferBranchPayoutFailureEmptyFromCallDepositInsufficientCase
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (cA' := cA') (cAPay := cAPay)
      (σ' := σ') (σ'_solm := σ'_solm)
      (σPay := σPay) (σPaySolm := σPaySolm)
      (A' := A') (A'_solm := A'_solm)
      (APay := APay) (APaySolm := APaySolm)
      (o := o) (outPay := outPay) (gasWord := gasWord) (kDep := kDep) (CDep := CDep)
      _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm hstartSolm
      hsettledSolm htimeSolmLe hbidderSolm hnounsCodeSolmEval hcallSolm
      hamountEq hamountSolm hdepth hpaySolm hpostPay
      (by
        simpa [amountWord, ownerWord, callerWord, memPayRetDyn, awPayRetDyn,
          freePtrDyn, memDeposit, wethWord] using hrdDepositCall)
      hwethCodeE
      (by simpa [amountWord] using hdepositBalance)

end Auction

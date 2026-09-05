import Benchmarks.Auction.SettleAuctionTransferBranchPayoutNonemptyCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutFailureEmptyWethDepositSuccessTransferCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay cADep : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm σDep σDepSolm : AccountMap}
    {A' A'_solm APay APaySolm ADep ADepSolm : Substate}
    {o outPay outDep : ByteArray} {kPay CPay kAfterDep CAfterDep : ℕ}
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
    (hpostDep : accountMapEquiv σDep σDepSolm)
    (hdepositRawTrue :
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
      let memDeposit :=
        auctionSettleAuctionWethDepositMem
          (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          amountWord
          (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
      let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
      let evmDeposit :=
        { evmPay with
          accountMap := σDepSolm,
          substate := ADepSolm,
          createdAccounts := cADep }
      callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
        (Int.ofNat amountWord.toNat) (memDeposit.readWithPadding 352 4)
        (true, evmDeposit, outDep) true)
    (hrdAfterDepRaw :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      let memDeposit :=
        auctionSettleAuctionWethDepositMem
          (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          amountWord
          (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
      let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
      let len := (min (⟨0⟩ : UInt256) (UInt256.ofNat outDep.size)).toNat
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨3432⟩
        [⟨1⟩, ⟨356⟩, amountWord, ⟨3504541104⟩,
          wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        (outDep.write 0 memDeposit (⟨352⟩ : UInt256).toNat len)
        (UInt256.ofNat
          (MachineState.M
            (MachineState.M (UInt256.ofNat 12).toNat
              (⟨352⟩ : UInt256).toNat (⟨4⟩ : UInt256).toNat)
            (⟨352⟩ : UInt256).toNat len))
        outDep (cADep, σDep) kAfterDep CAfterDep)
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
  let memDeposit :=
    auctionSettleAuctionWethDepositMem
      (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
      amountWord
      (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
      (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
      (auctionPackedBidderWord
        (auctionAuctionPackedWord
          (auctionSettleAuctionEnterMap σ_evm I) I))
      (auctionPackedSettledEVMReturnWord
        (auctionAuctionPackedWord
          (auctionSettleAuctionEnterMap σ_evm I) I))
  let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
  have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
    exact hpostPay
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
    have hslot :=
      accountMapEquiv_storage_findD hpostTf I.codeOwner ⟨151⟩
        (⟨0⟩ : UInt256)
    rw [htfOwner]
    simpa [evmTf, auctionSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hslot
  have hownerEq :
      EVM.address (auctionOwnerAddressAt evmTf) =
        AccountAddress.ofUInt256 ownerWord := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    apply Fin.ext
    simp [auctionOwnerAddressAt, ownerWord, hownerLoad, EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt
      (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
          solcAddrMask_result_canonical
            (Solm.EVM.storageLoad evmTf evmTf.executionEnv.codeOwner ⟨151⟩))
  have hwethWordEq :
      UInt256.land
          (Solm.EVM.storageLoad evmPay
            evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask =
        wethWord := by
    simpa [wethWord] using
      transferBranchWethWordAt
        (σ := σPay) (τ := σPaySolm) (evm := evmPay)
        (I := I) hpostPayAccounts
        (by simp [evmPay])
        (by simpa [evmPay] using htfOwner)
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
  have hwethTarget :
      EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat)) =
        AccountAddress.ofUInt256 wethWord := by
    exact transferBranchWethTarget
      (σ := σPay) (I := I) hwethWordEq (by simp [wethWord])
  have hdeposit :
      typedCallViaEVM auctionConfig evmPay
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "deposit"
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat) []
        (true, evmDeposit, outDep) true := by
    refine ⟨memDeposit.readWithPadding 352 4, ?_, ?_⟩
    · simpa [memDeposit] using
        auctionSettleAuctionWethDepositEncode_eq
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
    · rw [hwethTarget]
      have hamountEqLocal : amountWord = auctionSettleAuctionAmount evmEnter := by
        simpa [amountWord, evmEnter, evmS] using hamountEq
      rw [← hamountEqLocal]
      exact hdepositRawTrue
  have hrdAfterDep :
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨3432⟩
        [⟨1⟩, ⟨356⟩, amountWord, ⟨3504541104⟩,
          wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memDeposit (UInt256.ofNat 12) outDep
        (cADep, σDep) kAfterDep CAfterDep := by
    have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat outDep.size)).toNat =
          0 := by
      have hle :
          (⟨0⟩ : UInt256) ≤ UInt256.ofNat outDep.size := by
        show (0 : Nat) ≤ (UInt256.ofNat outDep.size).val.val
        exact Nat.zero_le _
      simp [min, hle]
    have hawDep :
        UInt256.ofNat
            (MachineState.M
              (MachineState.M (UInt256.ofNat 12).toNat
                (⟨352⟩ : UInt256).toNat
                (⟨4⟩ : UInt256).toNat)
              (⟨352⟩ : UInt256).toNat
              (⟨0⟩ : UInt256).toNat) =
          UInt256.ofNat 12 := by
      native_decide
    simpa [amountWord, ownerWord, memDeposit, wethWord, hmin,
      byteArray_write_len_zero, hawDep] using hrdAfterDepRaw
  obtain ⟨gasTransfer, kTransferCall, CTransferCall,
      hrdTransferCall⟩ :=
    auctionSettleAuctionDepositSuccessToTransferCall
      hrdAfterDep
  let memTransfer :=
    auctionSettleAuctionWethTransferMem
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
      ownerWord
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
        (⟨352⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
      (g'' := gTransfer'') (callGas := callGasTransfer)
      (valueWord := ⟨0⟩) (targetWord := wethTransferWord)
      (by
        simpa [evmTransferE, evmDepositE, evmPayE,
          evmTfE, initState, memTransfer,
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
        (memTransfer.readWithPadding
          (⟨352⟩ : UInt256).toNat
          (⟨68⟩ : UInt256).toNat)
        (zTransfer, evmTransfer, outTransfer) true := by
    simpa [evmTransfer] using htransferSolmRaw
  have hdepositOwner :
      evmDeposit.executionEnv.codeOwner = I.codeOwner := by
    simp [evmDeposit, evmPay, evmTf, evmMark, evmEnter, evmS,
      auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState,
      storageStore_executionEnv]
  have hwethWordTransferEq :
      UInt256.land
          (Solm.EVM.storageLoad evmDeposit
            evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask =
        wethTransferWord := by
    simpa [wethTransferWord] using
      transferBranchWethWordAt
        (σ := σDep) (τ := σDepSolm) (evm := evmDeposit)
        (I := I) hpostDep
        (by simp [evmDeposit])
        hdepositOwner
  have hwethTargetTransfer :
      EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmDeposit
              evmDeposit.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat)) =
        AccountAddress.ofUInt256 wethTransferWord := by
    exact transferBranchWethTarget
      (σ := σDep) (I := I) hwethWordTransferEq
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
    refine ⟨memTransfer.readWithPadding 352 68, ?_, ?_⟩
    · have henc :=
        auctionSettleAuctionWethTransferEncode_eq
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
          ownerWord hownerCanon
      rw [hownerMask] at henc
      have hamountEqLocal : amountWord = auctionSettleAuctionAmount evmEnter := by
        simpa [amountWord, evmEnter, evmS] using hamountEq
      have hamountNat :
          amountWord.toNat = (auctionSettleAuctionAmount evmEnter).toNat := by
        rw [hamountEqLocal]
      rw [hamountNat] at henc
      simpa [memTransfer, hownerAddr] using henc
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
    exact transferBranchWethLookupCodePos
      (σ := σPay) (τ := σPaySolm) (evm := evmPay)
      (wethWord := wethWord)
      hpostPayAccounts (by simp [evmPay]) hwethWordEq
      (by simpa [wethWord] using hwethCodeE)
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
    have hwethCodeSolm :
        0 < (UInt256.ofNat (((evmPay.lookupAccount
          (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))).option 0
            (fun acc => acc.code.size)))).toNat := by
      exact hwethCodeSolmTransfer
    have hrdTransferFailRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
            A I) := by
      exact auctionCallSuccessGuardMissingPush0
        (pc := ⟨3518⟩) (okPc := ⟨3532⟩)
        (status := ⟨0⟩)
        (R := [⟨420⟩, ⟨2835717307⟩, wethTransferWord,
          amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
          ⟨413⟩, auctionSelWord I])
        (by
          simpa [amountWord, ownerWord, memTransfer,
            wethTransferWord] using hrdAfterTransferRaw)
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
        hamountSolm hpaySolm hwethCodeSolm hdeposit
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
    let transferRetWord :=
      UInt256.ofNat
        (fromByteArrayBigEndian (outTransfer.extract 0 32))
    by_cases hshortTransfer : outTransfer.size < 32
    · have htransferDec :
          auctionConfig.externalABI.decode? "transfer"
            outTransfer = none :=
        auctionExternalABI_decode_transfer_none_short
          hshortTransfer
      have hrdTransferDecodeRev :
          RDrev auctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀
              (Sat256.ofUInt256 g) A I) := by
        exact auctionSettleAuctionTransferReturnShortRevert
          (amount := amountWord) (owner := ownerWord)
          (weth := wethTransferWord)
          (rd := by
            simpa [amountWord, ownerWord, memTransfer,
              wethTransferWord] using hrdAfterTransferRaw)
          hshortTransfer
          (by
            simpa [memTransfer] using
              auctionSettleAuctionTransferReturnMload64_any
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
                ownerWord houtTransferSize)
      have hbody :
          ExecTransitionBody auctionConfig auctionContract
            evmS ∅ settleAuctionTransition.body .reverted :=
        auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
          evmS evmTf evmPay evmDeposit evmTransfer
          (by simpa [evmS, initState] using hwv)
          hpausedSolm hstatusSolm hstartSolm hsettledSolm
          htimeSolmLe hbidderSolm hnounsCodeSolmEval
          (by
            simpa [evmTf, evmMark, evmEnter] using
              hcallSolm)
          hamountSolm hpaySolm hwethCodeSolmTransfer hdeposit
          htransferTrue htransferDec
      exact hrdTransferDecodeRev.reEquivExecutionRevert _hcode
        hdispatch hdecode hbody
    · have houtTransfer32 : 32 ≤ outTransfer.size := by
        omega
      by_cases hhugeTransfer :
          (2 : Nat) ^ 255 ≤ outTransfer.size
      · have htransferDec :
            auctionConfig.externalABI.decode? "transfer"
              outTransfer = none :=
          auctionExternalABI_decode_transfer_none_huge
            hhugeTransfer
        have hrdTransferDecodeRev :
            RDrev auctionBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀
                (Sat256.ofUInt256 g) A I) := by
          exact auctionSettleAuctionTransferReturnHugeRevert
            (amount := amountWord) (owner := ownerWord)
            (weth := wethTransferWord)
            (rd := by
              simpa [amountWord, ownerWord, memTransfer,
                wethTransferWord] using hrdAfterTransferRaw)
            hhugeTransfer houtTransferSize
            (by
              simpa [memTransfer] using
                auctionSettleAuctionTransferReturnMload64_any
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
                  ownerWord houtTransferSize)
        have hbody :
            ExecTransitionBody auctionConfig auctionContract
              evmS ∅ settleAuctionTransition.body .reverted :=
          auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
            evmS evmTf evmPay evmDeposit evmTransfer
            (by simpa [evmS, initState] using hwv)
            hpausedSolm hstatusSolm hstartSolm hsettledSolm
            htimeSolmLe hbidderSolm hnounsCodeSolmEval
            (by
              simpa [evmTf, evmMark, evmEnter] using
                hcallSolm)
            hamountSolm hpaySolm hwethCodeSolmTransfer hdeposit
            htransferTrue htransferDec
        exact hrdTransferDecodeRev.reEquivExecutionRevert
          _hcode hdispatch hdecode hbody
      · have houtTransferHi :
          outTransfer.size < (2 : Nat) ^ 255 :=
          Nat.lt_of_not_ge hhugeTransfer
        have hfinishReturn {transferOk : Bool}
            (htransferDec :
              auctionConfig.externalABI.decode? "transfer"
                outTransfer = some [.bool transferOk])
            (hret :
              RDret auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀
                  (Sat256.ofUInt256 g) A I)
                (cATransfer,
                  auctionSettleAuctionExitMap σTransfer I)
                ByteArray.empty) := by
          exact
            auctionSettleAuctionTransferFromSuccessReturnRuntime
              (evm := evmS) (evmTransferFrom := evmTf)
              (evmPay := evmPay) (evmDeposit := evmDeposit)
              (evmTransfer := evmTransfer)
              (transferOk := transferOk)
              _hcode hdispatch hdecode rfl hret
              (by simpa [evmS, initState] using hwv)
              hpausedSolm hstatusSolm hstartSolm hsettledSolm
              htimeSolmLe hbidderSolm hnounsCodeSolmEval
              (by
                simpa [evmTf, evmMark, evmEnter] using
                  hcallSolm)
              hamountSolm hpaySolm hwethCodeSolmTransfer
              hdeposit htransferTrue htransferDec
              (by
                simp [auctionSettleAuctionExitState, evmTransfer,
                  storageStore_createdAccounts])
              (by
                simp [evmTransfer, evmDeposit, evmPay, evmTf,
                  evmMark, evmEnter, evmS,
                  auctionSettleAuctionMarkSettledState,
                  auctionSettleAuctionEnterState, initState,
                  storageStore_executionEnv])
              (by
                simpa [evmTransferE, evmTransfer] using
                  hpostTransfer)
        by_cases htransferZero : transferRetWord = ⟨0⟩
        · have htransferDec :
              auctionConfig.externalABI.decode? "transfer"
                outTransfer = some [.bool false] :=
            auctionExternalABI_decode_transfer_false
              houtTransfer32 houtTransferHi htransferZero
          obtain ⟨_, _, _, _, hrdEvent⟩ :=
            auctionSettleAuctionTransferReturnBoolToEvent
              (amount := amountWord) (owner := ownerWord)
              (weth := wethTransferWord)
              (retWord := transferRetWord)
              (rd := by
                simpa [amountWord, ownerWord, memTransfer,
                  wethTransferWord] using hrdAfterTransferRaw)
              houtTransfer32 houtTransferHi
              (by
                simpa [memTransfer] using
                  auctionSettleAuctionTransferReturnMload64
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
                    ownerWord houtTransfer32 houtTransferSize)
              (by
                simpa [transferRetWord, memTransfer] using
                  auctionSettleAuctionTransferReturnMload352
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
                    ownerWord houtTransfer32 houtTransferSize)
              (Or.inl htransferZero)
          have hret :
              RDret auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀
                  (Sat256.ofUInt256 g) A I)
                (cATransfer,
                  auctionSettleAuctionExitMap σTransfer I)
                ByteArray.empty :=
            auctionSettleAuctionEventToReturn _hperm hrdEvent
          exact hfinishReturn htransferDec hret
        · by_cases htransferOne : transferRetWord = ⟨1⟩
          · have htransferDec :
                auctionConfig.externalABI.decode? "transfer"
                  outTransfer = some [.bool true] :=
              auctionExternalABI_decode_transfer_true
                houtTransfer32 houtTransferHi htransferOne
            obtain ⟨_, _, _, _, hrdEvent⟩ :=
              auctionSettleAuctionTransferReturnBoolToEvent
                (amount := amountWord) (owner := ownerWord)
                (weth := wethTransferWord)
                (retWord := transferRetWord)
                (rd := by
                  simpa [amountWord, ownerWord, memTransfer,
                    wethTransferWord] using hrdAfterTransferRaw)
                houtTransfer32 houtTransferHi
                (by
                  simpa [memTransfer] using
                    auctionSettleAuctionTransferReturnMload64
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
                      ownerWord houtTransfer32 houtTransferSize)
                (by
                  simpa [transferRetWord, memTransfer] using
                    auctionSettleAuctionTransferReturnMload352
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
                      ownerWord houtTransfer32 houtTransferSize)
                (Or.inr htransferOne)
            have hret :
                RDret auctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀
                    (Sat256.ofUInt256 g) A I)
                  (cATransfer,
                    auctionSettleAuctionExitMap σTransfer I)
                  ByteArray.empty :=
              auctionSettleAuctionEventToReturn _hperm hrdEvent
            exact hfinishReturn htransferDec hret
          · have htransferDec :
                auctionConfig.externalABI.decode? "transfer"
                  outTransfer = none :=
              auctionExternalABI_decode_transfer_none_noncanon
                houtTransfer32 houtTransferHi htransferZero
                htransferOne
            have hrdTransferDecodeRev :
                RDrev auctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀
                    (Sat256.ofUInt256 g) A I) := by
              exact auctionSettleAuctionTransferReturnNoncanonRevert
                (amount := amountWord) (owner := ownerWord)
                (weth := wethTransferWord)
                (retWord := transferRetWord)
                (rd := by
                  simpa [amountWord, ownerWord, memTransfer,
                    wethTransferWord] using hrdAfterTransferRaw)
                houtTransfer32 houtTransferHi
                (by
                  simpa [memTransfer] using
                    auctionSettleAuctionTransferReturnMload64
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
                      ownerWord houtTransfer32 houtTransferSize)
                (by
                  simpa [transferRetWord, memTransfer] using
                    auctionSettleAuctionTransferReturnMload352
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
                      ownerWord houtTransfer32 houtTransferSize)
                htransferZero htransferOne
            have hbody :
                ExecTransitionBody auctionConfig auctionContract
                  evmS ∅ settleAuctionTransition.body
                  .reverted :=
              auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
                evmS evmTf evmPay evmDeposit evmTransfer
                (by simpa [evmS, initState] using hwv)
                hpausedSolm hstatusSolm hstartSolm
                hsettledSolm htimeSolmLe hbidderSolm
                hnounsCodeSolmEval
                (by
                  simpa [evmTf, evmMark, evmEnter] using
                    hcallSolm)
                hamountSolm hpaySolm hwethCodeSolmTransfer
                hdeposit htransferTrue htransferDec
            exact hrdTransferDecodeRev.reEquivExecutionRevert
              _hcode hdispatch hdecode hbody


end Auction

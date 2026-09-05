import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyCodeDepositMadeFailure
import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyCodeDepositMadeSuccess

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutFailureEmptyWethCodeDepositMadeAfterCallCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm : AccountMap}
    {A' A'_solm APay APaySolm : Substate}
    {o outPay : ByteArray} {kPay CPay : ℕ}
    {gasWord : UInt256} {kDep CDep : ℕ}
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
    (hrdDepositCall :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      let memDeposit :=
        auctionSettleAuctionWethDepositMem
          (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          amountWord
          (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionPackedBidderWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (auctionPackedSettledEVMReturnWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
      let wethWord := UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3431⟩
        [gasWord, wethWord, amountWord, ⟨352⟩, ⟨4⟩, ⟨352⟩, ⟨0⟩,
          ⟨356⟩, amountWord, ⟨3504541104⟩, wethWord, amountWord, ownerWord,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memDeposit (UInt256.ofNat 12) outPay (cAPay, σPay) kDep CDep)
    (hwethCodeE :
      Reasoning.Theory.uniswapExtCodeSizeWord σPay
          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask) ≠
        ⟨0⟩)
    (hdepositBalance :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      amountWord ≤ (σPay.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))) :
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
  let wethWord :=
    UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
  have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
    exact hpostPay
  obtain ⟨cADep, σDep, zDep, outDep, AInDep, callGasDep,
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
      (calldata := memDeposit.readWithPadding 352 4)
      (g'' := gDep'') (callGas := callGasDep)
      (valueWord := amountWord) (targetWord := wethWord)
      (by
        simpa [evmPayE, initState, accountAddress_roundtrip,
          _hperm, memDeposit, wethWord] using hThetaDep)
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
          (memDeposit.readWithPadding 352 4)
          (false, evmDeposit, outDep) true := by
      simpa [evmDeposit] using hdepositSolmRaw
    exact transferBranchPayoutFailureEmptyWethCodeDepositMadeFailureCase
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (cA' := cA') (cAPay := cAPay) (cADep := cADep)
      (σ' := σ') (σ'_solm := σ'_solm)
      (σPay := σPay) (σPaySolm := σPaySolm)
      (σDep := σDep) (σDepSolm := σDepSolm)
      (A' := A') (A'_solm := A'_solm)
      (APay := APay) (APaySolm := APaySolm)
      (ADep := ADep) (ADepSolm := ADepSolm)
      (o := o) (outPay := outPay) (outDep := outDep)
      (kAfterDep := kAfterDep) (CAfterDep := CAfterDep)
      _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsCodeSolmEval
      hcallSolm hamountEq hamountSolm hpaySolm hpostPay hdepositRawFalse
      hrdAfterDepRaw houtDepSize hwethCodeE
  · have hdepositRawTrue :
        callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
          (Int.ofNat amountWord.toNat)
          (memDeposit.readWithPadding 352 4)
          (true, evmDeposit, outDep) true := by
      simpa [evmDeposit] using hdepositSolmRaw
    exact transferBranchPayoutFailureEmptyWethCodeDepositMadeSuccessCase
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (cA' := cA') (cAPay := cAPay) (cADep := cADep)
      (σ' := σ') (σ'_solm := σ'_solm)
      (σPay := σPay) (σPaySolm := σPaySolm)
      (σDep := σDep) (σDepSolm := σDepSolm)
      (A' := A') (A'_solm := A'_solm)
      (APay := APay) (APaySolm := APaySolm)
      (ADep := ADep) (ADepSolm := ADepSolm)
      (o := o) (outPay := outPay) (outDep := outDep)
      (kPay := kPay) (CPay := CPay)
      (kAfterDep := kAfterDep) (CAfterDep := CAfterDep)
      _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm
      hnounsCodeSolmEval hcallSolm hpostTf hamountEq hamountSolm
      hdepth hpaySolm hpostPay hpostDep hdepositRawTrue
      hrdAfterDepRaw hwethCodeE

end Auction

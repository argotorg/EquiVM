import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyCodeDepositMadeAfterCall

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutFailureEmptyWethCodeCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm : AccountMap}
    {A' A'_solm APay APaySolm : Substate}
    {o outPay : ByteArray} {kPay CPay kFallback CFallback : ℕ}
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
    (hrdFallback :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3347⟩
        [⟨0⟩, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        (auctionSettleAuctionPayoutLoopMem
          (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          amountWord
          (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionPackedBidderWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (auctionPackedSettledEVMReturnWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I)))
        (UInt256.ofNat 12) outPay (cAPay, σPay) kFallback CFallback)
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
  obtain ⟨gasWord, kDep, CDep, hrdDepositCall⟩ :
      ∃ gasWord kDep CDep,
        RD auctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3431⟩
          [gasWord, wethWord, amountWord, ⟨352⟩, ⟨4⟩, ⟨352⟩, ⟨0⟩,
            ⟨356⟩, amountWord, ⟨3504541104⟩, wethWord, amountWord, ownerWord,
            ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
          memDeposit (UInt256.ofNat 12) outPay (cAPay, σPay) kDep CDep := by
    simpa [memDeposit, wethWord, amountWord, ownerWord] using
      auctionSettleAuctionPayoutFallbackToDepositCall hwethCodeE hrdFallback
  have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
    simpa [evmPayE, evmPay] using hpostPay
  by_cases hdepositBalance :
      amountWord ≤
        (σPay.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
  · exact transferBranchPayoutFailureEmptyWethCodeDepositMadeAfterCallCase
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (cA' := cA') (cAPay := cAPay)
      (σ' := σ') (σ'_solm := σ'_solm)
      (σPay := σPay) (σPaySolm := σPaySolm)
      (A' := A') (A'_solm := A'_solm)
      (APay := APay) (APaySolm := APaySolm)
      (o := o) (outPay := outPay) (kPay := kPay) (CPay := CPay)
      (gasWord := gasWord) (kDep := kDep) (CDep := CDep)
      (hrdDepositCall := hrdDepositCall)
      (hwethCodeE := hwethCodeE)
      (hdepositBalance := hdepositBalance)
      _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm
      hnounsCodeSolmEval hcallSolm hpostTf hamountEq hamountSolm
      hdepth hpaySolm hpostPay
  · obtain ⟨kAfterDep, CAfterDep, hrdAfterDepRaw⟩ :=
      RD.callValueInsufficientBalance hrdDepositCall _hperm
        (by native_decide)
        (by simpa [amountWord] using hdepositBalance)
        hdepth
        (by
          change 12 ≤ 1024
          native_decide)
    have hmin :
        (min (⟨0⟩ : UInt256)
          (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
      native_decide
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
    have hrdAfterDep :
        RD auctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I)
          ⟨3432⟩
          [⟨0⟩, ⟨356⟩, amountWord, ⟨3504541104⟩,
            wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
            ⟨2471⟩, ⟨413⟩, auctionSelWord I]
          memDeposit (UInt256.ofNat 12) ByteArray.empty
          (cAPay, σPay) kAfterDep CAfterDep := by
      have htmp := hrdAfterDepRaw
      rw [hmin, byteArray_write_len_zero, hawDep] at htmp
      simpa [amountWord, ownerWord, memDeposit, wethWord] using htmp
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
          (memDeposit.readWithPadding 352 4)
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
      · rw [hwethTarget, ← hamountEq]
        exact hdepositRawFalse
    have hrdDepositFailRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I) := by
      exact auctionCallSuccessGuardMissingPush0
        (pc := ⟨3432⟩) (okPc := ⟨3446⟩)
        (status := ⟨0⟩)
        (R := [⟨356⟩, amountWord, ⟨3504541104⟩, wethWord,
          amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
          ⟨413⟩, auctionSelWord I])
        (by
          simpa [amountWord, ownerWord, memDeposit, wethWord] using
            hrdAfterDep)
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

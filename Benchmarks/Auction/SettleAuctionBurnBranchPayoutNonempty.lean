import Benchmarks.Auction.SettleAuctionBurnBranchPayoutNonemptyTransfer

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionBodyBurnPayoutFailureNonemptyCase
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
        (auctionSettleAuctionPayoutLoopMem
          (auctionAuctionNounWord σ1 I)
          amountWord
          (auctionAuctionStartWord σ1 I)
          (auctionAuctionEndWord σ1 I)
          (auctionPackedBidderWord (auctionAuctionPackedWord σ1 I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ1 I)))
        (UInt256.ofNat 12) outPay (cAPay, σPay) kPay CPay) :
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
  obtain ⟨memPayRet, awPayRet, _, _, hrdFallback⟩ :=
    auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallback
      houtPaySize houtZero
      (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
  by_cases hwethCodeE :
      Reasoning.Theory.uniswapExtCodeSizeWord σPay
          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I)
            solcAddrMask) ≠
        ⟨0⟩
  · obtain ⟨kFallbackDyn, CFallbackDyn, hrdFallbackDyn⟩ :=
      auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallbackFixed
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
        (owner := ownerWord)
        houtPaySize houtZero
        (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
    have hfreeStable :
        auctionSettleAuctionDynMload64
            (auctionSettleAuctionDynDepositMem
              (auctionSettleAuctionPayoutNonemptyMemCopy
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
                outPay)
              (auctionSettleAuctionPayoutNonemptyAwCopy outPay))
            (auctionSettleAuctionDynDepositAw
              (auctionSettleAuctionPayoutNonemptyMemCopy
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
                outPay)
              (auctionSettleAuctionPayoutNonemptyAwCopy outPay)) =
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionPayoutNonemptyMemCopy
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
              outPay)
            (auctionSettleAuctionPayoutNonemptyAwCopy outPay) := by
      exact auctionSettleAuctionPayoutNonemptyDepositFreeStable
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
    have hdepositLen :
        UInt256.sub
            (⟨4⟩ +
              auctionSettleAuctionDynMload64
                (auctionSettleAuctionPayoutNonemptyMemCopy
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
                  outPay)
                (auctionSettleAuctionPayoutNonemptyAwCopy outPay))
            (auctionSettleAuctionDynMload64
              (auctionSettleAuctionPayoutNonemptyMemCopy
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
                outPay)
              (auctionSettleAuctionPayoutNonemptyAwCopy outPay)) =
          ⟨4⟩ := by
      exact auctionSettleAuctionPayoutNonemptyDepositLen
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
    obtain ⟨gasWord, kDep, CDep, hrdDepositCall⟩ :=
      auctionSettleAuctionPayoutFallbackToDepositCallAnyMem
        hwethCodeE hfreeStable hdepositLen hrdFallbackDyn
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
    let awPayRetDyn :=
      auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
        auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
          (evm_evm := evmPayE) (evm_solm := evmPay)
          (tgt := AccountAddress.ofUInt256 wethWord)
          (value := Int.ofNat amountWord.toNat)
          (calldata := memDeposit.readWithPadding freePtrDyn.toNat 4)
          (out := outDep) (cA' := cADep) (σ' := σDep)
          (A' := ADep) (A_in := AInDep) (z := zDep)
          (g'' := gDep'') (callGas := callGasDep)
          (valueWord := amountWord) (callPerm := true)
          (wordOfInt_ofNat_toNat amountWord).symm
          (by
            simpa [evmPayE, initState, accountAddress_roundtrip,
              _hperm, memDeposit, memPayRetDyn, awPayRetDyn,
              freePtrDyn, wethWord] using hThetaDep)
          (by simpa [evmPayE, initState] using hdepositBalance)
          (by
            simp [evmPayE, evmBurnE, initState]
            intro hbad
            have hbadVal : I.depth.val = 1024 := by
              exact congrArg Fin.val hbad
            omega)
          (by simpa [evmPayE, evmPay] using hpostPayAccounts)
          (by
            simp [evmPayE, evmPay, evmBurnE, evmBurn, evmMark,
              evmEnter, evmS, auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              auctionStorageStore_σ₀])
          (by simp [evmPayE, evmPay])
          (by
            simp [evmPayE, evmPay, evmBurnE, evmBurn, evmMark,
              evmEnter, evmS, auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              auctionStorageStore_genesisBlockHeader])
          (by
            simp [evmPayE, evmPay, evmBurnE, evmBurn, evmMark,
              evmEnter, evmS, auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              auctionStorageStore_blocks])
          (by
            simp [evmPayE, evmPay, evmBurnE, evmBurn, evmMark,
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
              Account.lookupStorage, auctionSlotWord, hburnOwner]
          unfold wethWord
          rw [hslot, ← hwethSlotPay]
        have hwethTarget :
            EVM.address (AccountAddress.ofNat
                ((UInt256.land
                  (Solm.EVM.storageLoad evmPay
                    evmPay.executionEnv.codeOwner ⟨202⟩)
                  solcAddrMask).toNat)) =
              AccountAddress.ofUInt256 wethWord := by
          rw [hwethWordEq]
          rw [accountAddress_ofUInt256_eq_ofNat_toNat]
          apply Fin.ext
          simp [EVM.address, EVM.uintN]
          exact Nat.mod_eq_of_lt
            (by
              simpa [EVM.addressModulus, EVM.twoPow,
                AccountAddress.size, wethWord] using
                solcAddrMask_result_canonical
                  (auctionSlotWord ⟨202⟩ σPay I))
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
              auctionSettleAuctionPayoutNonemptyDepositEncode_eq
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
          · rw [hwethTarget, ← hamountEqLocal]
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
          auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethDepositFailure
            evmS evmBurn evmPay evmDeposit
            (by simpa [evmS, initState] using hwv) hpausedSolm
            hstatusSolm hstartSolm hsettledSolm htimeSolmLe
            hbidderSolm hnounsCodeSolmEval
            (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
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
              simp [evmPay, Solm.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage,
                auctionSlotWord, hburnOwner]
            unfold wethWord
            rw [hslot, ← hwethSlotPay]
          rw [hwethWordEq]
          rw [accountAddress_ofUInt256_eq_ofNat_toNat]
          apply Fin.ext
          simp [EVM.address, EVM.uintN]
          exact Nat.mod_eq_of_lt
            (by
              simpa [EVM.addressModulus, EVM.twoPow,
                AccountAddress.size, wethWord] using
                solcAddrMask_result_canonical
                  (auctionSlotWord ⟨202⟩ σPay I))
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
              auctionSettleAuctionPayoutNonemptyDepositEncode_eq
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
          · rw [hwethTarget, ← hamountEqLocal]
            exact hdepositRawTrue
        have hrdLoadWethInput :
            RD auctionBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3432⟩
              [⟨1⟩, ⟨4⟩ + freePtrDyn, amountWord, ⟨3504541104⟩,
                wethWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
                ⟨413⟩, auctionSelWord I]
              memDeposit
              (auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn)
              outDep (cADep, σDep) kAfterDep CAfterDep := by
          have hmin :
              (min (⟨0⟩ : UInt256)
                  (UInt256.ofNat outDep.size)).toNat =
                0 := by
            have hle :
                (⟨0⟩ : UInt256) ≤ UInt256.ofNat outDep.size := by
              show (0 : Nat) ≤ (UInt256.ofNat outDep.size).val.val
              exact Nat.zero_le _
            simp [min, hle]
          have hrdAfterDep := hrdAfterDepRaw
          rw [hmin, byteArray_write_len_zero] at hrdAfterDep
          simpa [amountWord, ownerWord, memDeposit, wethWord,
            freePtrDyn] using hrdAfterDep
        exact
          auctionSettleAuctionBodyBurnPayoutFailureNonemptyTransferCase
            (cADep := cADep) (σDep := σDep) (σDepSolm := σDepSolm)
            (ADep := ADep) (ADepSolm := ADepSolm)
            _hcode _hperm hdispatch hdecode hwv
            hpausedSolm hstatusSolm hstartSolm hsettledSolm htimeSolmLe
            hbidderSolm hnounsCodeSolmEval hcallSolm hpostBurn hamountEq
            hamountSolm hdepth hpaySolm hpostPay houtZero houtPaySmall
            hwethCodeE hpostDep hdeposit hrdLoadWethInput
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
        simpa [evmPay, evmBurn, evmMark, evmEnter, evmS,
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
              Account.lookupStorage, auctionSlotWord, hburnOwner]
          unfold wethWord
          rw [hslot, ← hwethSlotPay]
        rw [hwethWordEq]
        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        apply Fin.ext
        simp [EVM.address, EVM.uintN]
        exact Nat.mod_eq_of_lt
          (by
            simpa [EVM.addressModulus, EVM.twoPow,
              AccountAddress.size, wethWord] using
              solcAddrMask_result_canonical
                (auctionSlotWord ⟨202⟩ σPay I))
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
              Account.lookupStorage, auctionSlotWord, hburnOwner]
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
            auctionSettleAuctionPayoutNonemptyDepositEncode_eq
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
        · rw [hwethTarget, ← hamountEqLocal]
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
        auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethDepositFailure
          evmS evmBurn evmPay evmDeposit
          (by simpa [evmS, initState] using hwv) hpausedSolm
          hstatusSolm hstartSolm hsettledSolm htimeSolmLe
          hbidderSolm hnounsCodeSolmEval
          (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
          hamountSolm hpaySolm hwethCodeSolm hdeposit
      exact hrdDepositFailRev.reEquivExecutionRevert _hcode
        hdispatch hdecode hbody
  · let wethWord :=
        UInt256.land (auctionSlotWord ⟨202⟩ σPay I) solcAddrMask
    have hwethCodeZero :
        Reasoning.Theory.uniswapExtCodeSizeWord σPay
            (UInt256.land (auctionSlotWord ⟨202⟩ σPay I)
              solcAddrMask) =
          ⟨0⟩ := by
      by_contra hne
      exact hwethCodeE hne
    have hrdNoCodeRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I) :=
      auctionSettleAuctionPayoutFallbackWethNoCodeRevertAnyMem
        hwethCodeZero hrdFallback
    have hpostPayAccounts :
        accountMapEquiv σPay σPaySolm := by
      simpa [evmPayE, evmPay] using hpostPay
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
          Account.lookupStorage, auctionSlotWord, hburnOwner]
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
        exact accountMapEquiv_code_size_word hpostPayAccounts
          wethAddr
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
      auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethNoCode
        evmS evmBurn evmPay
        (by simpa [evmS, initState] using hwv) hpausedSolm
        hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
        hamountSolm hpaySolm hwethCodeSolm
    exact hrdNoCodeRev.reEquivExecutionRevert _hcode
      hdispatch hdecode hbody


end Auction

import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmptyFromCallCodeWeth
import Benchmarks.Auction.SettleAuctionTransferBranchCallFailure

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionBodyTransferFromBranch {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD auctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hwv : I.weiValue = ⟨0⟩)
    (hpausedZero : auctionPausedWord σ_evm I ≠ ⟨0⟩)
    (hpausedSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩)
    (hstatusEntered : auctionSlotWord ⟨101⟩ σ_evm I ≠ ⟨2⟩)
    (hstatusSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ_evm I ≠ ⟨0⟩)
    (hstartSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ_evm I) = ⟨0⟩)
    (hsettledSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (hendWord : auctionSlotWord ⟨210⟩ σ_evm I = auctionSlotWord ⟨210⟩ σ_solm I)
    (htime :
      ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ_evm I).toNat)
    (hsettledWord : auctionSlotWord ⟨211⟩ σ_evm I = auctionSlotWord ⟨211⟩ σ_solm I)
    (hbidderZero :
      auctionPackedBidderWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I) ≠
        ⟨0⟩) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  have htimeSolmLe :
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat := by
    have hmap :
        auctionAuctionEndWord σ_solm I = auctionAuctionEndWord σ_evm I := by
      simpa [auctionAuctionEndWord] using hendWord.symm
    have hnotSolm :
        ¬ (UInt256.ofNat I.header.timestamp).toNat <
            (auctionAuctionEndWord σ_solm I).toNat := by
      intro hlt
      exact htime (by simpa [hmap] using hlt)
    have hle := Nat.le_of_not_gt hnotSolm
    simpa [evmS, initState, auctionAuctionEndWord, auctionSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hle
  have hpackedEnter :
      auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I =
        auctionAuctionPackedWord σ_evm I := by
    unfold auctionAuctionPackedWord auctionSettleAuctionEnterMap auctionSlotWord
    simpa using
      sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨211⟩ ⟨101⟩
        ⟨2⟩ (by decide)
  have hbidderEvm :
      auctionPackedBidderWord (auctionAuctionPackedWord σ_evm I) ≠ ⟨0⟩ := by
    intro hzero
    exact hbidderZero (by simpa [hpackedEnter] using hzero)
  have hbidderSolmWord :
      auctionPackedBidderWord (auctionAuctionPackedWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    have hpacked :
        auctionAuctionPackedWord σ_evm I =
          auctionAuctionPackedWord σ_solm I := by
      simpa [auctionAuctionPackedWord] using hsettledWord
    exact hbidderEvm (by simpa [hpacked] using hzero)
  have hbidderSolm :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0 := by
    have hload :
        Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩ =
          auctionAuctionPackedWord σ_solm I := by
      simp [evmS, initState, auctionAuctionPackedWord, auctionSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    rw [hload]
    exact auctionPackedBidderAddress_ne_zero
      (auctionAuctionPackedWord σ_solm I) hbidderSolmWord
  by_cases hnounsNoCode :
    Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap
          (auctionSettleAuctionEnterMap σ_evm I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap
              (auctionSettleAuctionEnterMap σ_evm I) I) I)
          solcAddrMask) =
      ⟨0⟩
  · exact transferBranchNoCodeCase
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      _hcode _hperm _hAccounts hdispatch hdecode hreach hwv hpausedZero
      hpausedSolm hstatusEntered hstatusSolm hstart hstartSolm hsettled
      hsettledSolm htime hbidderZero
      (by simpa [evmS] using htimeSolmLe)
      (by simpa [evmS] using hbidderSolm)
      hnounsNoCode
  · have hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
          (auctionSettleAuctionMarkSettledMap
            (auctionSettleAuctionEnterMap σ_evm I) I)
          (UInt256.land
            (auctionSlotWord ⟨201⟩
              (auctionSettleAuctionMarkSettledMap
                (auctionSettleAuctionEnterMap σ_evm I) I) I)
            solcAddrMask) ≠
        ⟨0⟩ := by
      intro hzero
      exact hnounsNoCode hzero
    have hnounsCodeSolmEval :
        evalExpr? auctionConfig
            { contract := auctionContract,
              locals := auctionSettleAuctionSnapshotStore
                (auctionSettleAuctionEnterState evmS) }
            (auctionSettleAuctionMarkSettledState
              (auctionSettleAuctionEnterState evmS))
            (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
          .ok (.bool true) := by
      simpa [evmS] using
        evalExpr_settleAuction_nounsCode_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) _hAccounts hnounsCode
    by_cases hdepth : I.depth.val < 1024
    · obtain ⟨cA', σ', z, o, A', k, C, hrdPost, hcallEvm, hosz⟩ :=
        auctionSettleAuctionX_transferFromPostCall
          (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered
          hstart hsettled htime hbidderZero hnounsCode hdepth hreach
      obtain ⟨σ'_solm, A'_solm, hcallSolm, hpostTf⟩ :=
        auctionSettleAuctionTransferFromCall_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) _hAccounts hcallEvm
      let evmTf :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      cases z
      · exact transferBranchCallFailureCase
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (cA' := cA') (σ' := σ') (σ'_solm := σ'_solm)
          (A'_solm := A'_solm) (o := o) (k := k) (C := C)
          _hcode hdispatch hdecode hwv
          hpausedSolm hstatusSolm hstartSolm hsettledSolm
          htimeSolmLe hbidderSolm hnounsCodeSolmEval hcallSolm
          hosz (by simpa using hrdPost)
      · by_cases hamountZero :
          auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I = ⟨0⟩
        · exact transferBranchNoPayoutCase
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (cA' := cA') (σ' := σ') (σ'_solm := σ'_solm)
            (A'_solm := A'_solm) (o := o) (k := k) (C := C)
            _hcode _hperm _hAccounts hdispatch hdecode hwv
            hpausedSolm hstatusSolm hstartSolm hsettledSolm
            (by simpa [evmS] using htimeSolmLe)
            (by simpa [evmS] using hbidderSolm)
            (by simpa [evmS] using hnounsCodeSolmEval)
            (by simpa [evmS, evmEnter, evmMark, evmTf] using hcallSolm)
            hpostTf (by simpa using hrdPost) hamountZero
        ·
          obtain ⟨_, _, hrdPayEntry⟩ :=
            auctionSettleAuctionTransferFromSuccessToPayoutEntry
              (target :=
                UInt256.land
                  (auctionSlotWord ⟨201⟩
                    (auctionSettleAuctionMarkSettledMap
                      (auctionSettleAuctionEnterMap σ_evm I) I) I)
                  solcAddrMask)
              hamountZero (rd := by simpa using hrdPost)
          have hownerWordMasked :
              UInt256.land
                  (UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask)
                  solcAddrMask =
                UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask := by
            exact solcAddrMask_clean
              (solcAddrMask_result_canonical (auctionSlotWord ⟨151⟩ σ' I))
          obtain ⟨_, _, hrdPayCall⟩ :=
            auctionSettleAuctionTransferFromPayoutEntryToCall hownerWordMasked
              (rd := hrdPayEntry)
          let amountWord :=
            auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
          let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
          let evmTfE :=
            { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σ' } with
                substate := A',
                createdAccounts := cA' }
          have henterAccounts :
              accountMapEquiv (auctionSettleAuctionEnterMap σ_evm I)
                evmEnter.accountMap := by
            have henterEquiv :
                accountMapEquiv (auctionSettleAuctionEnterMap σ_evm I)
                  (auctionSettleAuctionEnterMap σ_solm I) := by
              exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩
                _hAccounts
            have henterMapState :
                accountMapEquiv (auctionSettleAuctionEnterMap σ_solm I)
                  evmEnter.accountMap := by
              simpa [evmEnter, evmS] using
                (auctionSettleAuctionEnterMap_accountMap
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                  (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g))
            exact accountMapEquiv.trans henterEquiv henterMapState
          have henterOwner : evmEnter.executionEnv.codeOwner = I.codeOwner := by
            simp [evmEnter, evmS, auctionSettleAuctionEnterState, initState,
              storageStore_executionEnv]
          have hamountEq :
              amountWord = auctionSettleAuctionAmount evmEnter := by
            have hslot :=
              accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨208⟩
                (⟨0⟩ : UInt256)
            simpa [amountWord, auctionSettleAuctionAmount, henterOwner,
              auctionAuctionAmountWord, auctionSlotWord, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage] using hslot
          have hamountSolm :
              0 < (auctionSettleAuctionAmount evmEnter).toNat := by
            apply Nat.pos_of_ne_zero
            intro hzeroNat
            have hzeroWord : auctionSettleAuctionAmount evmEnter = ⟨0⟩ := by
              apply u256_inj
              simpa [UInt256.toNat] using hzeroNat
            exact hamountZero (hamountEq.trans hzeroWord)
          have htfOwner : evmTf.executionEnv.codeOwner = I.codeOwner := by
            simp [evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState,
              auctionSettleAuctionEnterState, initState,
              storageStore_executionEnv]
          have hownerLoad :
              auctionSlotWord ⟨151⟩ σ' I =
                Solm.EVM.storageLoad evmTf evmTf.executionEnv.codeOwner
                  ⟨151⟩ := by
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
            simp [auctionOwnerAddressAt, ownerWord, hownerLoad, EVM.address,
              EVM.uintN]
            exact Nat.mod_eq_of_lt
              (by
                simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
                  solcAddrMask_result_canonical
                    (Solm.EVM.storageLoad evmTf
                      evmTf.executionEnv.codeOwner ⟨151⟩))
          have htfEAccounts : accountMapEquiv evmTfE.accountMap evmTf.accountMap := by
            simpa [evmTfE, evmTf] using hpostTf
          have htfESigma0 : evmTfE.σ₀ = evmTf.σ₀ := by
            simp [evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
              initState, auctionStorageStore_σ₀]
          have htfECreated : evmTf.createdAccounts = evmTfE.createdAccounts := by
            simp [evmTfE, evmTf]
          have htfEGenesis : evmTf.genesisBlockHeader = evmTfE.genesisBlockHeader := by
            simp [evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
              initState, auctionStorageStore_genesisBlockHeader]
          have htfEBlocks : evmTf.blocks = evmTfE.blocks := by
            simp [evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
              initState, auctionStorageStore_blocks]
          have htfEEnv : evmTf.executionEnv = evmTfE.executionEnv := by
            simp [evmTfE, evmTf, evmMark, evmEnter, evmS,
              auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
              initState, storageStore_executionEnv]
          have hpayStackLen :
              [⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩, amountWord,
                ownerWord, ⟨3347⟩, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
                ⟨2471⟩, ⟨413⟩, auctionSelWord I].length + 1 ≤ 1024 := by
            change 17 ≤ 1024
            native_decide
          by_cases hpayBalance :
              amountWord ≤ (σ'.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
          · obtain ⟨cAPay, σPay, zPay, outPay, AInPay, callGasPay,
                kPay, CPay, hThetaPayPack, hrdAfterPayRaw, houtPaySize⟩ :=
              RD.callValueMadeEmptyInOut hrdPayCall (by native_decide) _hperm
                (by simpa [amountWord] using hpayBalance) hdepth
                (by simpa [amountWord, ownerWord] using hpayStackLen)
            obtain ⟨gPay'', APay, hThetaPay⟩ := hThetaPayPack
            let evmPayE :=
              { evmTfE with
                  accountMap := σPay,
                  substate := APay,
                  createdAccounts := cAPay }
            cases zPay
            ·
              have hpayBalanceE :
                  amountWord ≤ (evmTfE.accountMap.find? evmTfE.executionEnv.codeOwner
                    |>.elim ⟨0⟩ (·.balance)) := by
                simpa [evmTfE, initState, amountWord] using hpayBalance
              have hpayDepthE : evmTfE.executionEnv.depth ≠ 1024 := by
                simp [evmTfE, initState]
                intro hbad
                have hbadVal : I.depth.val = 1024 := by
                  exact congrArg Fin.val hbad
                omega
              have hpayTransport :=
                transferBranchPayCallTransport
                  (evmTfE := evmTfE) (evmTf := evmTf) (cAPay := cAPay)
                  (σPay := σPay) (AInPay := AInPay) (APay := APay)
                  (z := false) (outPay := outPay) (gPay'' := gPay'')
                  (callGasPay := callGasPay) (amountWord := amountWord)
                  (ownerWord := ownerWord)
                  (by simpa [evmTfE, initState, amountWord, ownerWord, _hperm]
                    using hThetaPay)
                  hpayBalanceE hpayDepthE
                  htfEAccounts htfESigma0 htfECreated htfEGenesis htfEBlocks htfEEnv
              obtain ⟨σPaySolm, hpayPair⟩ := hpayTransport
              let APaySolm := Classical.choose hpayPair
              have hpayAnd := Classical.choose_spec hpayPair
              have hpaySolmRaw := hpayAnd.1
              have hpostPay := hpayAnd.2
              let evmPay :=
                { evmTf with
                    accountMap := σPaySolm,
                    substate := APaySolm,
                    createdAccounts := evmPayE.createdAccounts }
              have hpaySolm :
                  callViaEVM evmTf (EVM.address (auctionOwnerAddressAt evmTf))
                    (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
                    ByteArray.empty (false, evmPay, outPay) true := by
                rw [hownerEq, ← hamountEq]
                exact hpaySolmRaw
              by_cases houtZero : outPay.size = 0
              · obtain ⟨kFallback, CFallback, hrdFallbackDyn⟩ :=
                  auctionSettleAuctionPayoutCallFailureEmptyReturnToFallback
                    houtZero
                    (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                by_cases hwethCodeE :
                    Reasoning.Theory.uniswapExtCodeSizeWord σPay
                        (UInt256.land (auctionSlotWord ⟨202⟩ σPay I)
                          solcAddrMask) ≠
                      ⟨0⟩
                · exact transferBranchPayoutFailureEmptyFromCallWethCodeCase
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (cA' := cA') (cAPay := cAPay)
                    (σ' := σ') (σ'_solm := σ'_solm)
                    (σPay := σPay) (σPaySolm := σPaySolm)
                    (A' := A') (A'_solm := A'_solm)
                    (APay := APay) (APaySolm := APaySolm)
                    (o := o) (outPay := outPay)
                    (kFallback := kFallback) (CFallback := CFallback)
                    _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm
                    hstartSolm hsettledSolm htimeSolmLe hbidderSolm
                    hnounsCodeSolmEval hcallSolm hpostTf hamountEq hamountSolm
                    hdepth hpaySolm hpostPay
                    (by simpa [amountWord, ownerWord] using hrdFallbackDyn)
                    hwethCodeE
                · have hwethCodeZero :
                      Reasoning.Theory.uniswapExtCodeSizeWord σPay
                          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I)
                            solcAddrMask) =
                        ⟨0⟩ := by
                    by_contra hne
                    exact hwethCodeE hne
                  exact transferBranchPayoutFailureEmptyWethNoCodeAnyMemCase
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (cA' := cA') (cAPay := cAPay)
                    (σ' := σ') (σ'_solm := σ'_solm)
                    (σPay := σPay) (σPaySolm := σPaySolm)
                    (A' := A') (A'_solm := A'_solm)
                    (APay := APay) (APaySolm := APaySolm)
                    (o := o) (outPay := outPay)
                    (_kPay := kPay) (_CPay := CPay)
                    (kFallback := kFallback) (CFallback := CFallback)
                    _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm
                    hstartSolm hsettledSolm htimeSolmLe hbidderSolm
                    hnounsCodeSolmEval hcallSolm hpostTf hamountSolm hpaySolm
                    hpostPay
                    (by simpa [amountWord, ownerWord] using hrdFallbackDyn)
                    hwethCodeZero
              · obtain ⟨memPayRet, awPayRet, _, _, hrdFallback⟩ :=
                  auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallback
                    houtPaySize houtZero
                    (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                by_cases hwethCodeE :
                    Reasoning.Theory.uniswapExtCodeSizeWord σPay
                        (UInt256.land (auctionSlotWord ⟨202⟩ σPay I)
                          solcAddrMask) ≠
                      ⟨0⟩
                · have houtPaySmall : outPay.size < 2 ^ 138 := by
                    exact Theta_returnData_size_lt_2pow138_of_eq
                      (hΘ := by
                        simpa [evmTfE, initState, accountAddress_roundtrip,
                          _hperm, amountWord, ownerWord] using hThetaPay)
                      (hd := by simp)
                  exact transferBranchPayoutFailureNonemptyWethCodeCase
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (cA' := cA') (cAPay := cAPay)
                    (σ' := σ') (σ'_solm := σ'_solm)
                    (σPay := σPay) (σPaySolm := σPaySolm)
                    (A' := A') (A'_solm := A'_solm)
                    (APay := APay) (APaySolm := APaySolm)
                    (o := o) (outPay := outPay) (kPay := kPay) (CPay := CPay)
                    _hcode _hperm hdispatch hdecode hwv hpausedSolm hstatusSolm
                    hstartSolm hsettledSolm htimeSolmLe hbidderSolm
                    hnounsCodeSolmEval hcallSolm hpostTf hamountEq hamountSolm
                    hdepth hpaySolm hpostPay houtPaySize houtZero houtPaySmall
                    (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                    hwethCodeE
                · have hwethCodeZero :
                      Reasoning.Theory.uniswapExtCodeSizeWord σPay
                          (UInt256.land (auctionSlotWord ⟨202⟩ σPay I)
                            solcAddrMask) =
                        ⟨0⟩ := by
                    by_contra hne
                    exact hwethCodeE hne
                  exact transferBranchPayoutFailureNonemptyWethNoCodeCase
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (cA' := cA') (cAPay := cAPay)
                    (σ' := σ') (σ'_solm := σ'_solm)
                    (σPay := σPay) (σPaySolm := σPaySolm)
                    (A' := A') (A'_solm := A'_solm)
                    (APay := APay) (APaySolm := APaySolm)
                    (o := o) (outPay := outPay) (kPay := kPay) (CPay := CPay)
                    _hcode hdispatch hdecode hwv hpausedSolm hstatusSolm
                    hstartSolm hsettledSolm htimeSolmLe hbidderSolm
                    hnounsCodeSolmEval hcallSolm hamountSolm hpaySolm
                    hpostPay houtPaySize houtZero
                    (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                    hwethCodeZero
            · have hpayEvmTrue :
                      callViaEVM evmTfE (AccountAddress.ofUInt256 ownerWord)
                        (Int.ofNat amountWord.toNat) ByteArray.empty
                        (true, evmPayE, outPay) true := by
                    exact callViaEVM_callMade_of_theta
                      (evm := evmTfE) (tgt := AccountAddress.ofUInt256 ownerWord)
                      (value := Int.ofNat amountWord.toNat) (calldata := ByteArray.empty)
                      (out := outPay) (cA' := cAPay) (σ' := σPay)
                      (A' := APay) (A_in := AInPay) (z := true)
                      (g'' := gPay'') (callGas := callGasPay)
                      (valueWord := amountWord) (callPerm := true)
                      (wordOfInt_ofNat_toNat amountWord).symm
                      (by
                        simpa [evmTfE, initState, accountAddress_roundtrip, _hperm]
                          using hThetaPay)
                      (by simpa [evmTfE, initState, amountWord] using hpayBalance)
                      (by
                        simp [evmTfE, initState]
                        intro hbad
                        have hbadVal : I.depth.val = 1024 := by
                          exact congrArg Fin.val hbad
                        omega)
              obtain ⟨σPaySolm, APaySolm, hpaySolmRaw, hpostPay⟩ :=
                auctionCallViaEVM_callMade_accountMapEquiv_perm
                  (storage := auctionConfig.storage) (evm_solm := evmTf)
                  hpayEvmTrue
                  htfEAccounts htfESigma0 htfECreated htfEGenesis htfEBlocks htfEEnv
              let evmPay :=
                { evmTf with
                    accountMap := σPaySolm,
                    substate := APaySolm,
                    createdAccounts := evmPayE.createdAccounts }
              have hpaySolm :
                  callViaEVM evmTf (EVM.address (auctionOwnerAddressAt evmTf))
                    (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
                    ByteArray.empty (true, evmPay, outPay) true := by
                rw [hownerEq, ← hamountEq]
                exact hpaySolmRaw
              exact transferBranchPayoutSuccessCase
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (cA' := cA') (cAPay := cAPay) (σ' := σ')
                (σPay := σPay) (σPaySolm := σPaySolm)
                (σ'_solm := σ'_solm) (A'_solm := A'_solm)
                (APaySolm := APaySolm) (o := o) (outPay := outPay)
                (kPay := kPay) (CPay := CPay)
                _hcode _hperm hdispatch hdecode hwv
                hpausedSolm hstatusSolm hstartSolm hsettledSolm
                htimeSolmLe hbidderSolm hnounsCodeSolmEval hcallSolm
                hamountSolm
                (by simpa [evmPay, evmPayE] using hpaySolm)
                hpostPay houtPaySize
                (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
          · change RuntimeCase
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) g
            exact transferBranchPayoutInsufficientBalanceFromCallNamed
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (cA' := cA') (σ' := σ') (σ'_solm := σ'_solm)
              (A'_solm := A'_solm) (o := o)
              (evmS := evmS) (evmEnter := evmEnter)
              (evmMark := evmMark) (evmTf := evmTf)
              (amountWord := amountWord) (ownerWord := ownerWord)
              _hcode _hperm hdispatch hdecode
              rfl rfl rfl rfl rfl rfl hwv
              hpausedSolm hstatusSolm hstartSolm hsettledSolm
              htimeSolmLe hbidderSolm hnounsCodeSolmEval hcallSolm
              hpostTf hamountEq hamountSolm hdepth hpayBalance
              hrdPayCall
    · exact transferBranchDepthLimitCase
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        _hcode _hperm hdispatch hdecode hreach hwv hpausedZero hstatusEntered
        hpausedSolm hstatusSolm hstart hstartSolm hsettled hsettledSolm
        htime hbidderZero hnounsCode
        (by simpa [evmS] using hnounsCodeSolmEval)
        (by simpa [evmS] using htimeSolmLe)
        (by simpa [evmS] using hbidderSolm)
        hdepth

end Auction

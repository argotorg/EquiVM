import Benchmarks.Auction.SettleAndCreateAfterSettlement
import Benchmarks.Auction.SettleAuctionTransferBranchHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleCurrentAndCreateNewAuctionBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 18))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 18) rfl _hsel
  have hdispatch := auctionDispatch_settleCurrentAndCreateNewAuction _hsel
  have hdecode := auctionDecode_settleCurrentAndCreateNewAuction (I := I) hsz4
  have hreach := auctionReachSettleCurrentAndCreateNewAuctionBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hstatusWord :
        auctionSlotWord ⟨101⟩ σ_evm I = auctionSlotWord ⟨101⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨101⟩ ⟨0⟩
    by_cases hstatusEntered : auctionSlotWord ⟨101⟩ σ_evm I = ⟨2⟩
    · have hstatusSolm :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ = ⟨2⟩ := by
        have hmap : auctionSlotWord ⟨101⟩ σ_solm I = ⟨2⟩ := by
          simpa [hstatusWord] using hstatusEntered
        simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
          using hmap
      have hbody := auctionSettleAndCreateTransitionReverts_statusEntered evmS
        (by simp only [evmS, initState]; exact hwv) hstatusSolm
      exact (auctionX_settleCurrentAndCreateNewAuction_revert_statusEntered
          (g := Sat256.ofUInt256 g) hwv hstatusEntered hreach)
        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
    · have hstatusSolm :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩ := by
        intro h
        apply hstatusEntered
        have hmap : auctionSlotWord ⟨101⟩ σ_solm I = ⟨2⟩ := by
          simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
            using h
        simpa [hstatusWord] using hmap
      have hpausedWord :
          auctionSlotWord ⟨51⟩ σ_evm I = auctionSlotWord ⟨51⟩ σ_solm I :=
        accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨51⟩ ⟨0⟩
      by_cases hpausedZero : auctionPausedWord σ_evm I = ⟨0⟩
      · have hpausedSolm :
            UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
                ⟨255⟩ =
              ⟨0⟩ := by
          have hmap : auctionPausedWord σ_solm I = ⟨0⟩ := by
            simpa [auctionPausedWord, hpausedWord] using hpausedZero
          simpa [evmS, initState, auctionPausedWord, auctionSlotWord, Solm.EVM.storageLoad,
            State.lookupAccount] using hmap
        have hsettleReach := auctionSettleCurrentAndCreateNewAuctionX_toInternalSettleAuction
          (cA := cA)
          (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (g := Sat256.ofUInt256 g) _hperm hwv hstatusEntered hpausedZero hreach
        have hsnapshotReach := auctionInternalSettleAuction_toSnapshotCheck
          (ret := (⟨2690⟩ : UInt256)) hsettleReach
        have hstartWord :
            auctionSlotWord ⟨209⟩ σ_evm I = auctionSlotWord ⟨209⟩ σ_solm I :=
          accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨209⟩ ⟨0⟩
        by_cases hstart : auctionAuctionStartWord σ_evm I = ⟨0⟩
        · have hstartSolm :
              Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩ := by
            have hmap : auctionAuctionStartWord σ_solm I = ⟨0⟩ := by
              simpa [auctionAuctionStartWord, hstartWord] using hstart
            simpa [evmS, initState, auctionAuctionStartWord, auctionSlotWord,
              Solm.EVM.storageLoad, State.lookupAccount] using hmap
          have hbody := auctionSettleAndCreateTransitionReverts_settleNotStarted evmS
            (by simp only [evmS, initState]; exact hwv) hstatusSolm hpausedSolm hstartSolm
          exact (auctionInternalSettleAuction_revert_notStarted
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (ret := (⟨2690⟩ : UInt256)) hstart hsettleReach)
            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
        · have hsettledWord :
              auctionSlotWord ⟨211⟩ σ_evm I = auctionSlotWord ⟨211⟩ σ_solm I :=
            accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨211⟩ ⟨0⟩
          by_cases hsettled :
              auctionPackedSettledWord (auctionAuctionPackedWord σ_evm I) ≠ ⟨0⟩
          · have hstartSolm :
                Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩ := by
              have hstartEq :
                  auctionAuctionStartWord σ_evm I = auctionAuctionStartWord σ_solm I := by
                simpa [auctionAuctionStartWord] using hstartWord
              have hstartSolmWord : auctionAuctionStartWord σ_solm I ≠ ⟨0⟩ := by
                intro hzero
                exact hstart (by simp [hstartEq, hzero])
              simpa [evmS, initState, auctionAuctionStartWord, auctionSlotWord,
                Solm.EVM.storageLoad, State.lookupAccount] using hstartSolmWord
            have hsettledSolm :
                auctionPackedSettledWord
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) ≠
                  ⟨0⟩ := by
              have hpackedEq :
                  auctionAuctionPackedWord σ_evm I = auctionAuctionPackedWord σ_solm I := by
                simpa [auctionAuctionPackedWord] using hsettledWord
              have hsettledSolmWord :
                  auctionPackedSettledWord (auctionAuctionPackedWord σ_solm I) ≠ ⟨0⟩ := by
                intro hzero
                exact hsettled (by simp [hpackedEq, hzero])
              simpa [evmS, initState, auctionAuctionPackedWord, auctionSlotWord,
                Solm.EVM.storageLoad, State.lookupAccount] using hsettledSolmWord
            have hbody := auctionSettleAndCreateTransitionReverts_settleAlreadySettled evmS
              (by simp only [evmS, initState]; exact hwv) hstatusSolm hpausedSolm
              hstartSolm hsettledSolm
            exact (auctionInternalSettleAuction_revert_alreadySettled
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g)
                (ret := (⟨2690⟩ : UInt256)) hstart hsettled hsettleReach)
              |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
          · have hsettledZero :
                auctionPackedSettledWord (auctionAuctionPackedWord σ_evm I) = ⟨0⟩ := by
              by_contra hzero
              exact hsettled hzero
            have hstartSolm :
                Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩ := by
              have hstartEq :
                  auctionAuctionStartWord σ_evm I = auctionAuctionStartWord σ_solm I := by
                simpa [auctionAuctionStartWord] using hstartWord
              have hstartSolmWord : auctionAuctionStartWord σ_solm I ≠ ⟨0⟩ := by
                intro hzero
                exact hstart (by simp [hstartEq, hzero])
              simpa [evmS, initState, auctionAuctionStartWord, auctionSlotWord,
                Solm.EVM.storageLoad, State.lookupAccount] using hstartSolmWord
            have hsettledSolm :
                auctionPackedSettledWord
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
                  ⟨0⟩ := by
              have hpackedEq :
                  auctionAuctionPackedWord σ_evm I = auctionAuctionPackedWord σ_solm I := by
                simpa [auctionAuctionPackedWord] using hsettledWord
              have hsettledSolmWord :
                  auctionPackedSettledWord (auctionAuctionPackedWord σ_solm I) = ⟨0⟩ := by
                simpa [hpackedEq] using hsettledZero
              simpa [evmS, initState, auctionAuctionPackedWord, auctionSlotWord,
                Solm.EVM.storageLoad, State.lookupAccount] using hsettledSolmWord
            have hendWord :
                auctionSlotWord ⟨210⟩ σ_evm I = auctionSlotWord ⟨210⟩ σ_solm I :=
              accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨210⟩ ⟨0⟩
            by_cases htime :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (auctionAuctionEndWord σ_evm I).toNat
            · have htimeSolm :
                  (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat <
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat := by
                have hendEq :
                    auctionAuctionEndWord σ_evm I = auctionAuctionEndWord σ_solm I := by
                  simpa [auctionAuctionEndWord] using hendWord
                have htimeSolmWord :
                    (UInt256.ofNat I.header.timestamp).toNat <
                      (auctionAuctionEndWord σ_solm I).toNat := by
                  simpa [hendEq] using htime
                simpa [evmS, initState, auctionAuctionEndWord, auctionSlotWord,
                  Solm.EVM.storageLoad, State.lookupAccount] using htimeSolmWord
              have hbody := auctionSettleAndCreateTransitionReverts_settleTimeNotReached evmS
                (by simp only [evmS, initState]; exact hwv) hstatusSolm hpausedSolm
                hstartSolm hsettledSolm htimeSolm
              exact (auctionInternalSettleAuction_revert_timeNotReached
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  (ret := (⟨2690⟩ : UInt256)) hstart hsettledZero htime hsettleReach)
                |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
            · have hmarkReach := auctionInternalSettleAuction_toMarkSettled
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g)
                (ret := (⟨2690⟩ : UInt256)) _hperm hstart hsettledZero htime
                hsettleReach
              by_cases hbidderZero :
                  auctionPackedBidderWord
                      (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I) =
                    ⟨0⟩
              · by_cases hnounsNoCode :
                    Reasoning.Theory.uniswapExtCodeSizeWord
                        (auctionSettleAuctionMarkSettledMap
                          (auctionSettleAuctionEnterMap σ_evm I) I)
                        (UInt256.land
                          (auctionSlotWord ⟨201⟩
                            (auctionSettleAuctionMarkSettledMap
                              (auctionSettleAuctionEnterMap σ_evm I) I) I)
                          solcAddrMask) =
                      ⟨0⟩
                · let postEvm :=
                    auctionSettleAuctionMarkSettledMap
                      (auctionSettleAuctionEnterMap σ_evm I) I
                  let postSolm :=
                    auctionSettleAuctionMarkSettledMap
                      (auctionSettleAuctionEnterMap σ_solm I) I
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
                      auctionPackedBidderWord (auctionAuctionPackedWord σ_evm I) = ⟨0⟩ := by
                    simpa [hpackedEnter] using hbidderZero
                  have hbidderSolmWord :
                      auctionPackedBidderWord (auctionAuctionPackedWord σ_solm I) = ⟨0⟩ := by
                    have hpacked :
                        auctionAuctionPackedWord σ_evm I =
                          auctionAuctionPackedWord σ_solm I := by
                      simpa [auctionAuctionPackedWord] using hsettledWord
                    simpa [hpacked] using hbidderEvm
                  have hbidderSolm :
                      AccountAddress.ofNat
                          (auctionPackedBidderWord
                            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat =
                        AccountAddress.ofNat 0 := by
                    have hload :
                        Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩ =
                          auctionAuctionPackedWord σ_solm I := by
                      simp [evmS, initState, auctionAuctionPackedWord, auctionSlotWord,
                        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                    rw [hload, hbidderSolmWord]
                    rfl
                  have henterEquiv :
                      accountMapEquiv (auctionSettleAuctionEnterMap σ_evm I)
                        (auctionSettleAuctionEnterMap σ_solm I) :=
                    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ _hAccounts
                  have hmarkValEq :
                      auctionSetBoolOffset20TrueWord
                          (auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_evm I) I) =
                        auctionSetBoolOffset20TrueWord
                          (auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I) := by
                    have hslot :=
                      accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨211⟩
                        (default : UInt256)
                    simpa [auctionSlotWord] using congrArg auctionSetBoolOffset20TrueWord hslot
                  have hpostEquiv : accountMapEquiv postEvm postSolm := by
                    dsimp [postEvm, postSolm, auctionSettleAuctionMarkSettledMap]
                    rw [hmarkValEq]
                    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
                      (auctionSetBoolOffset20TrueWord
                        (auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I))
                      henterEquiv
                  have hnounsTargetEq :
                      UInt256.land (auctionSlotWord ⟨201⟩ postEvm I) solcAddrMask =
                        UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask := by
                    have hslot :=
                      accountMapEquiv_storage_findD hpostEquiv I.codeOwner ⟨201⟩
                        (default : UInt256)
                    simpa [auctionSlotWord] using
                      congrArg (fun w => UInt256.land w solcAddrMask) hslot
                  have hnounsNoCodeSolm :
                      Reasoning.Theory.uniswapExtCodeSizeWord postSolm
                          (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask) =
                        ⟨0⟩ := by
                    have htmp :
                        Reasoning.Theory.uniswapExtCodeSizeWord postSolm
                            (UInt256.land (auctionSlotWord ⟨201⟩ postEvm I) solcAddrMask) =
                          ⟨0⟩ := by
                      rw [← uniswapExtCodeSizeWord_accountMapEquiv hpostEquiv
                        (UInt256.land (auctionSlotWord ⟨201⟩ postEvm I) solcAddrMask)]
                      simpa [postEvm] using hnounsNoCode
                    simpa [hnounsTargetEq] using htmp
                  have henterMapState :
                      accountMapEquiv (auctionSettleAuctionEnterMap σ_solm I)
                        evmEnter.accountMap := by
                    simpa [evmEnter, evmS] using
                      (auctionSettleAuctionEnterMap_accountMap
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g))
                  have henterOwner : evmEnter.executionEnv.codeOwner = I.codeOwner := by
                    simp [evmEnter, evmS, auctionSettleAuctionEnterState, initState,
                      storageStore_executionEnv]
                  have hmarkOwner : evmMark.executionEnv.codeOwner = I.codeOwner := by
                    simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
                      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
                  have hslotEnterPacked :
                      auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I =
                        Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                          ⟨211⟩ := by
                    have hslot :=
                      accountMapEquiv_storage_findD henterMapState I.codeOwner ⟨211⟩
                        (⟨0⟩ : UInt256)
                    simpa [henterOwner, auctionSlotWord, Solm.EVM.storageLoad,
                      State.lookupAccount, Account.lookupStorage] using hslot
                  have hslotEnterPackedI :
                      auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I =
                        Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩ := by
                    simpa [henterOwner] using hslotEnterPacked
                  have hpostMapState : accountMapEquiv postSolm evmMark.accountMap := by
                    dsimp [evmMark, auctionSettleAuctionMarkSettledState]
                    rw [henterOwner]
                    simp only [storageStore_accountMap]
                    dsimp [postSolm, auctionSettleAuctionMarkSettledMap]
                    rw [hslotEnterPackedI]
                    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
                      (auctionSetBoolOffset20TrueWord
                        (Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩))
                      henterMapState
                  have htargetMapSource :
                      UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask =
                        UInt256.land
                          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                            ⟨201⟩)
                          solcAddrMask := by
                    have hslotPost :
                        auctionSlotWord ⟨201⟩ postSolm I =
                          Solm.EVM.storageLoad evmMark evmMark.executionEnv.codeOwner
                            ⟨201⟩ := by
                      have hslot :=
                        accountMapEquiv_storage_findD hpostMapState I.codeOwner ⟨201⟩
                          (⟨0⟩ : UInt256)
                      simpa [hmarkOwner, auctionSlotWord, Solm.EVM.storageLoad,
                        State.lookupAccount, Account.lookupStorage] using hslot
                    have hslotMark := auctionSettleAuctionMarkSettledState_storageLoad_nouns
                      evmEnter
                    simpa [evmMark] using
                      congrArg (fun w => UInt256.land w solcAddrMask)
                        (hslotPost.trans hslotMark)
                  have hnounsNoCodeState :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
                          (UInt256.land
                            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                              ⟨201⟩)
                            solcAddrMask) =
                        ⟨0⟩ := by
                    have htmp :
                        Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
                            (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I)
                              solcAddrMask) =
                          ⟨0⟩ := by
                      rw [← uniswapExtCodeSizeWord_accountMapEquiv hpostMapState
                        (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask)]
                      exact hnounsNoCodeSolm
                    simpa [htargetMapSource] using htmp
                  have hlookup :
                      (UInt256.ofNat (((auctionSettleAuctionMarkSettledState evmEnter).lookupAccount
                        (AccountAddress.ofNat
                          ((UInt256.land
                            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                              ⟨201⟩)
                            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size))).toNat =
                        0 := by
                    let targetSource :=
                      UInt256.land
                        (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                          ⟨201⟩)
                        solcAddrMask
                    have hlookup0 :=
                      auctionUniswapExtCodeSizeWord_zero_lookup_code_zero
                        (σ := evmMark.accountMap) (target := targetSource)
                        (addr := AccountAddress.ofNat targetSource.toNat)
                        (by simp [accountAddress_ofUInt256_eq_ofNat_toNat])
                        (by simpa [targetSource] using hnounsNoCodeState)
                    simpa [evmMark, targetSource, State.lookupAccount] using hlookup0
                  have hnounsNoCodeSolmEval :
                      evalExpr? auctionConfig
                          { contract := auctionContract,
                            locals := auctionSettleAuctionSnapshotStore
                              (auctionSettleAuctionEnterState evmS) }
                          (auctionSettleAuctionMarkSettledState
                            (auctionSettleAuctionEnterState evmS))
                          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
                        .ok (.bool false) := by
                    simpa [evmEnter] using
                      evalExpr_settleAuction_nounsNoCode_after_markSettled evmEnter hlookup
                  have hbody := auctionSettleAndCreateTransitionReverts_settleBurnNoCode evmS
                    (by simp only [evmS, initState]; exact hwv) hstatusSolm hpausedSolm
                    hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsNoCodeSolmEval
                  exact (auctionInternalSettleAuction_revert_burnNoCode
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (ret := (⟨2690⟩ : UInt256)) hbidderZero hnounsNoCode hmarkReach)
                    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
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
                      auctionPackedBidderWord (auctionAuctionPackedWord σ_evm I) = ⟨0⟩ := by
                    simpa [hpackedEnter] using hbidderZero
                  have hbidderSolmWord :
                      auctionPackedBidderWord (auctionAuctionPackedWord σ_solm I) = ⟨0⟩ := by
                    have hpacked :
                        auctionAuctionPackedWord σ_evm I =
                          auctionAuctionPackedWord σ_solm I := by
                      simpa [auctionAuctionPackedWord] using hsettledWord
                    simpa [hpacked] using hbidderEvm
                  have hbidderSolm :
                      AccountAddress.ofNat
                          (auctionPackedBidderWord
                            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat =
                        AccountAddress.ofNat 0 := by
                    have hload :
                        Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩ =
                          auctionAuctionPackedWord σ_solm I := by
                      simp [evmS, initState, auctionAuctionPackedWord, auctionSlotWord,
                        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                    rw [hload, hbidderSolmWord]
                    rfl
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
                      auctionInternalSettleAuction_burnPostCall
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g)
                        (ret := (⟨2690⟩ : UInt256)) _hperm hbidderZero hnounsCode
                        hdepth hmarkReach
                    obtain ⟨σ'_solm, A'_solm, hcallSolm, _hpostBurn⟩ :=
                      auctionSettleAuctionBurnCall_accountMapEquiv
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) _hAccounts hcallEvm
                    let evmBurn :=
                      { auctionSettleAuctionMarkSettledState
                          (auctionSettleAuctionEnterState evmS) with
                        accountMap := σ'_solm,
                        substate := A'_solm,
                        createdAccounts := cA' }
                    cases z
                    · have hrdFail : RDrev auctionBytecode (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
                        auctionSettleAuctionBurnCallFailure
                          (by simpa using hrdPost) hosz (by simp)
                      have hbody :=
                        auctionSettleAndCreateTransitionReverts_settleBurnCallFailure
                          evmS evmBurn (by simp only [evmS, initState]; exact hwv)
                          hstatusSolm hpausedSolm hstartSolm hsettledSolm htimeSolmLe
                          hbidderSolm hnounsCodeSolmEval
                          (by simpa [evmBurn] using hcallSolm)
                      exact hrdFail.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                    · by_cases hamountZero : auctionAuctionAmountWord
                          (auctionSettleAuctionEnterMap σ_evm I) I = ⟨0⟩
                      · have henterMap : accountMapEquiv
                            (auctionSettleAuctionEnterMap σ_evm I)
                            (auctionSettleAuctionEnterState evmS).accountMap :=
                          (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ _hAccounts).trans
                            auctionSettleAuctionEnterMap_accountMap
                        have hamountSolm : Solm.EVM.storageLoad
                            (auctionSettleAuctionEnterState evmS)
                            (auctionSettleAuctionEnterState evmS).executionEnv.codeOwner ⟨208⟩ = ⟨0⟩ := by
                          have hh := accountMapEquiv_storage_findD henterMap I.codeOwner ⟨208⟩ ⟨0⟩
                          simpa only [auctionSettleAuctionEnterState_executionEnv, evmS, initState,
                            Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                            auctionAuctionAmountWord, auctionSlotWord] using hh.symm.trans hamountZero
                        have hsettle := auctionSettleAuctionWithMemoryReturns_burnNoPayout
                          (auctionSettleAuctionEnterState evmS) evmBurn
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨209⟩) (by decide)]
                            using hstartSolm)
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨211⟩) (by decide)]
                            using hsettledSolm)
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨210⟩) (by decide)]
                            using htimeSolmLe)
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨211⟩) (by decide)]
                            using hbidderSolm)
                          hnounsCodeSolmEval (by simpa only [evmBurn] using hcallSolm) hamountSolm
                        obtain ⟨_, _, rdEvent⟩ := auctionSettleAuctionBurnSuccessToNoPayoutEventAt hamountZero hrdPost
                        obtain ⟨memRet, awRet, kr, Cr, hm, rdRet⟩ := auctionSettleAndCreateEventReturn _hperm
                          (by rw [auctionSettleAuctionBurnCallMem_size]; decide)
                          (auctionSettleAuctionBurnCallMem_read64 ..) (by decide) (by decide) (by decide) (by decide)
                          (by rw [auctionSettleAuctionBurnCallMem_size]; native_decide) rdEvent
                        exact auctionSettleAndCreateFromSettleReturn _hcode _hperm hdispatch hdecode
                          hwv hstatusSolm hpausedSolm hdepth hsettle
                          (by simp only [evmBurn, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, storageStore_executionEnv, evmS, initState])
                          _hpostBurn
                          (by simp only [evmBurn, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, auctionStorageStore_σ₀, evmS, initState])
                          (by simp only [evmBurn, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, auctionStorageStore_genesisBlockHeader, evmS, initState])
                          (by simp only [evmBurn, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, auctionStorageStore_blocks, evmS, initState])
                          hm (by native_decide) rdRet
                      · sorry
                  · have hdepthEq : I.depth = 1024 := by
                      apply Fin.ext
                      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                      have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
                      omega
                    have hrdFail := auctionInternalSettleAuction_revert_burnDepthLimit
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (ret := (⟨2690⟩ : UInt256)) hbidderZero hnounsCode hdepthEq
                      hmarkReach
                    have hbody :=
                      auctionSettleAndCreateTransitionReverts_settleBurnDepthLimit evmS
                        (by simp only [evmS, initState]; exact hwv)
                        hstatusSolm hpausedSolm hstartSolm hsettledSolm htimeSolmLe
                        hbidderSolm hnounsCodeSolmEval
                        (by simpa [evmS, initState] using hdepthEq)
                    exact hrdFail.reEquivExecutionRevert _hcode hdispatch hdecode hbody
              · by_cases hnounsNoCode :
                    Reasoning.Theory.uniswapExtCodeSizeWord
                        (auctionSettleAuctionMarkSettledMap
                          (auctionSettleAuctionEnterMap σ_evm I) I)
                        (UInt256.land
                          (auctionSlotWord ⟨201⟩
                            (auctionSettleAuctionMarkSettledMap
                              (auctionSettleAuctionEnterMap σ_evm I) I) I)
                          solcAddrMask) =
                      ⟨0⟩
                · let postEvm :=
                    auctionSettleAuctionMarkSettledMap
                      (auctionSettleAuctionEnterMap σ_evm I) I
                  let postSolm :=
                    auctionSettleAuctionMarkSettledMap
                      (auctionSettleAuctionEnterMap σ_solm I) I
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
                    apply hbidderEvm
                    have hpacked :
                        auctionAuctionPackedWord σ_evm I =
                          auctionAuctionPackedWord σ_solm I := by
                      simpa [auctionAuctionPackedWord] using hsettledWord
                    simpa [hpacked] using hzero
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
                    simpa [hload] using
                      auctionPackedBidderAddress_ne_zero (auctionAuctionPackedWord σ_solm I)
                        hbidderSolmWord
                  have henterEquiv :
                      accountMapEquiv (auctionSettleAuctionEnterMap σ_evm I)
                        (auctionSettleAuctionEnterMap σ_solm I) :=
                    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ _hAccounts
                  have hmarkValEq :
                      auctionSetBoolOffset20TrueWord
                          (auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_evm I) I) =
                        auctionSetBoolOffset20TrueWord
                          (auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I) := by
                    have hslot :=
                      accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨211⟩
                        (default : UInt256)
                    simpa [auctionSlotWord] using congrArg auctionSetBoolOffset20TrueWord hslot
                  have hpostEquiv : accountMapEquiv postEvm postSolm := by
                    dsimp [postEvm, postSolm, auctionSettleAuctionMarkSettledMap]
                    rw [hmarkValEq]
                    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
                      (auctionSetBoolOffset20TrueWord
                        (auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I))
                      henterEquiv
                  have hnounsTargetEq :
                      UInt256.land (auctionSlotWord ⟨201⟩ postEvm I) solcAddrMask =
                        UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask := by
                    have hslot :=
                      accountMapEquiv_storage_findD hpostEquiv I.codeOwner ⟨201⟩
                        (default : UInt256)
                    simpa [auctionSlotWord] using
                      congrArg (fun w => UInt256.land w solcAddrMask) hslot
                  have hnounsNoCodeSolm :
                      Reasoning.Theory.uniswapExtCodeSizeWord postSolm
                          (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask) =
                        ⟨0⟩ := by
                    have htmp :
                        Reasoning.Theory.uniswapExtCodeSizeWord postSolm
                            (UInt256.land (auctionSlotWord ⟨201⟩ postEvm I) solcAddrMask) =
                          ⟨0⟩ := by
                      rw [← uniswapExtCodeSizeWord_accountMapEquiv hpostEquiv
                        (UInt256.land (auctionSlotWord ⟨201⟩ postEvm I) solcAddrMask)]
                      simpa [postEvm] using hnounsNoCode
                    simpa [hnounsTargetEq] using htmp
                  have henterMapState :
                      accountMapEquiv (auctionSettleAuctionEnterMap σ_solm I)
                        evmEnter.accountMap := by
                    simpa [evmEnter, evmS] using
                      (auctionSettleAuctionEnterMap_accountMap
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g))
                  have henterOwner : evmEnter.executionEnv.codeOwner = I.codeOwner := by
                    simp [evmEnter, evmS, auctionSettleAuctionEnterState, initState,
                      storageStore_executionEnv]
                  have hmarkOwner : evmMark.executionEnv.codeOwner = I.codeOwner := by
                    simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
                      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
                  have hslotEnterPacked :
                      auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I =
                        Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                          ⟨211⟩ := by
                    have hslot :=
                      accountMapEquiv_storage_findD henterMapState I.codeOwner ⟨211⟩
                        (⟨0⟩ : UInt256)
                    simpa [henterOwner, auctionSlotWord, Solm.EVM.storageLoad,
                      State.lookupAccount, Account.lookupStorage] using hslot
                  have hslotEnterPackedI :
                      auctionSlotWord ⟨211⟩ (auctionSettleAuctionEnterMap σ_solm I) I =
                        Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩ := by
                    simpa [henterOwner] using hslotEnterPacked
                  have hpostMapState : accountMapEquiv postSolm evmMark.accountMap := by
                    dsimp [evmMark, auctionSettleAuctionMarkSettledState]
                    rw [henterOwner]
                    simp only [storageStore_accountMap]
                    dsimp [postSolm, auctionSettleAuctionMarkSettledMap]
                    rw [hslotEnterPackedI]
                    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
                      (auctionSetBoolOffset20TrueWord
                        (Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩))
                      henterMapState
                  have htargetMapSource :
                      UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask =
                        UInt256.land
                          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                            ⟨201⟩)
                          solcAddrMask := by
                    have hslotPost :
                        auctionSlotWord ⟨201⟩ postSolm I =
                          Solm.EVM.storageLoad evmMark evmMark.executionEnv.codeOwner
                            ⟨201⟩ := by
                      have hslot :=
                        accountMapEquiv_storage_findD hpostMapState I.codeOwner ⟨201⟩
                          (⟨0⟩ : UInt256)
                      simpa [hmarkOwner, auctionSlotWord, Solm.EVM.storageLoad,
                        State.lookupAccount, Account.lookupStorage] using hslot
                    have hslotMark := auctionSettleAuctionMarkSettledState_storageLoad_nouns
                      evmEnter
                    simpa [evmMark] using
                      congrArg (fun w => UInt256.land w solcAddrMask)
                        (hslotPost.trans hslotMark)
                  have hnounsNoCodeState :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
                          (UInt256.land
                            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                              ⟨201⟩)
                            solcAddrMask) =
                        ⟨0⟩ := by
                    have htmp :
                        Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
                            (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I)
                              solcAddrMask) =
                          ⟨0⟩ := by
                      rw [← uniswapExtCodeSizeWord_accountMapEquiv hpostMapState
                        (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask)]
                      exact hnounsNoCodeSolm
                    simpa [htargetMapSource] using htmp
                  have hlookup :
                      (UInt256.ofNat (((auctionSettleAuctionMarkSettledState evmEnter).lookupAccount
                        (AccountAddress.ofNat
                          ((UInt256.land
                            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                              ⟨201⟩)
                            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size))).toNat =
                        0 := by
                    let targetSource :=
                      UInt256.land
                        (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                          ⟨201⟩)
                        solcAddrMask
                    have hlookup0 :=
                      auctionUniswapExtCodeSizeWord_zero_lookup_code_zero
                        (σ := evmMark.accountMap) (target := targetSource)
                        (addr := AccountAddress.ofNat targetSource.toNat)
                        (by simp [accountAddress_ofUInt256_eq_ofNat_toNat])
                        (by simpa [targetSource] using hnounsNoCodeState)
                    simpa [evmMark, targetSource, State.lookupAccount] using hlookup0
                  have hnounsNoCodeSolmEval :
                      evalExpr? auctionConfig
                          { contract := auctionContract,
                            locals := auctionSettleAuctionSnapshotStore
                              (auctionSettleAuctionEnterState evmS) }
                          (auctionSettleAuctionMarkSettledState
                            (auctionSettleAuctionEnterState evmS))
                          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
                        .ok (.bool false) := by
                    simpa [evmEnter] using
                      evalExpr_settleAuction_nounsNoCode_after_markSettled evmEnter hlookup
                  have hbody := auctionSettleAndCreateTransitionReverts_settleTransferFromNoCode
                    evmS (by simp only [evmS, initState]; exact hwv) hstatusSolm hpausedSolm
                    hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsNoCodeSolmEval
                  exact (auctionInternalSettleAuction_revert_transferFromNoCode
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (ret := (⟨2690⟩ : UInt256)) hbidderZero hnounsNoCode hmarkReach)
                    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
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
                    apply hbidderEvm
                    have hpacked :
                        auctionAuctionPackedWord σ_evm I =
                          auctionAuctionPackedWord σ_solm I := by
                      simpa [auctionAuctionPackedWord] using hsettledWord
                    simpa [hpacked] using hzero
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
                    simpa [hload] using
                      auctionPackedBidderAddress_ne_zero (auctionAuctionPackedWord σ_solm I)
                        hbidderSolmWord
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
                      auctionInternalSettleAuction_transferFromPostCall
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g)
                        (ret := (⟨2690⟩ : UInt256)) _hperm hbidderZero hnounsCode
                        hdepth hmarkReach
                    obtain ⟨σ'_solm, A'_solm, hcallSolm, _hpostTf⟩ :=
                      auctionSettleAuctionTransferFromCall_accountMapEquiv
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) _hAccounts hcallEvm
                    let evmTf :=
                      { auctionSettleAuctionMarkSettledState
                          (auctionSettleAuctionEnterState evmS) with
                        accountMap := σ'_solm,
                        substate := A'_solm,
                        createdAccounts := cA' }
                    cases z
                    · have hrdFail : RDrev auctionBytecode (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
                        auctionSettleAuctionTransferFromCallFailure
                          (by simpa using hrdPost) hosz (by simp)
                      have hbody :=
                        auctionSettleAndCreateTransitionReverts_settleTransferFromCallFailure
                          evmS evmTf (by simp only [evmS, initState]; exact hwv)
                          hstatusSolm hpausedSolm hstartSolm hsettledSolm htimeSolmLe
                          hbidderSolm hnounsCodeSolmEval
                          (by simpa [evmTf] using hcallSolm)
                      exact hrdFail.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                    · by_cases hamountZero : auctionAuctionAmountWord
                          (auctionSettleAuctionEnterMap σ_evm I) I = ⟨0⟩
                      · have henterMap : accountMapEquiv
                            (auctionSettleAuctionEnterMap σ_evm I)
                            (auctionSettleAuctionEnterState evmS).accountMap :=
                          (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ _hAccounts).trans
                            auctionSettleAuctionEnterMap_accountMap
                        have hamountSolm : Solm.EVM.storageLoad
                            (auctionSettleAuctionEnterState evmS)
                            (auctionSettleAuctionEnterState evmS).executionEnv.codeOwner ⟨208⟩ = ⟨0⟩ := by
                          have hh := accountMapEquiv_storage_findD henterMap I.codeOwner ⟨208⟩ ⟨0⟩
                          simpa only [auctionSettleAuctionEnterState_executionEnv, evmS, initState,
                            Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                            auctionAuctionAmountWord, auctionSlotWord] using hh.symm.trans hamountZero
                        have hsettle := auctionSettleAuctionWithMemoryReturns_transferFromNoPayout
                          (auctionSettleAuctionEnterState evmS) evmTf
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨209⟩) (by decide)]
                            using hstartSolm)
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨211⟩) (by decide)]
                            using hsettledSolm)
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨210⟩) (by decide)]
                            using htimeSolmLe)
                          (by simpa only [auctionSettleAuctionEnterState_executionEnv,
                            auctionSettleAuctionEnterState_storageLoad_ne evmS (slot := ⟨211⟩) (by decide)]
                            using hbidderSolm)
                          hnounsCodeSolmEval (by simpa only [evmTf] using hcallSolm) hamountSolm
                        obtain ⟨_, _, rdEvent⟩ := auctionSettleAuctionTransferFromSuccessToNoPayoutEventAt hamountZero hrdPost
                        obtain ⟨memRet, awRet, kr, Cr, hm, rdRet⟩ := auctionSettleAndCreateEventReturn _hperm
                          (by rw [auctionSettleAuctionTransferFromMem_size]; decide)
                          (auctionSettleAuctionTransferFromMem_read64 ..) (by decide) (by decide) (by decide) (by decide)
                          (by rw [auctionSettleAuctionTransferFromMem_size]; native_decide) rdEvent
                        exact auctionSettleAndCreateFromSettleReturn _hcode _hperm hdispatch hdecode
                          hwv hstatusSolm hpausedSolm hdepth hsettle
                          (by simp only [evmTf, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, storageStore_executionEnv, evmS, initState])
                          _hpostTf
                          (by simp only [evmTf, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, auctionStorageStore_σ₀, evmS, initState])
                          (by simp only [evmTf, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, auctionStorageStore_genesisBlockHeader, evmS, initState])
                          (by simp only [evmTf, auctionSettleAuctionMarkSettledState,
                            auctionSettleAuctionEnterState, auctionStorageStore_blocks, evmS, initState])
                          hm (by native_decide) rdRet
                      · sorry
                  · have hdepthEq : I.depth = 1024 := by
                      apply Fin.ext
                      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                      have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
                      omega
                    have hrdFail := auctionInternalSettleAuction_revert_transferFromDepthLimit
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (ret := (⟨2690⟩ : UInt256)) hbidderZero hnounsCode hdepthEq
                      hmarkReach
                    have hbody :=
                      auctionSettleAndCreateTransitionReverts_settleTransferFromDepthLimit evmS
                        (by simp only [evmS, initState]; exact hwv)
                        hstatusSolm hpausedSolm hstartSolm hsettledSolm htimeSolmLe
                        hbidderSolm hnounsCodeSolmEval
                        (by simpa [evmS, initState] using hdepthEq)
                    exact hrdFail.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have hpausedSolm :
            UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
                ⟨255⟩ ≠
              ⟨0⟩ := by
          intro h
          apply hpausedZero
          have hmap : auctionPausedWord σ_solm I = ⟨0⟩ := by
            simpa [evmS, initState, auctionPausedWord, auctionSlotWord, Solm.EVM.storageLoad,
              State.lookupAccount] using h
          simpa [auctionPausedWord, hpausedWord] using hmap
        have hbody := auctionSettleAndCreateTransitionReverts_paused evmS
          (by simp only [evmS, initState]; exact hwv) hstatusSolm hpausedSolm
        exact (auctionX_settleCurrentAndCreateNewAuction_revert_paused
            (g := Sat256.ofUInt256 g) _hperm hwv hstatusEntered hpausedZero hreach)
          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          settleAndCreateTransition.body .reverted := by
      dsimp [settleAndCreateTransition, nonpayable]
      refine ExecFuncBody.execBlockRevert ?_
      exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false (by
        simpa only [initState] using hwv)))
    exact (auctionX_settleCurrentAndCreateNewAuction_callvalue_ne hreach hwv)
      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction

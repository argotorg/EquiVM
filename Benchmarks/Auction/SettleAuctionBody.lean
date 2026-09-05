import Benchmarks.Auction.SettleAuctionTransitions
import Benchmarks.Auction.SettleAuctionReturn
import Benchmarks.Auction.SettleAuctionTransferReturn
import Benchmarks.Auction.SettleAuctionDynamicWeth
import Benchmarks.Auction.SettleAuctionBurnBranchNoCode
import Benchmarks.Auction.SettleAuctionBurnBranchPayoutEmpty
import Benchmarks.Auction.SettleAuctionBurnBranchPayoutNonempty
import Benchmarks.Auction.SettleAuctionTransferBranch

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 13))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 13) rfl _hsel
  have hdispatch := auctionDispatch_settleAuction _hsel
  have hdecode := auctionDecode_settleAuction (I := I) hsz4
  have hreach := auctionReachSettleAuctionBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
      have hbody :
          ExecTransitionBody auctionConfig auctionContract evmS ∅
            settleAuctionTransition.body .reverted := by
        dsimp [settleAuctionTransition, nonpayable]
        refine ExecFuncBody.execBlockRevert ?_
        refine ExecBlock.consNormal
          (ExecStmt.requireTrue (evalCallvalueEq_true (by simpa [evmS, initState] using hwv))) ?_
        exact ExecBlock.consRevert
          (ExecStmt.requireFalse (evalExpr_pause_paused_false evmS hpausedSolm))
      exact (auctionX_settleAuction_revert_paused
          (g := Sat256.ofUInt256 g) hwv hpausedZero hreach)
        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
    · have hpausedSolm :
          UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
              ⟨255⟩ ≠
            ⟨0⟩ := by
        have hmap : auctionPausedWord σ_solm I ≠ ⟨0⟩ := by
          intro hzero
          exact hpausedZero (by
            simpa [auctionPausedWord, hpausedWord] using hzero)
        simpa [evmS, initState, auctionPausedWord, auctionSlotWord, Solm.EVM.storageLoad,
          State.lookupAccount] using hmap
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
        have hbody :
            ExecTransitionBody auctionConfig auctionContract evmS ∅
              settleAuctionTransition.body .reverted :=
          auctionSettleAuctionTransitionReverts_statusEntered evmS
            (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm
        exact (auctionX_settleAuction_revert_statusEntered
            (g := Sat256.ofUInt256 g) hwv hpausedZero hstatusEntered hreach)
          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have hstatusSolm :
            Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩ := by
          intro hbad
          have hmap : auctionSlotWord ⟨101⟩ σ_solm I = ⟨2⟩ := by
            simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
              using hbad
          exact hstatusEntered (by simpa [hstatusWord] using hmap)
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
          have hbody :
              ExecTransitionBody auctionConfig auctionContract evmS ∅
                settleAuctionTransition.body .reverted :=
            auctionSettleAuctionTransitionReverts_notStarted evmS
              (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm hstartSolm
          exact (auctionX_settleAuction_revert_notStarted
              (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered hstart hreach)
            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
        · have hstartSolm :
              Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩ := by
            intro hzero
            have hmap : auctionAuctionStartWord σ_solm I = ⟨0⟩ := by
              simpa [evmS, initState, auctionAuctionStartWord, auctionSlotWord,
                Solm.EVM.storageLoad, State.lookupAccount] using hzero
            exact hstart (by simpa [auctionAuctionStartWord, hstartWord] using hmap)
          have hsettledWord :
              auctionSlotWord ⟨211⟩ σ_evm I = auctionSlotWord ⟨211⟩ σ_solm I :=
            accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨211⟩ ⟨0⟩
          by_cases hsettled :
              auctionPackedSettledWord (auctionAuctionPackedWord σ_evm I) = ⟨0⟩
          · have hsettledSolm :
                auctionPackedSettledWord
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
                  ⟨0⟩ := by
              have hmap :
                  auctionPackedSettledWord (auctionAuctionPackedWord σ_solm I) = ⟨0⟩ := by
                simpa [auctionAuctionPackedWord, hsettledWord] using hsettled
              simpa [evmS, initState, auctionAuctionPackedWord, auctionSlotWord,
                Solm.EVM.storageLoad, State.lookupAccount] using hmap
            have hendWord :
                auctionSlotWord ⟨210⟩ σ_evm I = auctionSlotWord ⟨210⟩ σ_solm I :=
              accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨210⟩ ⟨0⟩
            by_cases htime :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (auctionAuctionEndWord σ_evm I).toNat
            · have htimeSolm :
                  (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat <
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat := by
                have hmap :
                    auctionAuctionEndWord σ_solm I = auctionAuctionEndWord σ_evm I := by
                  simpa [auctionAuctionEndWord] using hendWord.symm
                have htimeSolmWord :
                    (UInt256.ofNat I.header.timestamp).toNat <
                      (auctionAuctionEndWord σ_solm I).toNat := by
                  rwa [hmap]
                simpa [evmS, initState, auctionAuctionEndWord, auctionSlotWord,
                  Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, hmap]
                  using htimeSolmWord
              have hbody :
                  ExecTransitionBody auctionConfig auctionContract evmS ∅
                    settleAuctionTransition.body .reverted :=
                auctionSettleAuctionTransitionReverts_timeNotReached evmS
                  (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm hstartSolm
                  hsettledSolm htimeSolm
              exact (auctionX_settleAuction_revert_timeNotReached
                  (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered hstart
                  hsettled htime hreach)
                |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
            · by_cases hburnNoCode :
                auctionPackedBidderWord
                    (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I) =
                  ⟨0⟩ ∧
                Reasoning.Theory.uniswapExtCodeSizeWord
                    (auctionSettleAuctionMarkSettledMap
                      (auctionSettleAuctionEnterMap σ_evm I) I)
                    (UInt256.land
                      (auctionSlotWord ⟨201⟩
                        (auctionSettleAuctionMarkSettledMap
                          (auctionSettleAuctionEnterMap σ_evm I) I) I)
                      solcAddrMask) =
                  ⟨0⟩
              · rcases hburnNoCode with ⟨hbidderZero, hnounsNoCode⟩
                exact auctionSettleAuctionBodyBurnNoCodeBranch
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  _hcode _hperm _hAccounts hdispatch hdecode hreach hwv
                  hpausedZero (by simpa [evmS] using hpausedSolm)
                  hstatusEntered (by simpa [evmS] using hstatusSolm)
                  hstart (by simpa [evmS] using hstartSolm)
                  hsettled (by simpa [evmS] using hsettledSolm)
                  hendWord htime hsettledWord hbidderZero hnounsNoCode
              · by_cases hbidderZero :
                  auctionPackedBidderWord
                      (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I) =
                    ⟨0⟩
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
                    exact hburnNoCode ⟨hbidderZero, hzero⟩
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
                      auctionSettleAuctionX_burnPostCall
                        (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered
                        hstart hsettled htime hbidderZero hnounsCode hdepth hreach
                    cases z
                    · obtain ⟨σ'_solm, A'_solm, hcallSolm, _hpost⟩ :=
                        auctionSettleAuctionBurnCall_accountMapEquiv
                          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                          (I := I) (g := Sat256.ofUInt256 g) _hAccounts hcallEvm
                      have hrdFail :
                          RDrev auctionBytecode (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
                        auctionSettleAuctionBurnCallFailure
                          (rd := by simpa using hrdPost) hosz (by simp)
                      let evmBurn :=
                        { evmMark with
                          accountMap := σ'_solm,
                          substate := A'_solm,
                          createdAccounts := cA' }
                      have hbody :
                          ExecTransitionBody auctionConfig auctionContract evmS ∅
                            settleAuctionTransition.body .reverted :=
                        auctionSettleAuctionTransitionReverts_burnCallFailure evmS evmBurn
                          (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm
                          hstartSolm hsettledSolm htimeSolmLe hbidderSolm
                          hnounsCodeSolmEval (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
                      exact hrdFail.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                    · by_cases hamountZero :
                        auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I = ⟨0⟩
                      · obtain ⟨σ'_solm, A'_solm, hcallSolm, hpostBurn⟩ :=
                          auctionSettleAuctionBurnCall_accountMapEquiv
                            (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                            (I := I) (g := Sat256.ofUInt256 g) _hAccounts hcallEvm
                        let evmBurn :=
                          { evmMark with
                            accountMap := σ'_solm,
                            substate := A'_solm,
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
                        have hamountSolm :
                            Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                                ⟨208⟩ =
                              ⟨0⟩ := by
                          have hslot :=
                            accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨208⟩
                              (⟨0⟩ : UInt256)
                          have hload :
                              auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I =
                                Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner
                                  ⟨208⟩ := by
                            simpa [henterOwner, auctionAuctionAmountWord, auctionSlotWord,
                              Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                              using hslot
                          exact hload.symm.trans hamountZero
                        have hbody :
                            ExecTransitionBody auctionConfig auctionContract evmS ∅
                              settleAuctionTransition.body
                              (.returned
                                (resumeAfterInternalCall
                                  { contract := auctionContract, locals := ∅ } "_s" none)
                                (auctionSettleAuctionExitState evmBurn) none) :=
                          auctionSettleAuctionTransitionReturns_burnNoPayout evmS evmBurn
                            (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm
                            hstartSolm hsettledSolm htimeSolmLe hbidderSolm
                            hnounsCodeSolmEval
                            (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
                            hamountSolm
                        obtain ⟨_, _, hrdEvent⟩ :=
                          auctionSettleAuctionBurnSuccessToNoPayoutEvent
                            (target :=
                              UInt256.land
                                (auctionSlotWord ⟨201⟩
                                  (auctionSettleAuctionMarkSettledMap
                                    (auctionSettleAuctionEnterMap σ_evm I) I) I)
                                solcAddrMask)
                            hamountZero (rd := by simpa using hrdPost)
                        have hret :
                            RDret auctionBytecode (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              (cA', auctionSettleAuctionExitMap σ' I) ByteArray.empty :=
                          auctionSettleAuctionNoPayoutEventToReturn _hperm hrdEvent
                        have hcreated :
                            cA' = (auctionSettleAuctionExitState evmBurn).createdAccounts := by
                          simp [auctionSettleAuctionExitState, evmBurn, storageStore_createdAccounts]
                        have hburnOwner : evmBurn.executionEnv.codeOwner = I.codeOwner := by
                          simp [evmBurn, evmMark, evmEnter, evmS,
                            auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
                            initState, storageStore_executionEnv]
                        have hpostAccounts :
                            accountMapEquiv (auctionSettleAuctionExitMap σ' I)
                              (auctionSettleAuctionExitState evmBurn).accountMap := by
                          have hstore :=
                            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hpostBurn
                          simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
                            storageStore_accountMap, hburnOwner] using hstore
                        exact hret.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode
                          hbody hcreated hpostAccounts
                          (returnEquiv.fallthrough rfl rfl (by native_decide))
                      · obtain ⟨σ'_solm, A'_solm, hcallSolm, hpostBurn⟩ :=
                          auctionSettleAuctionBurnCall_accountMapEquiv
                            (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                            (I := I) (g := Sat256.ofUInt256 g) _hAccounts hcallEvm
                        let evmBurn :=
                          { evmMark with
                            accountMap := σ'_solm,
                            substate := A'_solm,
                            createdAccounts := cA' }
                        obtain ⟨_, _, hrdPayEntry⟩ :=
                          auctionSettleAuctionBurnSuccessToPayoutEntry
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
                          auctionSettleAuctionPayoutEntryToCall hownerWordMasked
                            (rd := hrdPayEntry)
                        let amountWord :=
                          auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
                        let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
                        let evmBurnE :=
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
                            { evmBurnE with
                                accountMap := σPay,
                                substate := APay,
                                createdAccounts := cAPay }
                          have hpayEvmRaw :
                              callViaEVM evmBurnE (AccountAddress.ofUInt256 ownerWord)
                                (Int.ofNat amountWord.toNat) ByteArray.empty
                                (zPay, evmPayE, outPay) true := by
                            refine callViaEVM.callMade
                              (valueWord := amountWord) (cA' := cAPay) (σ' := σPay)
                              (g' := gPay'') (A' := APay)
                              (wordOfInt_ofNat_toNat amountWord).symm
                              ⟨callGasPay, AInPay, ?_⟩ (by simp [evmPayE])
                              ?_ ?_
                            · simpa [evmBurnE, initState, accountAddress_roundtrip, _hperm]
                                using hThetaPay
                            · simpa [evmBurnE, initState, amountWord] using hpayBalance
                            · simp [evmBurnE, initState]
                              intro hbad
                              have hbadVal : I.depth.val = 1024 := by
                                exact congrArg Fin.val hbad
                              omega
                          cases zPay
                          · have hpayEvmFalse :
                                  callViaEVM evmBurnE (AccountAddress.ofUInt256 ownerWord)
                                    (Int.ofNat amountWord.toNat) ByteArray.empty
                                    (false, evmPayE, outPay) true := by
                                  simpa using hpayEvmRaw
                            obtain ⟨σPaySolm, APaySolm, hpaySolmRaw, hpostPay⟩ :=
                              auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
                                (evm_evm := evmBurnE) (evm_solm := evmBurn)
                                (tgt := AccountAddress.ofUInt256 ownerWord)
                                (value := Int.ofNat amountWord.toNat) (calldata := ByteArray.empty)
                                (out := outPay) (cA' := cAPay) (σ' := σPay)
                                (A' := APay) (A_in := AInPay) (z := false)
                                (g'' := gPay'') (callGas := callGasPay)
                                (valueWord := amountWord) (callPerm := true)
                                (wordOfInt_ofNat_toNat amountWord).symm
                                (by
                                  simpa [evmBurnE, initState, accountAddress_roundtrip, _hperm,
                                    amountWord, ownerWord] using hThetaPay)
                                (by simpa [evmBurnE, initState] using hpayBalance)
                                (by
                                  simp [evmBurnE, initState]
                                  intro hbad
                                  have hbadVal : I.depth.val = 1024 := by
                                    exact congrArg Fin.val hbad
                                  omega)
                                (by simpa [evmBurnE, evmBurn] using hpostBurn)
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    auctionStorageStore_σ₀])
                                (by simp [evmBurnE, evmBurn])
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    auctionStorageStore_genesisBlockHeader])
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    auctionStorageStore_blocks])
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    storageStore_executionEnv])
                            let evmPay :=
                              { evmBurn with
                                  accountMap := σPaySolm,
                                  substate := APaySolm,
                                  createdAccounts := evmPayE.createdAccounts }
                            have hpaySolm :
                                callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
                                  (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
                                  ByteArray.empty (false, evmPay, outPay) true := by
                              rw [hownerEq, ← hamountEq]
                              exact hpaySolmRaw
                            by_cases houtZero : outPay.size = 0
                            · exact auctionSettleAuctionBodyBurnPayoutFailureEmptyCase
                                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (cA' := cA') (cAPay := cAPay)
                                (σ' := σ') (σ'_solm := σ'_solm)
                                (σPay := σPay) (σPaySolm := σPaySolm)
                                (A' := A') (A'_solm := A'_solm)
                                (APay := APay) (APaySolm := APaySolm)
                                (o := o) (outPay := outPay) (kPay := kPay) (CPay := CPay)
                                _hcode _hperm hdispatch hdecode hwv
                                (by simpa [evmS] using hpausedSolm)
                                (by simpa [evmS] using hstatusSolm)
                                (by simpa [evmS] using hstartSolm)
                                (by simpa [evmS] using hsettledSolm)
                                (by simpa [evmS] using htimeSolmLe)
                                (by simpa [evmS] using hbidderSolm)
                                (by simpa [evmS] using hnounsCodeSolmEval)
                                (by simpa [evmS, evmEnter, evmMark, evmBurn] using hcallSolm)
                                hpostBurn
                                (by simpa [evmS, evmEnter, amountWord] using hamountEq)
                                (by simpa [evmS, evmEnter] using hamountSolm)
                                hdepth
                                (by
                                  simpa [evmS, evmEnter, evmMark, evmBurn, evmBurnE,
                                    evmPayE, evmPay] using hpaySolm)
                                hpostPay houtZero
                                (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                            · exact
                                auctionSettleAuctionBodyBurnPayoutFailureNonemptyCase
                                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                  (cA' := cA') (cAPay := cAPay)
                                  (σ' := σ') (σ'_solm := σ'_solm)
                                  (σPay := σPay) (σPaySolm := σPaySolm)
                                  (A' := A') (A'_solm := A'_solm)
                                  (APay := APay) (APaySolm := APaySolm)
                                  (o := o) (outPay := outPay) (kPay := kPay) (CPay := CPay)
                                  _hcode _hperm hdispatch hdecode hwv
                                  (by simpa [evmS] using hpausedSolm)
                                  (by simpa [evmS] using hstatusSolm)
                                  (by simpa [evmS] using hstartSolm)
                                  (by simpa [evmS] using hsettledSolm)
                                  (by simpa [evmS] using htimeSolmLe)
                                  (by simpa [evmS] using hbidderSolm)
                                  (by simpa [evmS] using hnounsCodeSolmEval)
                                  (by simpa [evmS, evmEnter, evmMark, evmBurn] using hcallSolm)
                                  hpostBurn
                                  (by simpa [evmS, evmEnter, amountWord] using hamountEq)
                                  (by simpa [evmS, evmEnter] using hamountSolm)
                                  hdepth
                                  (by
                                    simpa [evmS, evmEnter, evmMark, evmBurn, evmBurnE,
                                      evmPayE, evmPay] using hpaySolm)
                                  hpostPay houtPaySize houtZero
                                  (by
                                    exact Theta_returnData_size_lt_2pow138_of_eq
                                      (hΘ := by
                                        simpa [evmBurnE, initState, accountAddress_roundtrip,
                                          _hperm, amountWord, ownerWord] using hThetaPay)
                                      (hd := by simp))
                                  (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                          · have hpayEvmTrue :
                                    callViaEVM evmBurnE (AccountAddress.ofUInt256 ownerWord)
                                      (Int.ofNat amountWord.toNat) ByteArray.empty
                                      (true, evmPayE, outPay) true := by
                                  simpa using hpayEvmRaw
                            obtain ⟨σPaySolm, APaySolm, hpaySolmRaw, hpostPay⟩ :=
                              auctionCallViaEVM_callMade_accountMapEquiv_perm
                                (storage := auctionConfig.storage) (evm_solm := evmBurn)
                                hpayEvmTrue
                                (by simpa [evmBurnE, evmBurn] using hpostBurn)
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    auctionStorageStore_σ₀])
                                (by simp [evmBurnE, evmBurn])
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    auctionStorageStore_genesisBlockHeader])
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    auctionStorageStore_blocks])
                                (by
                                  simp [evmBurnE, evmBurn, evmMark, evmEnter, evmS,
                                    auctionSettleAuctionMarkSettledState,
                                    auctionSettleAuctionEnterState, initState,
                                    storageStore_executionEnv])
                            let evmPay :=
                              { evmBurn with
                                  accountMap := σPaySolm,
                                  substate := APaySolm,
                                  createdAccounts := evmPayE.createdAccounts }
                            have hpaySolm :
                                callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
                                  (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
                                  ByteArray.empty (true, evmPay, outPay) true := by
                              rw [hownerEq, ← hamountEq]
                              exact hpaySolmRaw
                            by_cases houtZero : outPay.size = 0
                            · obtain ⟨_, _, hrdEvent⟩ :=
                                auctionSettleAuctionPayoutCallSuccessEmptyReturnToEvent
                                  houtZero
                                  (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                              have hret :
                                  RDret auctionBytecode (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (cAPay, auctionSettleAuctionExitMap σPay I)
                                    ByteArray.empty :=
                                auctionSettleAuctionEventToReturn _hperm hrdEvent
                              have hbody :
                                  ExecTransitionBody auctionConfig auctionContract evmS ∅
                                    settleAuctionTransition.body
                                    (.returned
                                      (resumeAfterInternalCall
                                        { contract := auctionContract, locals := ∅ } "_s" none)
                                      (auctionSettleAuctionExitState evmPay) none) :=
                                auctionSettleAuctionTransitionReturns_burnPayoutLowLevelSuccess
                                  evmS evmBurn evmPay
                                  (by simpa [evmS, initState] using hwv) hpausedSolm
                                  hstatusSolm hstartSolm hsettledSolm htimeSolmLe
                                  hbidderSolm hnounsCodeSolmEval
                                  (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
                                  hamountSolm hpaySolm
                              have hcreated :
                                  cAPay =
                                    (auctionSettleAuctionExitState evmPay).createdAccounts := by
                                simp [auctionSettleAuctionExitState, evmPay, evmPayE,
                                  storageStore_createdAccounts]
                              have hpayOwner :
                                  evmPay.executionEnv.codeOwner = I.codeOwner := by
                                simp [evmPay, evmBurn, evmMark, evmEnter, evmS,
                                  auctionSettleAuctionMarkSettledState,
                                  auctionSettleAuctionEnterState, initState,
                                  storageStore_executionEnv]
                              have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
                                simpa [evmPayE, evmPay] using hpostPay
                              have hpostAccounts :
                                  accountMapEquiv (auctionSettleAuctionExitMap σPay I)
                                    (auctionSettleAuctionExitState evmPay).accountMap := by
                                have hstore :=
                                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩
                                    hpostPayAccounts
                                simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
                                  storageStore_accountMap, hpayOwner] using hstore
                              exact hret.reEquivExecutionGenAccountMapEquiv _hcode hdispatch
                                hdecode hbody hcreated hpostAccounts
                                (returnEquiv.fallthrough rfl rfl (by native_decide))
                            · obtain ⟨_, _, _, _, hrdEvent⟩ :=
                                auctionSettleAuctionPayoutCallSuccessNonemptyReturnToEvent
                                  houtPaySize houtZero
                                  (by simpa [amountWord, ownerWord] using hrdAfterPayRaw)
                              have hret :
                                  RDret auctionBytecode (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (cAPay, auctionSettleAuctionExitMap σPay I)
                                    ByteArray.empty :=
                                auctionSettleAuctionEventToReturn _hperm hrdEvent
                              have hbody :
                                  ExecTransitionBody auctionConfig auctionContract evmS ∅
                                    settleAuctionTransition.body
                                    (.returned
                                      (resumeAfterInternalCall
                                        { contract := auctionContract, locals := ∅ } "_s" none)
                                      (auctionSettleAuctionExitState evmPay) none) :=
                                auctionSettleAuctionTransitionReturns_burnPayoutLowLevelSuccess
                                  evmS evmBurn evmPay
                                  (by simpa [evmS, initState] using hwv) hpausedSolm
                                  hstatusSolm hstartSolm hsettledSolm htimeSolmLe
                                  hbidderSolm hnounsCodeSolmEval
                                  (by simpa [evmBurn, evmMark, evmEnter] using hcallSolm)
                                  hamountSolm hpaySolm
                              have hcreated :
                                  cAPay =
                                    (auctionSettleAuctionExitState evmPay).createdAccounts := by
                                simp [auctionSettleAuctionExitState, evmPay, evmPayE,
                                  storageStore_createdAccounts]
                              have hpayOwner :
                                  evmPay.executionEnv.codeOwner = I.codeOwner := by
                                simp [evmPay, evmBurn, evmMark, evmEnter, evmS,
                                  auctionSettleAuctionMarkSettledState,
                                  auctionSettleAuctionEnterState, initState,
                                  storageStore_executionEnv]
                              have hpostPayAccounts : accountMapEquiv σPay σPaySolm := by
                                simpa [evmPayE, evmPay] using hpostPay
                              have hpostAccounts :
                                  accountMapEquiv (auctionSettleAuctionExitMap σPay I)
                                    (auctionSettleAuctionExitState evmPay).accountMap := by
                                have hstore :=
                                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩
                                    hpostPayAccounts
                                simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
                                  storageStore_accountMap, hpayOwner] using hstore
                              exact hret.reEquivExecutionGenAccountMapEquiv _hcode hdispatch
                                hdecode hbody hcreated hpostAccounts
                                (returnEquiv.fallthrough rfl rfl (by native_decide))
                        · obtain ⟨kAfterPay, CAfterPay, hrdAfterPayRaw⟩ :=
                            RD.callValueInsufficientBalanceEmptyInOut hrdPayCall _hperm
                              (by native_decide)
                              (by simpa [amountWord] using hpayBalance) hdepth
                              (by simpa [amountWord, ownerWord] using hpayStackLen)
                          have hawPay :
                              UInt256.ofNat
                                  (MachineState.M
                                    (MachineState.M (UInt256.ofNat 12).toNat
                                      (⟨352⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)
                                    (⟨352⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
                                UInt256.ofNat 12 := by
                            native_decide
                          have hrdAfterPay :
                              RD auctionBytecode I (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                ⟨4828⟩
                                [⟨0⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩,
                                  ⟨0⟩, amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord,
                                  ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
                                (auctionSettleAuctionPayoutLoopMem
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
                                      (auctionSettleAuctionEnterMap σ_evm I) I)))
                                (UInt256.ofNat 12) ByteArray.empty (cA', σ')
                                kAfterPay CAfterPay := by
                            have htmp := hrdAfterPayRaw
                            rw [hawPay] at htmp
                            simpa [amountWord, ownerWord] using htmp
                          obtain ⟨_, _, hrdFallback⟩ :=
                            auctionSettleAuctionPayoutCallFailureEmptyReturnToFallback
                              rfl hrdAfterPay
                          let payTarget := EVM.address (auctionOwnerAddressAt evmBurn)
                          let evmPay :=
                            { evmBurn with
                              substate := (evmBurn.addAccessedAccount payTarget).substate }
                          have hbalanceEq :
                              ((σ'.find? I.codeOwner).elim (⟨0⟩ : UInt256)
                                  (fun acc => acc.balance)) =
                                ((σ'_solm.find? I.codeOwner).elim
                                  (⟨0⟩ : UInt256) (fun acc => acc.balance)) := by
                            have hmap := hpostBurn I.codeOwner
                            cases hσ : σ'.find? I.codeOwner <;>
                              cases hτ : σ'_solm.find? I.codeOwner <;>
                              simp [hσ, hτ] at hmap ⊢
                            exact hmap.2.1
                          have hbalanceSolm :
                              ¬ amountWord ≤
                                (evmBurn.accountMap.find? evmBurn.executionEnv.codeOwner
                                  |>.elim ⟨0⟩ (·.balance)) := by
                            intro hbal
                            apply hpayBalance
                            rw [hbalanceEq]
                            simpa [evmBurn, evmMark, evmEnter, evmS,
                              auctionSettleAuctionMarkSettledState,
                              auctionSettleAuctionEnterState, initState,
                              storageStore_executionEnv] using hbal
                          have hbalancePaySolm :
                              ¬ amountWord ≤
                                (evmPay.accountMap.find? evmPay.executionEnv.codeOwner
                                  |>.elim ⟨0⟩ (·.balance)) := by
                            simpa [evmPay] using hbalanceSolm
                          have hpaySolm :
                              callViaEVM evmBurn payTarget
                                (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
                                ByteArray.empty (false, evmPay, ByteArray.empty) true := by
                            rw [← hamountEq]
                            apply callViaEVM.callNotMade
                            · rfl
                            · rfl
                            · intro hmade
                              have hmadeBalance := hmade.1
                              rw [wordOfInt_ofNat_toNat amountWord] at hmadeBalance
                              exact hbalanceSolm hmadeBalance
                          have hpayOwner : evmPay.executionEnv.codeOwner = I.codeOwner := by
                            simpa [evmPay] using hburnOwner
                          have hmarkOwner : evmMark.executionEnv.codeOwner = I.codeOwner := by
                            simpa [evmBurn] using hburnOwner
                          by_cases hwethCodeE :
                              Reasoning.Theory.uniswapExtCodeSizeWord σ'
                                  (UInt256.land (auctionSlotWord ⟨202⟩ σ' I)
                                    solcAddrMask) ≠
                                ⟨0⟩
                          · obtain ⟨gasWord, kDep, CDep, hrdDepositCall⟩ :=
                              auctionSettleAuctionPayoutFallbackToDepositCall hwethCodeE
                                hrdFallback
                            let memDeposit :=
                              auctionSettleAuctionWethDepositMem
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
                            let wethWord :=
                              UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
                            obtain ⟨kAfterDep, CAfterDep, hrdAfterDepRaw⟩ :=
                              RD.callValueInsufficientBalance hrdDepositCall _hperm
                                (by native_decide)
                                (by simpa [amountWord] using hpayBalance)
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
                                  (cA', σ') kAfterDep CAfterDep := by
                              have htmp := hrdAfterDepRaw
                              rw [hmin, byteArray_write_len_zero, hawDep] at htmp
                              simpa [amountWord, ownerWord, memDeposit, wethWord] using htmp
                            let evmDeposit :=
                              { evmPay with
                                substate :=
                                  (evmPay.addAccessedAccount
                                    (AccountAddress.ofUInt256 wethWord)).substate }
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
                                exact hbalancePaySolm hmadeBalance
                            have hwethSlotPay :
                                auctionSlotWord ⟨202⟩ σ' I =
                                  auctionSlotWord ⟨202⟩ σ'_solm I := by
                              exact accountMapEquiv_storage_findD hpostBurn
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
                                      auctionSlotWord ⟨202⟩ σ'_solm I := by
                                  simp [evmPay, evmBurn, Solm.EVM.storageLoad,
                                    State.lookupAccount, Account.lookupStorage,
                                    auctionSlotWord, hmarkOwner]
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
                                      (auctionSlotWord ⟨202⟩ σ' I))
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
                                      auctionSlotWord ⟨202⟩ σ'_solm I := by
                                  simp [evmPay, evmBurn, Solm.EVM.storageLoad,
                                    State.lookupAccount, Account.lookupStorage,
                                    auctionSlotWord, hmarkOwner]
                                unfold wethWord
                                rw [hslot, ← hwethSlotPay]
                              have hwethCodePay :
                                  0 < (UInt256.ofNat
                                    ((σ'.find? (AccountAddress.ofUInt256 wethWord)).option
                                      0 (fun acc => acc.code.size))).toNat := by
                                exact auctionUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
                                  (σ := σ') (target := wethWord)
                                  (addr := AccountAddress.ofUInt256 wethWord) rfl
                                  (by simpa [wethWord] using hwethCodeE)
                              have hcodeEq :
                                  UInt256.ofNat
                                      ((σ'.find? (AccountAddress.ofUInt256 wethWord)).option
                                        0 (fun acc => acc.code.size)) =
                                    UInt256.ofNat
                                      ((σ'_solm.find?
                                        (AccountAddress.ofUInt256 wethWord)).option
                                        0 (fun acc => acc.code.size)) := by
                                let wethAddr := AccountAddress.ofUInt256 wethWord
                                have hpayOpt :
                                    UInt256.ofNat
                                        ((σ'.find? wethAddr).option 0
                                          (fun acc => acc.code.size)) =
                                      ((σ'.find? wethAddr).option (⟨0⟩ : UInt256)
                                        (fun acc => UInt256.ofNat acc.code.size)) := by
                                  cases σ'.find? wethAddr <;> rfl
                                have hsolmOpt :
                                    UInt256.ofNat
                                        ((σ'_solm.find? wethAddr).option 0
                                          (fun acc => acc.code.size)) =
                                      ((σ'_solm.find? wethAddr).option (⟨0⟩ : UInt256)
                                        (fun acc => UInt256.ofNat acc.code.size)) := by
                                  cases σ'_solm.find? wethAddr <;> rfl
                                rw [hpayOpt, hsolmOpt]
                                exact accountMapEquiv_code_size_word hpostBurn wethAddr
                              have hcodeNatEq := congrArg UInt256.toNat hcodeEq
                              have hcodeSolm :
                                  0 < (UInt256.ofNat
                                    ((σ'_solm.find?
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
                                UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
                            have hwethCodeZero :
                                Reasoning.Theory.uniswapExtCodeSizeWord σ'
                                    (UInt256.land (auctionSlotWord ⟨202⟩ σ' I)
                                      solcAddrMask) =
                                  ⟨0⟩ := by
                              by_contra hne
                              exact hwethCodeE hne
                            have hrdNoCodeRev :
                                RDrev auctionBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀
                                    (Sat256.ofUInt256 g) A I) :=
                              auctionSettleAuctionPayoutFallbackWethNoCodeRevert
                                hwethCodeZero hrdFallback
                            have hwethSlotPay :
                                auctionSlotWord ⟨202⟩ σ' I =
                                  auctionSlotWord ⟨202⟩ σ'_solm I := by
                              exact accountMapEquiv_storage_findD hpostBurn
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
                                    auctionSlotWord ⟨202⟩ σ'_solm I := by
                                simp [evmPay, evmBurn, Solm.EVM.storageLoad,
                                  State.lookupAccount, Account.lookupStorage, auctionSlotWord,
                                  hmarkOwner]
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
                                    ((σ'.find? (AccountAddress.ofUInt256 wethWord)).option
                                      0 (fun acc => acc.code.size))).toNat = 0 := by
                                exact auctionUniswapExtCodeSizeWord_zero_lookup_code_zero
                                  (σ := σ') (target := wethWord)
                                  (addr := AccountAddress.ofUInt256 wethWord) rfl
                                  (by simpa [wethWord] using hwethCodeZero)
                              have hcodeEq :
                                  UInt256.ofNat
                                      ((σ'.find? (AccountAddress.ofUInt256 wethWord)).option
                                        0 (fun acc => acc.code.size)) =
                                    UInt256.ofNat
                                      ((σ'_solm.find?
                                        (AccountAddress.ofUInt256 wethWord)).option
                                        0 (fun acc => acc.code.size)) := by
                                let wethAddr := AccountAddress.ofUInt256 wethWord
                                have hpayOpt :
                                    UInt256.ofNat
                                        ((σ'.find? wethAddr).option 0
                                          (fun acc => acc.code.size)) =
                                      ((σ'.find? wethAddr).option (⟨0⟩ : UInt256)
                                        (fun acc => UInt256.ofNat acc.code.size)) := by
                                  cases σ'.find? wethAddr <;> rfl
                                have hsolmOpt :
                                    UInt256.ofNat
                                        ((σ'_solm.find? wethAddr).option 0
                                          (fun acc => acc.code.size)) =
                                      ((σ'_solm.find? wethAddr).option (⟨0⟩ : UInt256)
                                        (fun acc => UInt256.ofNat acc.code.size)) := by
                                  cases σ'_solm.find? wethAddr <;> rfl
                                rw [hpayOpt, hsolmOpt]
                                exact accountMapEquiv_code_size_word hpostBurn wethAddr
                              have hcodeNatEq := congrArg UInt256.toNat hcodeEq
                              have hcodeSolm :
                                  (UInt256.ofNat
                                    ((σ'_solm.find?
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
                  · have hdepthEq : I.depth = 1024 := by
                      apply Fin.ext
                      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                      have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
                      omega
                    let nounSolm :=
                      Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩
                    let burnTargetSolm : EVM.Address := EVM.address (AccountAddress.ofNat
                      ((UInt256.land
                        (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
                        solcAddrMask).toNat))
                    let evmBurn :=
                      { evmMark with
                        substate := (evmMark.addAccessedAccount burnTargetSolm).substate }
                    have hdepthMark : evmMark.executionEnv.depth = 1024 := by
                      simpa [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
                        auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
                        using hdepthEq
                    have hcallSolm :
                        typedCallViaEVM auctionConfig evmMark burnTargetSolm "burn" 0
                          [.int (Int.ofNat nounSolm.toNat)]
                          (false, evmBurn, ByteArray.empty) true := by
                      exact callNotMade_depthLimit
                        (cfg := auctionConfig) (evm := evmMark) (tgt := burnTargetSolm)
                        (name := "burn") (args := [.int (Int.ofNat nounSolm.toNat)])
                        (calldata := (auctionSettleAuctionBurnCallMem nounSolm
                          ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩).readWithPadding 320 36)
                        (callPerm := true)
                        (auctionSettleAuctionBurnEncode_eq nounSolm
                          ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩)
                        hdepthMark
                    have hbody :
                        ExecTransitionBody auctionConfig auctionContract evmS ∅
                          settleAuctionTransition.body .reverted :=
                      auctionSettleAuctionTransitionReverts_burnCallFailure evmS evmBurn
                        (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm
                        hstartSolm hsettledSolm htimeSolmLe hbidderSolm
                        hnounsCodeSolmEval
                        (by simpa [evmBurn, evmMark, evmEnter, burnTargetSolm, nounSolm]
                          using hcallSolm)
                    exact (auctionSettleAuctionX_revert_burnDepthLimit
                        (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered
                        hstart hsettled htime hbidderZero hnounsCode hdepthEq hreach)
                      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                · exact auctionSettleAuctionBodyTransferFromBranch
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) _hcode _hperm _hAccounts hdispatch hdecode hreach hwv
                    hpausedZero (by simpa [evmS] using hpausedSolm)
                    hstatusEntered (by simpa [evmS] using hstatusSolm)
                    hstart (by simpa [evmS] using hstartSolm)
                    hsettled (by simpa [evmS] using hsettledSolm)
                    hendWord htime hsettledWord hbidderZero
          · have hsettledSolm :
                auctionPackedSettledWord
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) ≠
                  ⟨0⟩ := by
              have hmap :
                  auctionPackedSettledWord (auctionAuctionPackedWord σ_solm I) ≠ ⟨0⟩ := by
                intro hzero
                exact hsettled (by simpa [auctionAuctionPackedWord, hsettledWord] using hzero)
              simpa [evmS, initState, auctionAuctionPackedWord, auctionSlotWord,
                Solm.EVM.storageLoad, State.lookupAccount] using hmap
            have hbody :
                ExecTransitionBody auctionConfig auctionContract evmS ∅
                  settleAuctionTransition.body .reverted :=
              auctionSettleAuctionTransitionReverts_alreadySettled evmS
                (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm hstartSolm
                hsettledSolm
            exact (auctionX_settleAuction_revert_alreadySettled
                (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered hstart
                hsettled hreach)
              |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          settleAuctionTransition.body .reverted := by
      dsimp [settleAuctionTransition, nonpayable]
      exact bodyReverts_nonPayable (by simpa [initState] using hwv)
    exact (auctionX_settleAuction_callvalue_ne hreach hwv)
      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction

import Benchmarks.Auction.SettleAuctionTransitions

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionBodyBurnNoCodeBranch {cA gh bl σ_evm σ_solm σ₀ A I}
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
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I) =
        ⟨0⟩)
    (hnounsNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
          (auctionSettleAuctionMarkSettledMap
            (auctionSettleAuctionEnterMap σ_evm I) I)
          (UInt256.land
            (auctionSlotWord ⟨201⟩
              (auctionSettleAuctionMarkSettledMap
                (auctionSettleAuctionEnterMap σ_evm I) I) I)
            solcAddrMask) =
        ⟨0⟩) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let postEvm :=
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
        Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩ := by
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
          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask := by
    have hslotPost :
        auctionSlotWord ⟨201⟩ postSolm I =
          Solm.EVM.storageLoad evmMark evmMark.executionEnv.codeOwner ⟨201⟩ := by
      have hslot :=
        accountMapEquiv_storage_findD hpostMapState I.codeOwner ⟨201⟩
          (⟨0⟩ : UInt256)
      simpa [hmarkOwner, auctionSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage] using hslot
    have hslotMark := auctionSettleAuctionMarkSettledState_storageLoad_nouns evmEnter
    simpa [evmMark] using
      congrArg (fun w => UInt256.land w solcAddrMask)
        (hslotPost.trans hslotMark)
  have hnounsNoCodeState :
      Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask) =
        ⟨0⟩ := by
    have htmp :
        Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
            (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask) =
          ⟨0⟩ := by
      rw [← uniswapExtCodeSizeWord_accountMapEquiv hpostMapState
        (UInt256.land (auctionSlotWord ⟨201⟩ postSolm I) solcAddrMask)]
      exact hnounsNoCodeSolm
    simpa [htargetMapSource] using htmp
  have hlookup :
      (UInt256.ofNat (((auctionSettleAuctionMarkSettledState evmEnter).lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size))).toNat = 0 := by
    let targetSource :=
      UInt256.land
        (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
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
  have hbody :
      ExecTransitionBody auctionConfig auctionContract evmS ∅
        settleAuctionTransition.body .reverted :=
    auctionSettleAuctionTransitionReverts_burnNoCode evmS
      (by simpa only [evmS, initState] using hwv) hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm hnounsNoCodeSolmEval
  exact (auctionSettleAuctionX_revert_burnNoCode
      (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered
      hstart hsettled htime hbidderZero hnounsNoCode hreach)
    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction

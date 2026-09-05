import Benchmarks.Auction.SettleAuctionTransferBranchNoCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchNoPayoutCase {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' σ'_solm : AccountMap}
    {A'_solm : Substate} {o : ByteArray} {k C : ℕ}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
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
        (true,
          { evmMark with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) true)
    (hpostTf : accountMapEquiv σ' σ'_solm)
    (hrdPost :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let nounWord := auctionAuctionNounWord σ1 I
      let amountWord := auctionAuctionAmountWord σ1 I
      let startWord := auctionAuctionStartWord σ1 I
      let finishWord := auctionAuctionEndWord σ1 I
      let packedWord := auctionAuctionPackedWord σ1 I
      let bidderWord := auctionPackedBidderWord packedWord
      let settledWord := auctionPackedSettledEVMReturnWord packedWord
      let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
      let targetWord := UInt256.land (auctionSlotWord ⟨201⟩ σ2 I) solcAddrMask
      let callerWord := UInt256.ofNat I.codeOwner.val
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4628⟩
        (⟨1⟩ :: ⟨420⟩ :: ⟨599290589⟩ :: targetWord ::
          ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
        (auctionSettleAuctionTransferFromMem nounWord amountWord startWord
          finishWord bidderWord settledWord callerWord)
        (UInt256.ofNat 14) o (cA', σ') k C)
    (hamountZero :
      auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I = ⟨0⟩) :
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
          (auctionSettleAuctionExitState evmTf) none) :=
    auctionSettleAuctionTransitionReturns_transferFromNoPayout evmS evmTf
      (by simpa [evmS, initState] using hwv) hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm
      hnounsCodeSolmEval
      (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
      hamountSolm
  obtain ⟨_, _, hrdEvent⟩ :=
    let σ1 := auctionSettleAuctionEnterMap σ_evm I
    let nounWord := auctionAuctionNounWord σ1 I
    let amountWord := auctionAuctionAmountWord σ1 I
    let startWord := auctionAuctionStartWord σ1 I
    let finishWord := auctionAuctionEndWord σ1 I
    let packedWord := auctionAuctionPackedWord σ1 I
    let bidderWord := auctionPackedBidderWord packedWord
    let settledWord := auctionPackedSettledEVMReturnWord packedWord
    let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
    let targetWord := UInt256.land (auctionSlotWord ⟨201⟩ σ2 I) solcAddrMask
    let callerWord := UInt256.ofNat I.codeOwner.val
    have hrdPostNoPayout :
        RD auctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4628⟩
          (⟨1⟩ :: ⟨420⟩ :: ⟨599290589⟩ :: targetWord ::
            ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
          (auctionSettleAuctionTransferFromMem nounWord amountWord startWord
            finishWord bidderWord settledWord callerWord)
          (UInt256.ofNat 14) o (cA', σ') k C := by
      simpa [σ1, nounWord, amountWord, startWord, finishWord, packedWord,
        bidderWord, settledWord, σ2, targetWord, callerWord] using hrdPost
    auctionSettleAuctionTransferFromSuccessToNoPayoutEvent
      (target := targetWord) (noun := nounWord) (amount := amountWord)
      (start := startWord) (finish := finishWord) (bidder := bidderWord)
      (settled := settledWord) (caller := callerWord)
      (by simpa [amountWord, σ1] using hamountZero) hrdPostNoPayout
  have hret :
      RDret auctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA', auctionSettleAuctionExitMap σ' I) ByteArray.empty :=
    auctionSettleAuctionEventToReturn _hperm hrdEvent
  have hcreated :
      cA' = (auctionSettleAuctionExitState evmTf).createdAccounts := by
    simp [auctionSettleAuctionExitState, evmTf, storageStore_createdAccounts]
  have htfOwner : evmTf.executionEnv.codeOwner = I.codeOwner := by
    simp [evmTf, evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hpostAccounts :
      accountMapEquiv (auctionSettleAuctionExitMap σ' I)
        (auctionSettleAuctionExitState evmTf).accountMap := by
    have hstore :=
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hpostTf
    simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
      storageStore_accountMap, htfOwner] using hstore
  exact hret.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode
    hbody hcreated hpostAccounts
    (returnEquiv.fallthrough rfl rfl (by native_decide))

end Auction

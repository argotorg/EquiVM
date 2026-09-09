import Benchmarks.Auction.SettleAuctionTransferBranchPayoutInsufficient

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutSuccessCase {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay : Batteries.RBSet AccountAddress compare}
    {σ' σPay σPaySolm σ'_solm : AccountMap}
    {A'_solm APaySolm : Substate} {o outPay memPay : ByteArray}
    {awPay : UInt256} {kPay CPay : ℕ}
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
    (hamountSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      0 < (auctionSettleAuctionAmount evmEnter).toNat)
    (hpaySolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      let evmTf :=
        { evmMark with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' }
      let evmPay :=
        { evmTf with
          accountMap := σPaySolm
          substate := APaySolm
          createdAccounts := cAPay }
      callViaEVM evmTf (EVM.address (auctionOwnerAddressAt evmTf))
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
        ByteArray.empty (true, evmPay, outPay) true)
    (hpostPay : accountMapEquiv σPay σPaySolm)
    (houtPaySize : outPay.size < UInt256.size)
    (hrdAfterPay :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let amountWord := auctionAuctionAmountWord σ1 I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4828⟩
        [⟨1⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩,
          amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord, ⟨4688⟩,
          ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memPay awPay outPay (cAPay, σPay) kPay CPay) :
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
  let evmPay :=
    { evmTf with
      accountMap := σPaySolm,
      substate := APaySolm,
      createdAccounts := cAPay }
  let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
  let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  by_cases houtZero : outPay.size = 0
  · obtain ⟨_, _, hrdEvent⟩ :=
      auctionSettleAuctionPayoutCallSuccessEmptyReturnToEvent
        houtZero
        (by simpa [amountWord, ownerWord] using hrdAfterPay)
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
      auctionSettleAuctionTransitionReturns_transferFromPayoutLowLevelSuccess
        evmS evmTf evmPay
        (by simpa only [evmS, initState] using hwv) hpausedSolm
        hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
        hamountSolm hpaySolm
    have hcreated :
        cAPay =
          (auctionSettleAuctionExitState evmPay).createdAccounts := by
      simp [auctionSettleAuctionExitState, evmPay, storageStore_createdAccounts]
    have hpayOwner :
        evmPay.executionEnv.codeOwner = I.codeOwner := by
      simp [evmPay, evmTf, evmMark, evmEnter, evmS,
        auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState,
        storageStore_executionEnv]
    have hpostAccounts :
        accountMapEquiv (auctionSettleAuctionExitMap σPay I)
          (auctionSettleAuctionExitState evmPay).accountMap := by
      have hstore :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩
          hpostPay
      simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
        storageStore_accountMap, hpayOwner] using hstore
    exact hret.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode hbody
      hcreated hpostAccounts (returnEquiv.fallthrough rfl rfl (by native_decide))
  · obtain ⟨_, _, _, _, hrdEvent⟩ :=
      auctionSettleAuctionPayoutCallSuccessNonemptyReturnToEvent
        houtPaySize houtZero
        (by simpa [amountWord, ownerWord] using hrdAfterPay)
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
      auctionSettleAuctionTransitionReturns_transferFromPayoutLowLevelSuccess
        evmS evmTf evmPay
        (by simpa only [evmS, initState] using hwv) hpausedSolm
        hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
        hamountSolm hpaySolm
    have hcreated :
        cAPay =
          (auctionSettleAuctionExitState evmPay).createdAccounts := by
      simp [auctionSettleAuctionExitState, evmPay, storageStore_createdAccounts]
    have hpayOwner :
        evmPay.executionEnv.codeOwner = I.codeOwner := by
      simp [evmPay, evmTf, evmMark, evmEnter, evmS,
        auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState,
        storageStore_executionEnv]
    have hpostAccounts :
        accountMapEquiv (auctionSettleAuctionExitMap σPay I)
          (auctionSettleAuctionExitState evmPay).accountMap := by
      have hstore :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩
          hpostPay
      simpa [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
        storageStore_accountMap, hpayOwner] using hstore
    exact hret.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode hbody
      hcreated hpostAccounts (returnEquiv.fallthrough rfl rfl (by native_decide))

end Auction

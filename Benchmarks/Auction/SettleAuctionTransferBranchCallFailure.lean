import Benchmarks.Auction.SettleAuctionTransferBranchPayoutSuccess

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchCallFailureCase {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' σ'_solm : AccountMap}
    {A'_solm : Substate} {o : ByteArray} {k C : ℕ}
    (_hcode : I.code = auctionBytecode)
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
        (false,
          { evmMark with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) true)
    (hosz : o.size < UInt256.size)
    (hrdPost :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let target :=
        UInt256.land
          (auctionSlotWord ⟨201⟩ (auctionSettleAuctionMarkSettledMap σ1 I) I)
          solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4628⟩
        [⟨0⟩, ⟨420⟩, ⟨599290589⟩, target, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
          auctionSelWord I]
        (auctionSettleAuctionTransferFromMem
          (auctionAuctionNounWord σ1 I)
          (auctionAuctionAmountWord σ1 I)
          (auctionAuctionStartWord σ1 I)
          (auctionAuctionEndWord σ1 I)
          (auctionPackedBidderWord (auctionAuctionPackedWord σ1 I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ1 I))
          (UInt256.ofNat I.codeOwner.val))
        (UInt256.ofNat 14) o (cA', σ') k C) :
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
  have hrdFail :
      RDrev auctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    auctionSettleAuctionTransferFromCallFailure (rd := by simpa using hrdPost) hosz (by simp)
  have hbody :
      ExecTransitionBody auctionConfig auctionContract evmS ∅
        settleAuctionTransition.body .reverted :=
    auctionSettleAuctionTransitionReverts_transferFromCallFailure evmS evmTf
      (by simpa only [evmS, initState] using hwv) hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm
      hnounsCodeSolmEval (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
  exact hrdFail.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction

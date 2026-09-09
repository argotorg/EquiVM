import Benchmarks.Auction.SettleAuctionTransferBranchNoPayout

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchDepthLimitCase {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
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
    (hstatusEntered : auctionSlotWord ⟨101⟩ σ_evm I ≠ ⟨2⟩)
    (hpausedSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩)
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
    (htime :
      ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ_evm I).toNat)
    (hbidderZero :
      auctionPackedBidderWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I) ≠
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
          (auctionSettleAuctionMarkSettledMap
            (auctionSettleAuctionEnterMap σ_evm I) I)
          (UInt256.land
            (auctionSlotWord ⟨201⟩
              (auctionSettleAuctionMarkSettledMap
                (auctionSettleAuctionEnterMap σ_evm I) I) I)
            solcAddrMask) ≠
        ⟨0⟩)
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
    (hdepth : ¬ I.depth.val < 1024) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  have hdepthEq : I.depth = 1024 := by
    apply Fin.ext
    have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
    have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
    omega
  let nounSolm :=
    Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩
  let amountSolm :=
    Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let startSolm :=
    Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨209⟩
  let finishSolm :=
    Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨210⟩
  let packedSolm :=
    Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩
  let bidderSolmWord := auctionPackedBidderWord packedSolm
  let settledSolmWord := auctionPackedSettledEVMReturnWord packedSolm
  let callerSolm := UInt256.ofNat evmEnter.executionEnv.codeOwner.val
  let tfTargetSolm : EVM.Address := EVM.address (AccountAddress.ofNat
    ((UInt256.land
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
      solcAddrMask).toNat))
  let evmTf :=
    { evmMark with
      substate := (evmMark.addAccessedAccount tfTargetSolm).substate }
  have hdepthMark : evmMark.executionEnv.depth = 1024 := by
    simpa [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
      using hdepthEq
  have hbidderClean :
      UInt256.land solcAddrMask bidderSolmWord = bidderSolmWord := by
    dsimp [bidderSolmWord, auctionPackedBidderWord]
    rw [u256_land_comm solcAddrMask (UInt256.land packedSolm solcAddrMask)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical packedSolm)
  have hbidderAddr :
      AccountAddress.ofNat bidderSolmWord.toNat =
        AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidderSolmWord) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    rw [hbidderClean]
  have hencode :
      auctionConfig.externalABI.encode? "transferFrom"
          [.address evmEnter.executionEnv.codeOwner,
            .address (AccountAddress.ofNat bidderSolmWord.toNat),
            .int (Int.ofNat nounSolm.toNat)] =
        some ((auctionSettleAuctionTransferFromMem nounSolm amountSolm
          startSolm finishSolm bidderSolmWord settledSolmWord callerSolm)
          |>.readWithPadding 320 100) := by
    rw [hbidderAddr]
    simpa [callerSolm] using
      auctionSettleAuctionTransferFromEncode_eq nounSolm amountSolm
        startSolm finishSolm bidderSolmWord settledSolmWord
        evmEnter.executionEnv.codeOwner
  have hcallSolm :
      typedCallViaEVM auctionConfig evmMark tfTargetSolm "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat bidderSolmWord.toNat),
          .int (Int.ofNat nounSolm.toNat)]
        (false, evmTf, ByteArray.empty) true := by
    exact callNotMade_depthLimit
      (cfg := auctionConfig) (evm := evmMark) (tgt := tfTargetSolm)
      (name := "transferFrom")
      (args := [.address evmEnter.executionEnv.codeOwner,
        .address (AccountAddress.ofNat bidderSolmWord.toNat),
        .int (Int.ofNat nounSolm.toNat)])
      (calldata := (auctionSettleAuctionTransferFromMem nounSolm amountSolm
        startSolm finishSolm bidderSolmWord settledSolmWord callerSolm)
        |>.readWithPadding 320 100)
      (callPerm := true) hencode hdepthMark
  have hbody :
      ExecTransitionBody auctionConfig auctionContract evmS ∅
        settleAuctionTransition.body .reverted :=
    auctionSettleAuctionTransitionReverts_transferFromCallFailure evmS evmTf
      (by simpa only [evmS, initState] using hwv) hpausedSolm hstatusSolm
      hstartSolm hsettledSolm htimeSolmLe hbidderSolm
      hnounsCodeSolmEval
      (by simpa [evmTf, evmMark, evmEnter, tfTargetSolm, nounSolm,
        amountSolm, startSolm, finishSolm, packedSolm, bidderSolmWord,
        settledSolmWord, callerSolm] using hcallSolm)
  exact (auctionSettleAuctionX_revert_transferFromDepthLimit
      (g := Sat256.ofUInt256 g) _hperm hwv hpausedZero hstatusEntered
      hstart hsettled htime hbidderZero hnounsCode hdepthEq hreach)
    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction

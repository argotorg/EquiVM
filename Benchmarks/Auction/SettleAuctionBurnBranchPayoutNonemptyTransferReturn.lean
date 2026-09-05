import Benchmarks.Auction.SettleAuctionBurnBranchPayoutEmpty

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionPayoutNonemptyTransferAw_cover
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    let memCopy :=
      auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
    let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    freePtr.toNat + 68 ≤ 32 * (auctionSettleAuctionDynTransferAw awCall freePtr).toNat := by
  let memCopy :=
    auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hawCopy := auctionSettleAuctionPayoutNonemptyAwCopy_bounds (o := o) hosmall
  have hptr63 := auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall
  have hawDeposit :=
    auctionSettleAuctionDynDepositAw_bounds_of_mload
      (mem := memCopy) (aw := awCopy) (ptr := newFree)
      (by simpa [memCopy, awCopy, newFree] using hmload)
      hawCopy.1 hawCopy.2 hptr63
  have hawAfterEq :
      auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy =
        auctionSettleAuctionDynDepositAw memCopy awCopy := by
    simpa [auctionSettleAuctionDynDepositAwAfterMload64,
      auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds
        (aw := auctionSettleAuctionDynDepositAw memCopy awCopy) hawDeposit.1
  have hawCallEq : awCall = auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy := by
    simpa [awCall] using
      auctionSettleAuctionDynDepositCallAw_eq_afterMload64_of_mload
        (mem := memCopy) (aw := awCopy) (ptr := newFree)
        (by simpa [memCopy, awCopy, newFree] using hmload) hawCopy.1 hawCopy.2 hptr63
  have hawCall : 3 ≤ awCall.toNat ∧ awCall.toNat * 32 < UInt256.size := by
    rw [hawCallEq, hawAfterEq]
    exact hawDeposit
  have hptr99 : freePtr.toNat + 99 < UInt256.size := by
    rw [hmload]
    exact auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
  have hptr4 : (freePtr + (⟨4⟩ : UInt256)).toNat = freePtr.toNat + 4 := by
    rw [uadd_toNat, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
    rw [show freePtr.toNat + 4 = 4 + freePtr.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hptr36 : (freePtr + (⟨36⟩ : UInt256)).toNat = freePtr.toNat + 36 := by
    rw [uadd_toNat, show ((⟨36⟩ : UInt256).toNat = 36) by decide]
    rw [show freePtr.toNat + 36 = 36 + freePtr.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hselWord :=
    auctionMachineState_M_word_bounds (s := awCall.toNat) (f := freePtr.toNat)
      hawCall.1 hawCall.2
      (by
        rw [hmload]
        exact auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall)
  have hawFreeEq : auctionSettleAuctionDynMload64Aw awCall = awCall :=
    auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := awCall) hawCall.1
  have hselNat :
      (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat =
        MachineState.M awCall.toNat freePtr.toNat 32 := by
    dsimp [auctionSettleAuctionDynTransferSelAw]
    rw [hawFreeEq]
    exact UInt256.toNat_ofNat_of_lt hselWord.2.2.2
  have hselBounds :
      3 ≤ (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat ∧
        (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat * 32 < UInt256.size := by
    constructor
    · rw [hselNat]
      exact hselWord.1
    · rw [hselNat]
      exact hselWord.2.1
  have hargWord :=
    auctionMachineState_M_word_bounds
      (s := (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat)
      (f := freePtr.toNat + 4)
      hselBounds.1 hselBounds.2 (by omega)
  have hargNat :
      (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat =
        MachineState.M (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat
          (freePtr.toNat + 4) 32 := by
    dsimp [auctionSettleAuctionDynTransferArgAw]
    rw [hptr4]
    exact UInt256.toNat_ofNat_of_lt hargWord.2.2.2
  have hargBounds :
      3 ≤ (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat ∧
        (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat * 32 <
          UInt256.size := by
    constructor
    · rw [hargNat]
      exact hargWord.1
    · rw [hargNat]
      exact hargWord.2.1
  have htransferWord :=
    auctionMachineState_M_word_bounds
      (s := (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat)
      (f := freePtr.toNat + 36)
      hargBounds.1 hargBounds.2 (by omega)
  have htransferNat :
      awTransfer.toNat =
        MachineState.M (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat
          (freePtr.toNat + 36) 32 := by
    dsimp [awTransfer, auctionSettleAuctionDynTransferAw]
    rw [hptr36]
    exact UInt256.toNat_ofNat_of_lt htransferWord.2.2.2
  have hcover :=
    auctionMachineState_M_pos_offset_len_le_words_mul
      (s := (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat)
      (f := freePtr.toNat + 36) (l := 32) (by native_decide)
  change freePtr.toNat + 68 ≤ 32 * awTransfer.toNat
  rw [htransferNat]
  omega

theorem auctionSettleAuctionPayoutNonemptyTransferReturnAwAfterCall_eq
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    let memCopy :=
      auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
    let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    UInt256.ofNat
        (MachineState.M
          (MachineState.M
            (auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr).toNat
            freePtr.toNat 68)
          freePtr.toNat 32) =
      UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32) := by
  let memCopy :=
    auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  have hcover :
      freePtr.toNat + 68 ≤ 32 * awTransfer.toNat := by
    simpa [memCopy, awCopy, freePtr, awCall, awTransfer] using
      auctionSettleAuctionPayoutNonemptyTransferAw_cover
        noun amount start finish bidder settled owner hosmall hne
  have htransfer3 : 3 ≤ awTransfer.toNat := by
    have hfreeGe : 96 ≤ freePtr.toNat := by
      have hmload :
          freePtr = auctionSettleAuctionPayoutNonemptyNewFree o := by
        simpa [freePtr, memCopy, awCopy] using
          auctionSettleAuctionPayoutNonemptyMemCopy_mload64
            noun amount start finish bidder settled hosmall hne
      rw [hmload]
      exact auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
    have hle : 96 ≤ 32 * awTransfer.toNat := by omega
    omega
  have hawAfterEq :
      auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr = awTransfer := by
    simpa [auctionSettleAuctionDynTransferAwAfterMload64,
      auctionSettleAuctionDynMload64Aw, awTransfer] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := awTransfer) htransfer3
  have hM68 :
      MachineState.M
          (auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr).toNat
          freePtr.toNat 68 =
        awTransfer.toNat := by
    rw [hawAfterEq]
    exact auctionMachineState_M_inBounds hcover
  change
    UInt256.ofNat
        (MachineState.M
          (MachineState.M
            (auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr).toNat
            freePtr.toNat 68)
          freePtr.toNat 32) =
      UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  rw [hM68]

theorem auctionSettleAuctionBodyBurnPayoutFailureNonemptyTransferReturnCase
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' cAPay cADep cATransfer : Batteries.RBSet AccountAddress compare}
    {σ' σ'_solm σPay σPaySolm σDep σDepSolm σTransfer σTransferSolm : AccountMap}
    {A' A'_solm APay APaySolm ADepSolm ATransferSolm : Substate}
    {o outPay outDep outTransfer : ByteArray}
    {kAfterTransfer CAfterTransfer : ℕ}
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
    (hamountSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      0 < (auctionSettleAuctionAmount evmEnter).toNat)
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
    (houtZero : outPay.size ≠ 0)
    (houtPaySmall : outPay.size < 2 ^ 138)
    (hpostTransfer : accountMapEquiv σTransfer σTransferSolm)
    (hdeposit :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      let evmBurn :=
        { evmMark with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
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
      let awPayRetDyn := auctionSettleAuctionPayoutNonemptyAwCopy outPay
      let freePtrDyn := auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
      let memDeposit := auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
      let evmDeposit :=
        { evmPay with
            accountMap := σDepSolm,
            substate := ADepSolm,
            createdAccounts := cADep }
      typedCallViaEVM auctionConfig evmPay
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "deposit"
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat) []
        (true, evmDeposit, outDep) true)
    (htransferTrue :
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
      let evmDeposit :=
        { evmPay with
            accountMap := σDepSolm,
            substate := ADepSolm,
            createdAccounts := cADep }
      let evmTransfer :=
        { evmDeposit with
            accountMap := σTransferSolm,
            substate := ATransferSolm,
            createdAccounts := cATransfer }
      typedCallViaEVM auctionConfig evmDeposit
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmDeposit
              evmDeposit.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "transfer" 0
        [.address (auctionOwnerAddressAt evmBurn),
          .int (Int.ofNat
            (auctionSettleAuctionAmount evmEnter).toNat)]
        (true, evmTransfer, outTransfer) true)
    (hwethCodeSolmTransfer :
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
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0
          (fun acc => acc.code.size)))).toNat)
    (hrdAfterTransferParam :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
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
      let awPayRetDyn := auctionSettleAuctionPayoutNonemptyAwCopy outPay
      let freePtrDyn := auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
      let memDeposit := auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
      let awCall := auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtrDyn amountWord ownerWord
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtrDyn
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtrDyn.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtrDyn.toNat 32)
      let wethTransferWord := UInt256.land (auctionSlotWord ⟨202⟩ σDep I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3518⟩
        [⟨1⟩, (⟨68⟩ : UInt256) + freePtrDyn, ⟨2835717307⟩,
          wethTransferWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer (cATransfer, σTransfer)
        kAfterTransfer CAfterTransfer)
    (houtTransferSize : outTransfer.size < UInt256.size) :
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
  let evmDeposit :=
    { evmPay with
        accountMap := σDepSolm,
        substate := ADepSolm,
        createdAccounts := cADep }
  let evmTransfer :=
    { evmDeposit with
        accountMap := σTransferSolm,
        substate := ATransferSolm,
        createdAccounts := cATransfer }
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
  let awPayRetDyn := auctionSettleAuctionPayoutNonemptyAwCopy outPay
  let freePtrDyn := auctionSettleAuctionDynMload64 memPayRetDyn awPayRetDyn
  let memDeposit := auctionSettleAuctionDynDepositMem memPayRetDyn awPayRetDyn
  let memTransfer :=
    auctionSettleAuctionDynTransferMem memDeposit freePtrDyn
      amountWord ownerWord
  let wethTransferWord :=
    UInt256.land (auctionSlotWord ⟨202⟩ σDep I) solcAddrMask
  have hdepositLocal :
      typedCallViaEVM auctionConfig evmPay
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "deposit"
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat) []
        (true, evmDeposit, outDep) true := by
    simpa [evmS, evmEnter, evmMark, evmBurn, amountWord, evmBurnE,
      evmPayE, evmPay, memPayRetDyn, awPayRetDyn, freePtrDyn,
      memDeposit, evmDeposit] using hdeposit
  have htransferTrueLocal :
      typedCallViaEVM auctionConfig evmDeposit
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmDeposit
              evmDeposit.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))) "transfer" 0
        [.address (auctionOwnerAddressAt evmBurn),
          .int (Int.ofNat
            (auctionSettleAuctionAmount evmEnter).toNat)]
        (true, evmTransfer, outTransfer) true := by
    simpa [evmS, evmEnter, evmMark, evmBurn, amountWord, ownerWord,
      evmBurnE, evmPayE, evmPay, evmDeposit, evmTransfer] using
      htransferTrue
  have hwethCodeSolmTransferLocal :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0
          (fun acc => acc.code.size)))).toNat := by
    simpa [evmS, evmEnter, evmMark, evmBurn, evmBurnE, evmPayE,
      evmPay] using hwethCodeSolmTransfer
  let transferRetWord :=
    UInt256.ofNat
      (fromByteArrayBigEndian (outTransfer.extract 0 32))
  have hrdAfterTransfer :
      let awCall := auctionSettleAuctionDynDepositCallAw memPayRetDyn awPayRetDyn
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtrDyn
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtrDyn.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtrDyn.toNat 32)
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3518⟩
        [⟨1⟩, (⟨68⟩ : UInt256) + freePtrDyn, ⟨2835717307⟩,
          wethTransferWord, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer (cATransfer, σTransfer)
        kAfterTransfer CAfterTransfer := by
    simpa [amountWord, ownerWord, memPayRetDyn, awPayRetDyn,
      freePtrDyn, memDeposit, memTransfer, wethTransferWord] using
      hrdAfterTransferParam
  by_cases hshortTransfer : outTransfer.size < 32
  · have htransferDec :
        auctionConfig.externalABI.decode? "transfer"
          outTransfer = none :=
      auctionExternalABI_decode_transfer_none_short
        hshortTransfer
    have hrdTransferDecodeRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I) := by
      exact
        auctionSettleAuctionPayoutNonemptyTransferReturnShortRevertDyn
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
          ownerWord wethTransferWord houtPaySmall houtZero
          hshortTransfer houtTransferSize
          hrdAfterTransfer
    have hbody :
        ExecTransitionBody auctionConfig auctionContract
          evmS ∅ settleAuctionTransition.body .reverted :=
      auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
        evmS evmBurn evmPay evmDeposit evmTransfer
        (by simpa [evmS, initState] using hwv)
        hpausedSolm hstatusSolm hstartSolm hsettledSolm
        htimeSolmLe hbidderSolm hnounsCodeSolmEval
        (by
          simpa [evmBurn, evmMark, evmEnter] using
            hcallSolm)
        hamountSolm hpaySolm hwethCodeSolmTransferLocal hdepositLocal
        htransferTrueLocal htransferDec
    exact hrdTransferDecodeRev.reEquivExecutionRevert _hcode
      hdispatch hdecode hbody
  · have houtTransfer32 : 32 ≤ outTransfer.size := by
      omega
    by_cases hhugeTransfer :
        (2 : Nat) ^ 255 ≤ outTransfer.size
    · have htransferDec :
          auctionConfig.externalABI.decode? "transfer"
            outTransfer = none :=
        auctionExternalABI_decode_transfer_none_huge
          hhugeTransfer
      have hrdTransferDecodeRev :
          RDrev auctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀
              (Sat256.ofUInt256 g) A I) := by
        exact
          auctionSettleAuctionPayoutNonemptyTransferReturnHugeRevertDyn
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
            ownerWord wethTransferWord houtPaySmall houtZero
            hhugeTransfer houtTransferSize
            hrdAfterTransfer
      have hbody :
          ExecTransitionBody auctionConfig auctionContract
            evmS ∅ settleAuctionTransition.body .reverted :=
        auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
          evmS evmBurn evmPay evmDeposit evmTransfer
          (by simpa [evmS, initState] using hwv)
          hpausedSolm hstatusSolm hstartSolm hsettledSolm
          htimeSolmLe hbidderSolm hnounsCodeSolmEval
          (by
            simpa [evmBurn, evmMark, evmEnter] using
              hcallSolm)
          hamountSolm hpaySolm hwethCodeSolmTransferLocal hdepositLocal
          htransferTrueLocal htransferDec
      exact hrdTransferDecodeRev.reEquivExecutionRevert
        _hcode hdispatch hdecode hbody
    · have houtTransferHi :
        outTransfer.size < (2 : Nat) ^ 255 :=
        Nat.lt_of_not_ge hhugeTransfer
      have hfinishReturn {transferOk : Bool}
          (htransferDec :
            auctionConfig.externalABI.decode? "transfer"
              outTransfer = some [.bool transferOk])
          (hret :
            RDret auctionBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀
                (Sat256.ofUInt256 g) A I)
              (cATransfer,
                auctionSettleAuctionExitMap σTransfer I)
              ByteArray.empty) := by
        exact
          auctionSettleAuctionTransferSuccessReturnRuntime
            (evm := evmS) (evmBurn := evmBurn)
            (evmPay := evmPay) (evmDeposit := evmDeposit)
            (evmTransfer := evmTransfer)
            (transferOk := transferOk)
            _hcode hdispatch hdecode rfl hret
            (by simpa [evmS, initState] using hwv)
            hpausedSolm hstatusSolm hstartSolm hsettledSolm
            htimeSolmLe hbidderSolm hnounsCodeSolmEval
            (by
              simpa [evmBurn, evmMark, evmEnter] using
                hcallSolm)
            hamountSolm hpaySolm hwethCodeSolmTransferLocal
            hdepositLocal htransferTrueLocal htransferDec
            (by
              simp [auctionSettleAuctionExitState, evmTransfer,
                storageStore_createdAccounts])
            (by
              simp [evmTransfer, evmDeposit, evmPay, evmBurn,
                evmMark, evmEnter, evmS,
                auctionSettleAuctionMarkSettledState,
                auctionSettleAuctionEnterState, initState,
                storageStore_executionEnv])
            (by
              simpa [evmTransfer] using
                hpostTransfer)
      by_cases htransferZero : transferRetWord = ⟨0⟩
      · have htransferDec :
            auctionConfig.externalABI.decode? "transfer"
              outTransfer = some [.bool false] :=
          auctionExternalABI_decode_transfer_false
            houtTransfer32 houtTransferHi htransferZero
        obtain ⟨_, _, _, _, hrdEvent⟩ :=
          auctionSettleAuctionPayoutNonemptyTransferReturnBoolToEventDyn
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
            ownerWord wethTransferWord houtPaySmall houtZero
            houtTransfer32 houtTransferHi houtTransferSize
            (by
              simpa [transferRetWord] using
                (Or.inl htransferZero :
                  transferRetWord = ⟨0⟩ ∨
                    transferRetWord = ⟨1⟩))
            hrdAfterTransfer
        have hret :
            RDret auctionBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀
                (Sat256.ofUInt256 g) A I)
              (cATransfer,
                auctionSettleAuctionExitMap σTransfer I)
              ByteArray.empty :=
          auctionSettleAuctionEventToReturn _hperm hrdEvent
        exact hfinishReturn htransferDec hret
      · by_cases htransferOne : transferRetWord = ⟨1⟩
        · have htransferDec :
              auctionConfig.externalABI.decode? "transfer"
                outTransfer = some [.bool true] :=
            auctionExternalABI_decode_transfer_true
              houtTransfer32 houtTransferHi htransferOne
          obtain ⟨_, _, _, _, hrdEvent⟩ :=
            auctionSettleAuctionPayoutNonemptyTransferReturnBoolToEventDyn
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
              ownerWord wethTransferWord houtPaySmall houtZero
              houtTransfer32 houtTransferHi houtTransferSize
              (by
                simpa [transferRetWord] using
                  (Or.inr htransferOne :
                    transferRetWord = ⟨0⟩ ∨
                      transferRetWord = ⟨1⟩))
              hrdAfterTransfer
          have hret :
              RDret auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀
                  (Sat256.ofUInt256 g) A I)
                (cATransfer,
                  auctionSettleAuctionExitMap σTransfer I)
                ByteArray.empty :=
            auctionSettleAuctionEventToReturn _hperm hrdEvent
          exact hfinishReturn htransferDec hret
        · have htransferDec :
              auctionConfig.externalABI.decode? "transfer"
                outTransfer = none :=
            auctionExternalABI_decode_transfer_none_noncanon
              houtTransfer32 houtTransferHi htransferZero
              htransferOne
          have hrdTransferDecodeRev :
              RDrev auctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀
                  (Sat256.ofUInt256 g) A I) := by
            exact
              auctionSettleAuctionPayoutNonemptyTransferReturnNoncanonRevertDyn
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
                ownerWord wethTransferWord houtPaySmall houtZero
                houtTransfer32 houtTransferHi houtTransferSize
                (by simpa [transferRetWord] using htransferZero)
                (by simpa [transferRetWord] using htransferOne)
                hrdAfterTransfer
          have hbody :
              ExecTransitionBody auctionConfig auctionContract
                evmS ∅ settleAuctionTransition.body
                .reverted :=
            auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
              evmS evmBurn evmPay evmDeposit evmTransfer
              (by simpa [evmS, initState] using hwv)
              hpausedSolm hstatusSolm hstartSolm
              hsettledSolm htimeSolmLe hbidderSolm
              hnounsCodeSolmEval
              (by
                simpa [evmBurn, evmMark, evmEnter] using
                  hcallSolm)
              hamountSolm hpaySolm hwethCodeSolmTransferLocal
              hdepositLocal htransferTrueLocal htransferDec
          exact hrdTransferDecodeRev.reEquivExecutionRevert
            _hcode hdispatch hdecode hbody


end Auction

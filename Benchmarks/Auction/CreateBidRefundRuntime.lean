import Benchmarks.Auction.CreateBidRefundReturn
import Benchmarks.Auction.CreateBidRefundSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidRefundReturnedRuntime
    {cA cA' gh bl σ_evm σ_solm σCall σ₀ A I} {g : UInt256}
    {marker aw : UInt256} {mem rdata : ByteArray} {csRefund : Frame}
    (evm evmRefund : EVM.State)
    (hinit : evm = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
    (henv : evmRefund.executionEnv = I) (hcreated : evmRefund.createdAccounts = cA')
    (haccounts : accountMapEquiv σCall evmRefund.accountMap)
    (hcode : I.code = auctionBytecode) (hperm : I.perm = true)
    (hsel : selIs I (auctionSelBytes 6))
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hsafe : ExecFuncBody auctionConfig
      { contract := auctionContract,
        locals := auctionSafeTransferStore
          (AccountAddress.ofNat (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat)
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩) }
      (auctionCreateBidEnterState evm) safeTransferETHWithFallback.body
      (.returned csRefund evmRefund none))
    (hfinish : auctionLoadWord mem aw ⟨224⟩ =
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
    (hreach : ∃ k C, RD auctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem aw rdata (cA', σCall) k C) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let finish := Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
    (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩
  let evmBidder := auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund)
  let σBidder := auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I
  have henterEnv : (auctionCreateBidEnterState evm).executionEnv = I := by
    rw [auctionCreateBidEnterState, storageStore_executionEnv, hinit]
    rfl
  have hbidEnv : evmBidder.executionEnv = I := by
    simp only [evmBidder, auctionCreateBidBidderState, auctionCreateBidAmountState,
      storageStore_executionEnv, henv]
  have htime' : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat := by
    simpa only [finish, henterEnv] using htime
  have hle : (UInt256.ofNat evmBidder.executionEnv.header.timestamp).toNat ≤ finish.toNat := by
    rw [hbidEnv]
    exact Nat.le_of_lt htime'
  have hbidAccounts := auctionCreateBid_afterRefund_bidderAccounts_state
    haccounts rfl (by rw [henv]) (by rw [henv]) (by rw [henv])
  have hbuffer : auctionSlotWord ⟨203⟩ σBidder I =
      Solm.EVM.storageLoad evmBidder I.codeOwner ⟨203⟩ := by
    have hh := accountMapEquiv_storage_findD hbidAccounts I.codeOwner ⟨203⟩ ⟨0⟩
    simpa only [σBidder, evmBidder, auctionSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hh
  simp only [evmBidder] at hbidEnv hbuffer
  have hdispatch := auctionDispatch_createBid hsel
  have hdecode := auctionDecode_createBid hsz36 hbig
  by_cases hnot : (auctionSlotWord ⟨203⟩ σBidder I).toNat ≤
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat
  · have hbody := auctionCreateBidTransitionReturns_noExtension_refundReturned evm evmRefund I
      hstatus hnoun htime hreserve hmulFit haddFit hbid hbidder hsafe hle
      (by simpa only [finish, hbidEnv, ← hbuffer] using hnot)
    rw [hinit] at hbody
    have hm := auctionCreateBid_noExtension_afterRefund_postAccounts_state
      haccounts rfl (by rw [henv]) (by rw [henv]) (by rw [henv])
    have hret := auctionCreateBidNoExtensionDynamic hfinish hperm htime' hnot hreach
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by
        simp only [auctionCreateBidUnlockedState, auctionCreateBidBidderState,
          auctionCreateBidAmountState, storageStore_createdAccounts]
        exact hcreated.symm)
      hm (returnEquiv.fallthrough rfl rfl (by native_decide))
  · have hext : (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩ σBidder I).toNat := by omega
    by_cases hadd : (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩ σBidder I).toNat < UInt256.size
    · have hbody := auctionCreateBidTransitionReturns_extension_refundReturned evm evmRefund I
        hstatus hnoun htime hreserve hmulFit haddFit hbid hbidder hsafe hle
        (by simpa only [finish, hbidEnv, ← hbuffer] using hext)
        (by simpa only [hbidEnv, ← hbuffer] using hadd)
      rw [hinit] at hbody
      have hm := auctionCreateBid_extension_afterRefund_postAccounts_state
        haccounts rfl (by rw [henv]) (by rw [henv]) (by rw [henv]) (by rw [henv])
      have hret := auctionCreateBidExtensionDynamic hfinish hperm htime' hext hadd hreach
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        (by
          simp only [auctionCreateBidUnlockedState, auctionCreateBidExtendedState,
            auctionCreateBidBidderState, auctionCreateBidAmountState, storageStore_createdAccounts]
          exact hcreated.symm)
        hm (returnEquiv.fallthrough rfl rfl (by native_decide))
    · have hover : UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat +
          (auctionSlotWord ⟨203⟩ σBidder I).toNat := by omega
      have hbody := auctionCreateBidTransitionReverts_extensionOverflow_refundReturned evm evmRefund I
        hstatus hnoun htime hreserve hmulFit haddFit hbid hbidder hsafe hle
        (by simpa only [finish, hbidEnv, ← hbuffer] using hext)
        (by simpa only [hbidEnv, ← hbuffer] using hover)
      rw [hinit] at hbody
      exact (auctionCreateBidOverflowDynamic hfinish hperm htime' hext hover hreach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Auction

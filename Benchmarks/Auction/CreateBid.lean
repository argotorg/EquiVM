import Benchmarks.Auction.CreateBidRefundNotMade
import Benchmarks.Auction.CreateBidWethRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 50000000

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 6))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 6) rfl _hsel
  have hdispatch := auctionDispatch_createBid _hsel
  have hreach := auctionReachCreateBidBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hdecode := auctionDecode_createBid (I := I) hsz36 hbig
      have hbodyReach := auctionCreateBidX_decoded (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
        (sel := auctionSelWord I) hsz36 _hsize hbig hreach
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
        have hbody := auctionCreateBidTransitionReverts_statusEntered evmS I hstatusSolm
        exact (auctionCreateBidX_revert_statusEntered
            (g := Sat256.ofUInt256 g) hstatusEntered hbodyReach)
          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have henteredReach := auctionCreateBidX_toEntered
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (g := Sat256.ofUInt256 g) _hperm hstatusEntered hbodyReach
        have hstatusSolm :
            Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩ := by
          intro hbad
          have hmap : auctionSlotWord ⟨101⟩ σ_solm I = ⟨2⟩ := by
            simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
              using hbad
          exact hstatusEntered (by simpa [hstatusWord] using hmap)
        have hstatusBody := evalExpr_createBid_status_ne_entered_true evmS I hstatusSolm
        have hassignStatus := auctionCreateBidAssignStatusEntered evmS I
        let evmEnterS := auctionCreateBidEnterState evmS
        have henterAccounts :
            accountMapEquiv (auctionCreateBidEnterMap σ_evm I)
              (auctionCreateBidEnterMap σ_solm I) := by
          simpa [auctionCreateBidEnterMap] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ _hAccounts
        have hnounWord :
            auctionAuctionNounWord (auctionCreateBidEnterMap σ_evm I) I =
              auctionAuctionNounWord (auctionCreateBidEnterMap σ_solm I) I :=
          accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨207⟩ ⟨0⟩
        have hfinishWord :
            auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I =
              auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I :=
          accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨210⟩ ⟨0⟩
        have hreserveWord :
            auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_evm I) I =
              auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_solm I) I :=
          accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨204⟩ ⟨0⟩
        have hamountWord :
            auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I =
              auctionAuctionAmountWord (auctionCreateBidEnterMap σ_solm I) I :=
          accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨208⟩ ⟨0⟩
        have hminBidWord :
            auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_evm I) I =
              auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_solm I) I :=
          accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨205⟩ ⟨0⟩
        have hnounSolmWord :
            Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨207⟩ =
              auctionAuctionNounWord (auctionCreateBidEnterMap σ_solm I) I := by
          simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
            auctionCreateBidEnterMap, auctionAuctionNounWord, auctionSlotWord,
            storageStore_executionEnv, storageStore_accountMap, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]
        have hfinishSolmWord :
            Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨210⟩ =
              auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I := by
          simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
            auctionCreateBidEnterMap, auctionAuctionEndWord, auctionSlotWord,
            storageStore_executionEnv, storageStore_accountMap, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]
        have hreserveSolmWord :
            Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨204⟩ =
              auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_solm I) I := by
          simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
            auctionCreateBidEnterMap, auctionSlotWord,
            storageStore_executionEnv, storageStore_accountMap, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]
        have hamountSolmWord :
            Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨208⟩ =
              auctionAuctionAmountWord (auctionCreateBidEnterMap σ_solm I) I := by
          simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
            auctionCreateBidEnterMap, auctionAuctionAmountWord, auctionSlotWord,
            storageStore_executionEnv, storageStore_accountMap, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]
        have hminBidSolmWord :
            Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨205⟩ =
              auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_solm I) I := by
          simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
            auctionCreateBidEnterMap, auctionSlotWord,
            storageStore_executionEnv, storageStore_accountMap, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]
        by_cases hnoun :
            auctionAuctionNounWord (auctionCreateBidEnterMap σ_evm I) I =
              auctionCreateBidArgWord I
        · have hnounSolm :
              Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨207⟩ =
                auctionCreateBidArgWord I := by
            calc
              Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨207⟩ =
                  auctionAuctionNounWord (auctionCreateBidEnterMap σ_solm I) I :=
                hnounSolmWord
              _ = auctionAuctionNounWord (auctionCreateBidEnterMap σ_evm I) I :=
                hnounWord.symm
              _ = auctionCreateBidArgWord I := hnoun
          by_cases htime :
              (UInt256.ofNat I.header.timestamp).toNat <
                (auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I).toNat
          · have hsnapshotReach := auctionCreateBidX_toSnapshotCheck
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
              (g := Sat256.ofUInt256 g) _hperm hstatusEntered hbodyReach
            by_cases hreserve :
                I.weiValue.toNat <
                  (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_evm I) I).toNat
            · have htimeSolm :
                  (UInt256.ofNat evmEnterS.executionEnv.header.timestamp).toNat <
                    (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨210⟩).toNat := by
                calc
                  (UInt256.ofNat evmEnterS.executionEnv.header.timestamp).toNat =
                      (UInt256.ofNat I.header.timestamp).toNat := by
                    simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                      storageStore_executionEnv]
                  _ < (auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I).toNat :=
                    htime
                  _ = (auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I).toNat := by
                    rw [hfinishWord]
                  _ = (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨210⟩).toNat := by
                    rw [← hfinishSolmWord]
              have hreserveSolm :
                  evmEnterS.executionEnv.weiValue.toNat <
                    (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨204⟩).toNat := by
                calc
                  evmEnterS.executionEnv.weiValue.toNat = I.weiValue.toNat := by
                    simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                      storageStore_executionEnv]
                  _ < (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_evm I) I).toNat :=
                    hreserve
                  _ = (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_solm I) I).toNat := by
                    rw [hreserveWord]
                  _ = (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨204⟩).toNat := by
                    rw [← hreserveSolmWord]
              have hbody := auctionCreateBidTransitionReverts_belowReserve evmS I hstatusSolm
                (by simpa [evmEnterS] using hnounSolm)
                (by simpa [evmEnterS] using htimeSolm)
                (by simpa [evmEnterS] using hreserveSolm)
              exact (auctionCreateBidX_revert_belowReserve
                  (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime hreserve
                  hbodyReach)
                |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
            · have hreserveOk :
                  (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_evm I) I).toNat ≤
                    I.weiValue.toNat :=
                Nat.le_of_not_gt hreserve
              have htimeSolm :
                  (UInt256.ofNat evmEnterS.executionEnv.header.timestamp).toNat <
                    (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨210⟩).toNat := by
                calc
                  (UInt256.ofNat evmEnterS.executionEnv.header.timestamp).toNat =
                      (UInt256.ofNat I.header.timestamp).toNat := by
                    simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                      storageStore_executionEnv]
                  _ < (auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I).toNat :=
                    htime
                  _ = (auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I).toNat := by
                    rw [hfinishWord]
                  _ = (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨210⟩).toNat := by
                    rw [← hfinishSolmWord]
              have hreserveSolmOk :
                  (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                    ⟨204⟩).toNat ≤ evmEnterS.executionEnv.weiValue.toNat := by
                calc
                  (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨204⟩).toNat =
                      (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_solm I) I).toNat := by
                    rw [hreserveSolmWord]
                  _ = (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ_evm I) I).toNat := by
                    rw [← hreserveWord]
                  _ ≤ I.weiValue.toNat := hreserveOk
                  _ = evmEnterS.executionEnv.weiValue.toNat := by
                    simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                      storageStore_executionEnv]
              have hreserveBody := evalExpr_createBid_reserve_ge_true evmEnterS I
                hreserveSolmOk
              have hminBidReach := auctionCreateBidX_toMinBidCheck
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime hreserveOk
                hbodyReach
              by_cases hmulOverflow : UInt256.size ≤
                  (auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat *
                    (UInt256.land
                      (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_evm I) I)
                      ⟨255⟩).toNat
              · have hmulOverflowSolm : UInt256.size ≤
                    (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                        ⟨208⟩).toNat *
                      (UInt256.land
                        (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                          ⟨205⟩) ⟨255⟩).toNat := by
                  calc
                    UInt256.size ≤
                        (auctionAuctionAmountWord
                            (auctionCreateBidEnterMap σ_evm I) I).toNat *
                          (UInt256.land
                            (auctionSlotWord ⟨205⟩
                              (auctionCreateBidEnterMap σ_evm I) I) ⟨255⟩).toNat :=
                      hmulOverflow
                    _ = (auctionAuctionAmountWord
                            (auctionCreateBidEnterMap σ_solm I) I).toNat *
                          (UInt256.land
                            (auctionSlotWord ⟨205⟩
                              (auctionCreateBidEnterMap σ_solm I) I) ⟨255⟩).toNat := by
                      rw [hamountWord, hminBidWord]
                    _ = (Solm.EVM.storageLoad evmEnterS
                            evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                          (UInt256.land
                            (Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat := by
                      rw [← hamountSolmWord, ← hminBidSolmWord]
                have hbody := auctionCreateBidTransitionReverts_minBidMulOverflow evmS I
                  hstatusSolm (by simpa [evmEnterS] using hnounSolm)
                  (by simpa [evmEnterS] using htimeSolm)
                  (by simpa [evmEnterS] using hreserveSolmOk)
                  (by simpa [evmEnterS] using hmulOverflowSolm)
                exact (auctionCreateBidX_revert_minBidMulOverflow
                    (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime hreserveOk
                    hmulOverflow hbodyReach)
                  |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
              · have hmulFit :
                    (auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat *
                      (UInt256.land
                        (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_evm I) I)
                        ⟨255⟩).toNat < UInt256.size :=
                  Nat.lt_of_not_ge hmulOverflow
                have hminBidAddReach := auctionCreateBidX_toMinBidAddCheck
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime hreserveOk
                  hmulFit hbodyReach
                have hmulFitSolm :
                    (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                        ⟨208⟩).toNat *
                      (UInt256.land
                        (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                          ⟨205⟩) ⟨255⟩).toNat < UInt256.size := by
                  calc
                    (Solm.EVM.storageLoad evmEnterS
                        evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                      (UInt256.land
                        (Solm.EVM.storageLoad evmEnterS
                          evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat =
                        (auctionAuctionAmountWord
                            (auctionCreateBidEnterMap σ_solm I) I).toNat *
                          (UInt256.land
                            (auctionSlotWord ⟨205⟩
                              (auctionCreateBidEnterMap σ_solm I) I) ⟨255⟩).toNat := by
                      rw [hamountSolmWord, hminBidSolmWord]
                    _ = (auctionAuctionAmountWord
                            (auctionCreateBidEnterMap σ_evm I) I).toNat *
                          (UInt256.land
                            (auctionSlotWord ⟨205⟩
                              (auctionCreateBidEnterMap σ_evm I) I) ⟨255⟩).toNat := by
                      rw [← hamountWord, ← hminBidWord]
                    _ < UInt256.size := hmulFit
                by_cases haddOverflow : UInt256.size ≤
                    (auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat +
                      ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat *
                        (UInt256.land
                          (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_evm I) I)
                          ⟨255⟩).toNat) / 100
                · have haddOverflowSolm : UInt256.size ≤
                      (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                          ⟨208⟩).toNat +
                        ((Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                            ⟨208⟩).toNat *
                          (UInt256.land
                            (Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) / 100 := by
                    calc
                      UInt256.size ≤
                          (auctionAuctionAmountWord
                              (auctionCreateBidEnterMap σ_evm I) I).toNat +
                            ((auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_evm I) I).toNat *
                              (UInt256.land
                                (auctionSlotWord ⟨205⟩
                                  (auctionCreateBidEnterMap σ_evm I) I) ⟨255⟩).toNat) / 100 :=
                        haddOverflow
                      _ = (auctionAuctionAmountWord
                              (auctionCreateBidEnterMap σ_solm I) I).toNat +
                            ((auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_solm I) I).toNat *
                              (UInt256.land
                                (auctionSlotWord ⟨205⟩
                                  (auctionCreateBidEnterMap σ_solm I) I) ⟨255⟩).toNat) / 100 := by
                        rw [hamountWord, hminBidWord]
                      _ = (Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat +
                            ((Solm.EVM.storageLoad evmEnterS
                                evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                              (UInt256.land
                                (Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) /
                              100 := by
                        rw [← hamountSolmWord, ← hminBidSolmWord]
                  have hbody := auctionCreateBidTransitionReverts_minBidAddOverflow evmS I
                    hstatusSolm (by simpa [evmEnterS] using hnounSolm)
                    (by simpa [evmEnterS] using htimeSolm)
                    (by simpa [evmEnterS] using hreserveSolmOk)
                    (by simpa [evmEnterS] using hmulFitSolm)
                    (by simpa [evmEnterS] using haddOverflowSolm)
                  exact (auctionCreateBidX_revert_minBidAddOverflow
                      (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime
                      hreserveOk hmulFit haddOverflow hbodyReach)
                    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                · have haddFit :
                      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat +
                        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat *
                          (UInt256.land
                            (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_evm I) I)
                            ⟨255⟩).toNat) / 100 < UInt256.size :=
                    Nat.lt_of_not_ge haddOverflow
                  have hminBidCompareReach := auctionCreateBidX_toMinBidCompare
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime
                    hreserveOk hmulFit haddFit hbodyReach
                  have haddFitSolm :
                      (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                          ⟨208⟩).toNat +
                        ((Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                            ⟨208⟩).toNat *
                          (UInt256.land
                            (Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) / 100 <
                          UInt256.size := by
                    calc
                      (Solm.EVM.storageLoad evmEnterS
                          evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat +
                        ((Solm.EVM.storageLoad evmEnterS
                            evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                          (UInt256.land
                            (Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) /
                            100 =
                          (auctionAuctionAmountWord
                              (auctionCreateBidEnterMap σ_solm I) I).toNat +
                            ((auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_solm I) I).toNat *
                              (UInt256.land
                                (auctionSlotWord ⟨205⟩
                                  (auctionCreateBidEnterMap σ_solm I) I) ⟨255⟩).toNat) / 100 := by
                        rw [hamountSolmWord, hminBidSolmWord]
                      _ = (auctionAuctionAmountWord
                              (auctionCreateBidEnterMap σ_evm I) I).toNat +
                            ((auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_evm I) I).toNat *
                              (UInt256.land
                                (auctionSlotWord ⟨205⟩
                                  (auctionCreateBidEnterMap σ_evm I) I) ⟨255⟩).toNat) / 100 := by
                        rw [← hamountWord, ← hminBidWord]
                      _ < UInt256.size := haddFit
                  by_cases hbidTooLow :
                      I.weiValue.toNat <
                        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat +
                          ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat *
                            (UInt256.land
                              (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_evm I) I)
                              ⟨255⟩).toNat) / 100
                  · have hbidTooLowSolm :
                        evmEnterS.executionEnv.weiValue.toNat <
                          (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                              ⟨208⟩).toNat +
                            ((Solm.EVM.storageLoad evmEnterS
                                evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                              (UInt256.land
                                (Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) / 100 := by
                      calc
                        evmEnterS.executionEnv.weiValue.toNat = I.weiValue.toNat := by
                          simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                            storageStore_executionEnv]
                        _ < (auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_evm I) I).toNat +
                              ((auctionAuctionAmountWord
                                  (auctionCreateBidEnterMap σ_evm I) I).toNat *
                                (UInt256.land
                                  (auctionSlotWord ⟨205⟩
                                    (auctionCreateBidEnterMap σ_evm I) I) ⟨255⟩).toNat) / 100 :=
                          hbidTooLow
                        _ = (auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_solm I) I).toNat +
                              ((auctionAuctionAmountWord
                                  (auctionCreateBidEnterMap σ_solm I) I).toNat *
                                (UInt256.land
                                  (auctionSlotWord ⟨205⟩
                                    (auctionCreateBidEnterMap σ_solm I) I) ⟨255⟩).toNat) / 100 := by
                          rw [hamountWord, hminBidWord]
                        _ = (Solm.EVM.storageLoad evmEnterS
                                evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat +
                              ((Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                                (UInt256.land
                                  (Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) /
                                100 := by
                          rw [← hamountSolmWord, ← hminBidSolmWord]
                    have hbody := auctionCreateBidTransitionReverts_minBidTooLow evmS I
                      hstatusSolm (by simpa [evmEnterS] using hnounSolm)
                      (by simpa [evmEnterS] using htimeSolm)
                      (by simpa [evmEnterS] using hreserveSolmOk)
                      (by simpa [evmEnterS] using hmulFitSolm)
                      (by simpa [evmEnterS] using haddFitSolm)
                      (by simpa [evmEnterS] using hbidTooLowSolm)
                    exact (auctionCreateBidX_revert_minBidTooLow
                      (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime
                      hreserveOk hmulFit haddFit hbidTooLow hbodyReach)
                    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                  · have hbidOk :
                        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat +
                          ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ_evm I) I).toNat *
                            (UInt256.land
                              (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ_evm I) I)
                              ⟨255⟩).toNat) / 100 ≤ I.weiValue.toNat :=
                      Nat.le_of_not_gt hbidTooLow
                    have hbidOkSolm :
                        (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                            ⟨208⟩).toNat +
                          ((Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                            (UInt256.land
                              (Solm.EVM.storageLoad evmEnterS
                                evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) /
                              100 ≤ evmEnterS.executionEnv.weiValue.toNat := by
                      calc
                        (Solm.EVM.storageLoad evmEnterS
                            evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat +
                          ((Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat *
                            (UInt256.land
                              (Solm.EVM.storageLoad evmEnterS
                                evmEnterS.executionEnv.codeOwner ⟨205⟩) ⟨255⟩).toNat) /
                              100 =
                            (auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_solm I) I).toNat +
                              ((auctionAuctionAmountWord
                                  (auctionCreateBidEnterMap σ_solm I) I).toNat *
                                (UInt256.land
                                  (auctionSlotWord ⟨205⟩
                                    (auctionCreateBidEnterMap σ_solm I) I) ⟨255⟩).toNat) / 100 := by
                          rw [hamountSolmWord, hminBidSolmWord]
                        _ = (auctionAuctionAmountWord
                                (auctionCreateBidEnterMap σ_evm I) I).toNat +
                              ((auctionAuctionAmountWord
                                  (auctionCreateBidEnterMap σ_evm I) I).toNat *
                                (UInt256.land
                                  (auctionSlotWord ⟨205⟩
                                    (auctionCreateBidEnterMap σ_evm I) I) ⟨255⟩).toNat) / 100 := by
                          rw [← hamountWord, ← hminBidWord]
                        _ ≤ I.weiValue.toNat := hbidOk
                        _ = evmEnterS.executionEnv.weiValue.toNat := by
                          simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                            storageStore_executionEnv]
                    have hminBidGuardBody :=
                      evalExpr_createBid_minBidGuard_true evmEnterS I
                        (by simpa [evmEnterS] using hmulFitSolm)
                        (by simpa [evmEnterS] using haddFitSolm)
                        (by simpa [evmEnterS] using hbidOkSolm)
                    have hlastBidderReach := auctionCreateBidX_toLastBidderCheck
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun
                      htime hreserveOk hmulFit haddFit hbidOk hbodyReach
                    by_cases hdone :
                        auctionPackedBidderWord
                            (auctionAuctionPackedWord
                              (auctionCreateBidEnterMap σ_evm I) I) = ⟨0⟩ ∧
                          (auctionSlotWord ⟨203⟩
                              (auctionCreateBidBidderMap
                                (auctionCreateBidAmountMap
                                  (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat ≤
                            (UInt256.sub
                              (auctionAuctionEndWord
                                (auctionCreateBidEnterMap σ_evm I) I)
                              (UInt256.ofNat I.header.timestamp)).toNat
                    · rcases hdone with
                        ⟨hbidderZero, hnotExtended⟩
                      have hpostAccounts :=
                        auctionCreateBid_noExtension_noRefund_postAccounts
                          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := Sat256.ofUInt256 g) _hAccounts
                      have hpackedWord :
                          auctionAuctionPackedWord (auctionCreateBidEnterMap σ_evm I) I =
                            auctionAuctionPackedWord (auctionCreateBidEnterMap σ_solm I) I :=
                        accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨211⟩ ⟨0⟩
                      have hbidderZeroSolm :
                          AccountAddress.ofNat
                              (auctionPackedBidderWord
                                (Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat =
                            AccountAddress.ofNat 0 := by
                        have hbidderZeroSolmWord :
                            auctionPackedBidderWord
                                (Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩ := by
                          calc
                            auctionPackedBidderWord
                                (Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                              auctionPackedBidderWord
                                (auctionAuctionPackedWord
                                  (auctionCreateBidEnterMap σ_solm I) I) := by
                                simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                                  auctionCreateBidEnterMap, auctionAuctionPackedWord,
                                  auctionSlotWord, storageStore_executionEnv,
                                  storageStore_accountMap, Solm.EVM.storageLoad,
                                  State.lookupAccount, Account.lookupStorage]
                            _ = auctionPackedBidderWord
                                (auctionAuctionPackedWord
                                  (auctionCreateBidEnterMap σ_evm I) I) := by
                                rw [← hpackedWord]
                              _ = ⟨0⟩ := hbidderZero
                        rw [hbidderZeroSolmWord]
                        rfl
                      have hbidderAccounts :
                          accountMapEquiv
                            (auctionCreateBidBidderMap
                              (auctionCreateBidAmountMap
                                (auctionCreateBidEnterMap σ_evm I) I) I)
                            (auctionCreateBidBidderState
                              (auctionCreateBidAmountState evmEnterS)).accountMap := by
                        simpa [evmEnterS, evmS] using
                          auctionCreateBid_noExtension_noRefund_bidderAccounts
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                            (g := Sat256.ofUInt256 g) _hAccounts
                      have htimeBufferWord :
                          auctionSlotWord ⟨203⟩
                              (auctionCreateBidBidderMap
                                (auctionCreateBidAmountMap
                                  (auctionCreateBidEnterMap σ_evm I) I) I) I =
                            Solm.EVM.storageLoad
                              (auctionCreateBidBidderState
                                (auctionCreateBidAmountState evmEnterS))
                              (auctionCreateBidBidderState
                                (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                              ⟨203⟩ := by
                        have h :=
                          accountMapEquiv_storage_findD hbidderAccounts I.codeOwner ⟨203⟩ ⟨0⟩
                        simpa [auctionCreateBidBidderState, auctionCreateBidAmountState,
                          evmEnterS, auctionCreateBidEnterState, evmS, initState, auctionSlotWord,
                          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                          storageStore_executionEnv] using h
                      have hfinishEq :
                          auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I =
                            Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨210⟩ := by
                        calc
                          auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I =
                              auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I :=
                            hfinishWord
                          _ = Solm.EVM.storageLoad evmEnterS
                              evmEnterS.executionEnv.codeOwner ⟨210⟩ := by
                            rw [← hfinishSolmWord]
                      have hnotExtendedSolm :
                          (Solm.EVM.storageLoad
                              (auctionCreateBidBidderState
                                (auctionCreateBidAmountState evmEnterS))
                              (auctionCreateBidBidderState
                                (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                              ⟨203⟩).toNat ≤
                            (UInt256.sub
                              (Solm.EVM.storageLoad evmEnterS
                                evmEnterS.executionEnv.codeOwner ⟨210⟩)
                              (UInt256.ofNat
                                (auctionCreateBidBidderState
                                  (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp)).toNat := by
                        calc
                          (Solm.EVM.storageLoad
                              (auctionCreateBidBidderState
                                (auctionCreateBidAmountState evmEnterS))
                              (auctionCreateBidBidderState
                                (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                              ⟨203⟩).toNat =
                            (auctionSlotWord ⟨203⟩
                              (auctionCreateBidBidderMap
                                (auctionCreateBidAmountMap
                                  (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat := by
                              rw [htimeBufferWord]
                          _ ≤ (UInt256.sub
                              (auctionAuctionEndWord
                                (auctionCreateBidEnterMap σ_evm I) I)
                              (UInt256.ofNat I.header.timestamp)).toNat := hnotExtended
                          _ = (UInt256.sub
                                (Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨210⟩)
                                (UInt256.ofNat
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp)).toNat := by
                                rw [hfinishEq]
                                simp [evmEnterS, evmS, auctionCreateBidEnterState,
                                  auctionCreateBidAmountState, auctionCreateBidBidderState,
                                  initState, storageStore_executionEnv]
                      have hbody :=
                        auctionCreateBidTransitionReturns_noExtension_noRefund evmS I
                          hstatusSolm (by simpa [evmEnterS] using hnounSolm)
                          (by simpa [evmEnterS] using htimeSolm)
                          (by simpa [evmEnterS] using hreserveSolmOk)
                          (by simpa [evmEnterS] using hmulFitSolm)
                          (by simpa [evmEnterS] using haddFitSolm)
                          (by simpa [evmEnterS] using hbidOkSolm)
                          hbidderZeroSolm
                          (by simpa [evmEnterS] using hnotExtendedSolm)
                      exact (auctionCreateBidX_success_noExtension_noRefund
                          (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime
                          hreserveOk hmulFit haddFit hbidOk hbidderZero hnotExtended
                          hbodyReach)
                          |>.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode
                            hbody
                            (by simp [auctionCreateBidUnlockedState,
                              auctionCreateBidBidderState, auctionCreateBidAmountState,
                              evmS, auctionCreateBidEnterState, initState,
                              storageStore_createdAccounts])
                          hpostAccounts
                          (returnEquiv.fallthrough rfl rfl (by native_decide))
                    · by_cases hbidderZero :
                          auctionPackedBidderWord
                              (auctionAuctionPackedWord
                                (auctionCreateBidEnterMap σ_evm I) I) = ⟨0⟩
                      · have hextended :
                            (UInt256.sub
                                (auctionAuctionEndWord
                                  (auctionCreateBidEnterMap σ_evm I) I)
                                (UInt256.ofNat I.header.timestamp)).toNat <
                              (auctionSlotWord ⟨203⟩
                                (auctionCreateBidBidderMap
                                  (auctionCreateBidAmountMap
                                    (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat := by
                          apply Nat.lt_of_not_ge
                          intro hnotExtended
                          exact hdone ⟨hbidderZero, hnotExtended⟩
                        by_cases haddExtFit :
                            (UInt256.ofNat I.header.timestamp).toNat +
                              (auctionSlotWord ⟨203⟩
                                (auctionCreateBidBidderMap
                                  (auctionCreateBidAmountMap
                                    (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat <
                              UInt256.size
                        · have hpostAccounts :=
                            auctionCreateBid_extension_noRefund_postAccounts
                              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) _hAccounts
                          have hpackedWord :
                              auctionAuctionPackedWord (auctionCreateBidEnterMap σ_evm I) I =
                                auctionAuctionPackedWord (auctionCreateBidEnterMap σ_solm I) I :=
                            accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨211⟩ ⟨0⟩
                          have hbidderZeroSolm :
                              AccountAddress.ofNat
                                  (auctionPackedBidderWord
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat =
                                AccountAddress.ofNat 0 := by
                            have hbidderZeroSolmWord :
                                auctionPackedBidderWord
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩ := by
                              calc
                                auctionPackedBidderWord
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                  auctionPackedBidderWord
                                    (auctionAuctionPackedWord
                                      (auctionCreateBidEnterMap σ_solm I) I) := by
                                    simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                                      auctionCreateBidEnterMap, auctionAuctionPackedWord,
                                      auctionSlotWord, storageStore_executionEnv,
                                      storageStore_accountMap, Solm.EVM.storageLoad,
                                      State.lookupAccount, Account.lookupStorage]
                                _ = auctionPackedBidderWord
                                    (auctionAuctionPackedWord
                                      (auctionCreateBidEnterMap σ_evm I) I) := by
                                    rw [← hpackedWord]
                                  _ = ⟨0⟩ := hbidderZero
                            rw [hbidderZeroSolmWord]
                            rfl
                          have hbidderAccounts :
                              accountMapEquiv
                                (auctionCreateBidBidderMap
                                  (auctionCreateBidAmountMap
                                    (auctionCreateBidEnterMap σ_evm I) I) I)
                                (auctionCreateBidBidderState
                                  (auctionCreateBidAmountState evmEnterS)).accountMap := by
                            simpa [evmEnterS, evmS] using
                              auctionCreateBid_noExtension_noRefund_bidderAccounts
                                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) _hAccounts
                          have htimeBufferWord :
                              auctionSlotWord ⟨203⟩
                                  (auctionCreateBidBidderMap
                                    (auctionCreateBidAmountMap
                                      (auctionCreateBidEnterMap σ_evm I) I) I) I =
                                Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩ := by
                            have h :=
                              accountMapEquiv_storage_findD hbidderAccounts I.codeOwner ⟨203⟩
                                ⟨0⟩
                            simpa [auctionCreateBidBidderState, auctionCreateBidAmountState,
                              evmEnterS, auctionCreateBidEnterState, evmS, initState,
                              auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
                              Account.lookupStorage, storageStore_executionEnv] using h
                          have hfinishEq :
                              auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I =
                                Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨210⟩ := by
                            calc
                              auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I =
                                  auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I :=
                                hfinishWord
                              _ = Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨210⟩ := by
                                rw [← hfinishSolmWord]
                          have hextendedSolm :
                              (UInt256.sub
                                  (Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨210⟩)
                                  (UInt256.ofNat
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp)).toNat <
                                (Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩).toNat := by
                            calc
                              (UInt256.sub
                                  (Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨210⟩)
                                  (UInt256.ofNat
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp)).toNat =
                                (UInt256.sub
                                  (auctionAuctionEndWord
                                    (auctionCreateBidEnterMap σ_evm I) I)
                                  (UInt256.ofNat I.header.timestamp)).toNat := by
                                  rw [hfinishEq]
                                  simp [evmEnterS, evmS, auctionCreateBidEnterState,
                                    auctionCreateBidAmountState, auctionCreateBidBidderState,
                                    initState, storageStore_executionEnv]
                              _ < (auctionSlotWord ⟨203⟩
                                  (auctionCreateBidBidderMap
                                    (auctionCreateBidAmountMap
                                      (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat :=
                                hextended
                              _ = (Solm.EVM.storageLoad
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS))
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                    ⟨203⟩).toNat := by
                                  rw [htimeBufferWord]
                          have haddExtFitSolm :
                              (UInt256.ofNat
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp).toNat +
                                (Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩).toNat <
                                UInt256.size := by
                            calc
                              (UInt256.ofNat
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp).toNat +
                                (Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩).toNat =
                                (UInt256.ofNat I.header.timestamp).toNat +
                                  (auctionSlotWord ⟨203⟩
                                    (auctionCreateBidBidderMap
                                      (auctionCreateBidAmountMap
                                        (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat := by
                                  rw [← htimeBufferWord]
                                  simp [evmEnterS, evmS, auctionCreateBidEnterState,
                                    auctionCreateBidAmountState, auctionCreateBidBidderState,
                                    initState, storageStore_executionEnv]
                              _ < UInt256.size := haddExtFit
                          have hbody :=
                            auctionCreateBidTransitionReturns_extension_noRefund evmS I
                              hstatusSolm (by simpa [evmEnterS] using hnounSolm)
                              (by simpa [evmEnterS] using htimeSolm)
                              (by simpa [evmEnterS] using hreserveSolmOk)
                              (by simpa [evmEnterS] using hmulFitSolm)
                              (by simpa [evmEnterS] using haddFitSolm)
                              (by simpa [evmEnterS] using hbidOkSolm)
                              hbidderZeroSolm
                              (by simpa [evmEnterS] using hextendedSolm)
                              (by simpa [evmEnterS] using haddExtFitSolm)
                          exact (auctionCreateBidX_success_extension_noRefund
                              (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime
                              hreserveOk hmulFit haddFit hbidOk hbidderZero hextended
                              haddExtFit hbodyReach)
                              |>.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode
                                hbody
                                (by simp [auctionCreateBidUnlockedState,
                                  auctionCreateBidExtendedState, auctionCreateBidBidderState,
                                  auctionCreateBidAmountState, evmS, auctionCreateBidEnterState,
                                  initState, storageStore_createdAccounts])
                                hpostAccounts
                                (returnEquiv.fallthrough rfl rfl (by native_decide))
                        · have hover :
                              UInt256.size ≤
                                (UInt256.ofNat I.header.timestamp).toNat +
                                  (auctionSlotWord ⟨203⟩
                                    (auctionCreateBidBidderMap
                                      (auctionCreateBidAmountMap
                                        (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat :=
                            Nat.le_of_not_gt haddExtFit
                          have hpackedWord :
                              auctionAuctionPackedWord (auctionCreateBidEnterMap σ_evm I) I =
                                auctionAuctionPackedWord (auctionCreateBidEnterMap σ_solm I) I :=
                            accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨211⟩ ⟨0⟩
                          have hbidderZeroSolm :
                              AccountAddress.ofNat
                                  (auctionPackedBidderWord
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat =
                                AccountAddress.ofNat 0 := by
                            have hbidderZeroSolmWord :
                                auctionPackedBidderWord
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨211⟩) = ⟨0⟩ := by
                              calc
                                auctionPackedBidderWord
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                  auctionPackedBidderWord
                                    (auctionAuctionPackedWord
                                      (auctionCreateBidEnterMap σ_solm I) I) := by
                                    simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                                      auctionCreateBidEnterMap, auctionAuctionPackedWord,
                                      auctionSlotWord, storageStore_executionEnv,
                                      storageStore_accountMap, Solm.EVM.storageLoad,
                                      State.lookupAccount, Account.lookupStorage]
                                _ = auctionPackedBidderWord
                                    (auctionAuctionPackedWord
                                      (auctionCreateBidEnterMap σ_evm I) I) := by
                                    rw [← hpackedWord]
                                  _ = ⟨0⟩ := hbidderZero
                            rw [hbidderZeroSolmWord]
                            rfl
                          have hbidderAccounts :
                              accountMapEquiv
                                (auctionCreateBidBidderMap
                                  (auctionCreateBidAmountMap
                                    (auctionCreateBidEnterMap σ_evm I) I) I)
                                (auctionCreateBidBidderState
                                  (auctionCreateBidAmountState evmEnterS)).accountMap := by
                            simpa [evmEnterS, evmS] using
                              auctionCreateBid_noExtension_noRefund_bidderAccounts
                                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) _hAccounts
                          have htimeBufferWord :
                              auctionSlotWord ⟨203⟩
                                  (auctionCreateBidBidderMap
                                    (auctionCreateBidAmountMap
                                      (auctionCreateBidEnterMap σ_evm I) I) I) I =
                                Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩ := by
                            have h :=
                              accountMapEquiv_storage_findD hbidderAccounts I.codeOwner ⟨203⟩
                                ⟨0⟩
                            simpa [auctionCreateBidBidderState, auctionCreateBidAmountState,
                              evmEnterS, auctionCreateBidEnterState, evmS, initState,
                              auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
                              Account.lookupStorage, storageStore_executionEnv] using h
                          have hfinishEq :
                              auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I =
                                Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨210⟩ := by
                            calc
                              auctionAuctionEndWord (auctionCreateBidEnterMap σ_evm I) I =
                                  auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I :=
                                hfinishWord
                              _ = Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨210⟩ := by
                                rw [← hfinishSolmWord]
                          have hextendedSolm :
                              (UInt256.sub
                                  (Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨210⟩)
                                  (UInt256.ofNat
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp)).toNat <
                                (Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩).toNat := by
                            calc
                              (UInt256.sub
                                  (Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨210⟩)
                                  (UInt256.ofNat
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp)).toNat =
                                (UInt256.sub
                                  (auctionAuctionEndWord
                                    (auctionCreateBidEnterMap σ_evm I) I)
                                  (UInt256.ofNat I.header.timestamp)).toNat := by
                                  rw [hfinishEq]
                                  simp [evmEnterS, evmS, auctionCreateBidEnterState,
                                    auctionCreateBidAmountState, auctionCreateBidBidderState,
                                    initState, storageStore_executionEnv]
                              _ < (auctionSlotWord ⟨203⟩
                                  (auctionCreateBidBidderMap
                                    (auctionCreateBidAmountMap
                                      (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat :=
                                hextended
                              _ = (Solm.EVM.storageLoad
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS))
                                    (auctionCreateBidBidderState
                                      (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                    ⟨203⟩).toNat := by
                                  rw [htimeBufferWord]
                          have hoverSolm :
                              UInt256.size ≤
                                (UInt256.ofNat
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp).toNat +
                                (Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩).toNat := by
                            calc
                              UInt256.size ≤
                                  (UInt256.ofNat I.header.timestamp).toNat +
                                    (auctionSlotWord ⟨203⟩
                                      (auctionCreateBidBidderMap
                                        (auctionCreateBidAmountMap
                                          (auctionCreateBidEnterMap σ_evm I) I) I) I).toNat :=
                                hover
                              _ =
                                (UInt256.ofNat
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.header.timestamp).toNat +
                                (Solm.EVM.storageLoad
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS))
                                  (auctionCreateBidBidderState
                                    (auctionCreateBidAmountState evmEnterS)).executionEnv.codeOwner
                                  ⟨203⟩).toNat := by
                                  rw [← htimeBufferWord]
                                  simp [evmEnterS, evmS, auctionCreateBidEnterState,
                                    auctionCreateBidAmountState, auctionCreateBidBidderState,
                                    initState, storageStore_executionEnv]
                          have hbody :=
                            auctionCreateBidTransitionReverts_extensionOverflow_noRefund evmS I
                              hstatusSolm (by simpa [evmEnterS] using hnounSolm)
                              (by simpa [evmEnterS] using htimeSolm)
                              (by simpa [evmEnterS] using hreserveSolmOk)
                              (by simpa [evmEnterS] using hmulFitSolm)
                              (by simpa [evmEnterS] using haddFitSolm)
                              (by simpa [evmEnterS] using hbidOkSolm)
                              hbidderZeroSolm
                              (by simpa [evmEnterS] using hextendedSolm)
                              (by simpa [evmEnterS] using hoverSolm)
                          exact (auctionCreateBidX_revert_extensionOverflow_noRefund
                              (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime
                              hreserveOk hmulFit haddFit hbidOk hbidderZero hextended hover
                              hbodyReach)
                              |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                      · let evmSE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
                        let evmEnterE := auctionCreateBidEnterState evmSE
                        let σEnterEvm := auctionCreateBidEnterMap σ_evm I
                        let nounWord := auctionAuctionNounWord σEnterEvm I
                        let amountWord := auctionAuctionAmountWord σEnterEvm I
                        let startWord := auctionAuctionStartWord σEnterEvm I
                        let finishWord := auctionAuctionEndWord σEnterEvm I
                        let packedWord := auctionAuctionPackedWord σEnterEvm I
                        let ownerWord := auctionPackedBidderWord packedWord
                        let settledWord := auctionPackedSettledEVMReturnWord packedWord
                        have hownerNZ : ownerWord ≠ ⟨0⟩ := by
                          simpa [ownerWord, packedWord, σEnterEvm] using hbidderZero
                        have hrefundEntry :=
                          auctionCreateBidX_toRefundTransferEntry
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            _hperm hstatusEntered hnoun htime hreserveOk hmulFit haddFit
                            hbidOk (by simpa [ownerWord, packedWord, σEnterEvm] using hownerNZ)
                            hbodyReach
                        have hownerClean : UInt256.land ownerWord solcAddrMask = ownerWord := by
                          exact solcAddrMask_clean (by
                            simpa [ownerWord, packedWord, auctionPackedBidderWord] using
                              solcAddrMask_result_canonical packedWord)
                        obtain ⟨_, _, hrdRefundEntry⟩ := hrefundEntry
                        obtain ⟨_, _, hrdRefundCall⟩ :=
                          auctionCreateBidRefundTransferEntryToCall
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                            (σ₀ := σ₀) (A := A) (I := I)
                            (g := Sat256.ofUInt256 g) (owner := ownerWord)
                            (marker := ownerWord) (noun := nounWord) (amount := amountWord)
                            (start := startWord) (finish := finishWord)
                            (bidder := ownerWord) (settled := settledWord)
                            hownerClean
                            (by
                              simpa [σEnterEvm, nounWord, amountWord, startWord, finishWord,
                                packedWord, ownerWord, settledWord] using hrdRefundEntry)
                        have hrefundStackLen :
                            [⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩,
                              amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord,
                              ⟨1715⟩, ownerWord, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
                              auctionSelWord I].length + 1 ≤ 1024 := by
                          change 18 ≤ 1024
                          native_decide
                        have hrefundNotMadeCase :
                            ∀ {aw k C},
                              RD auctionBytecode I (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                ⟨4828⟩
                                [⟨0⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩,
                                  ⟨0⟩, amountWord, ownerWord, ⟨3347⟩, amountWord,
                                  ownerWord, ⟨1715⟩, ownerWord, ⟨128⟩,
                                  auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
                                (auctionCreateBidRefundLoopMem nounWord amountWord startWord
                                  finishWord ownerWord settledWord)
                                aw ByteArray.empty (cA, σEnterEvm) k C →
                              (¬ (EVM.wordOfInt (Int.ofNat
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat) ≤
                                  (evmEnterS.accountMap.find?
                                      evmEnterS.executionEnv.codeOwner |>.elim ⟨0⟩
                                    (·.balance)) ∧
                                evmEnterS.executionEnv.depth ≠ 1024)) →
                              RuntimeCase (cA := cA) (gh := gh) (bl := bl)
                                (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                                (A := A) (I := I) g := by
                          intro aw k C hrdAfterRefundRaw hnotMadeSolm
                          obtain ⟨_, _, hrdRefundFallback⟩ :=
                            auctionCreateBidRefundCallFailureEmptyReturnToFallback
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) (owner := ownerWord)
                              (marker := ownerWord) (amount := amountWord)
                              rfl hrdAfterRefundRaw
                          have hnotMadeEvm : ¬ (amountWord ≤
                              (σEnterEvm.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧
                              I.depth ≠ 1024) := by
                            have hbalance := accountMapEquiv_balance_word henterAccounts I.codeOwner
                            have hamount : EVM.wordOfInt (Int.ofNat
                                (Solm.EVM.storageLoad evmEnterS
                                  evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat) = amountWord := by
                              rw [wordOfInt_ofNat_toNat, hamountSolmWord, ← hamountWord]
                            rw [hamount] at hnotMadeSolm
                            simp only [evmEnterS, auctionCreateBidEnterState,
                              storageStore_accountMap, storageStore_executionEnv,
                              evmS, initState] at hnotMadeSolm
                            change ¬ (amountWord ≤
                              ((auctionCreateBidEnterMap σ_solm I).find? I.codeOwner
                                |>.elim ⟨0⟩ (·.balance)) ∧ I.depth ≠ 1024) at hnotMadeSolm
                            rwa [← hbalance] at hnotMadeSolm
                          have hrdRev : RDrev auctionBytecode (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                            by_cases hwethCode :
                                Reasoning.Theory.uniswapExtCodeSizeWord σEnterEvm
                                  (UInt256.land (auctionSlotWord ⟨202⟩ σEnterEvm I)
                                    solcAddrMask) = ⟨0⟩
                            · exact auctionCreateBidRefundFallbackWethNoCodeRevertAnyMem
                                hwethCode hrdRefundFallback
                            · exact auctionSafeTransferNotMadeWethCodeReverts
                                (by evm_ov) _hperm hnotMadeEvm hwethCode hrdRefundFallback
                          have hpackedWord :
                              packedWord =
                                auctionAuctionPackedWord
                                  (auctionCreateBidEnterMap σ_solm I) I :=
                            accountMapEquiv_storage_findD henterAccounts
                              I.codeOwner ⟨211⟩ ⟨0⟩
                          have hownerSolmWord :
                              auctionPackedBidderWord
                                  (Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                ownerWord := by
                            calc
                              auctionPackedBidderWord
                                  (Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                auctionPackedBidderWord
                                  (auctionAuctionPackedWord
                                    (auctionCreateBidEnterMap σ_solm I) I) := by
                                  simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                                    auctionCreateBidEnterMap, auctionAuctionPackedWord,
                                    auctionSlotWord, storageStore_executionEnv,
                                    storageStore_accountMap, Solm.EVM.storageLoad,
                                    State.lookupAccount, Account.lookupStorage]
                              _ = auctionPackedBidderWord packedWord := by rw [← hpackedWord]
                              _ = ownerWord := rfl
                          have hbidderSolm :
                              AccountAddress.ofNat
                                  (auctionPackedBidderWord
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
                                AccountAddress.ofNat 0 := by
                            apply auctionCreateBidPackedBidderAddress_ne_zero
                            intro hzero
                            exact hownerNZ (by simpa [hownerSolmWord] using hzero)
                          have hbody := auctionCreateBidTransitionReverts_refundNotMade
                            evmS I hstatusSolm (by simpa [evmEnterS] using hnounSolm)
                            (by simpa [evmEnterS] using htimeSolm)
                            (by simpa [evmEnterS] using hreserveSolmOk)
                            (by simpa [evmEnterS] using hmulFitSolm)
                            (by simpa [evmEnterS] using haddFitSolm)
                            (by simpa [evmEnterS] using hbidOkSolm)
                            (by simpa [evmEnterS] using hbidderSolm)
                            (by simpa [evmEnterS] using hnotMadeSolm)
                          exact hrdRev.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                        by_cases hdepth : I.depth.val < 1024
                        · by_cases hrefundBalance :
                              amountWord ≤
                                ((σEnterEvm.find? I.codeOwner).elim ⟨0⟩ (fun acc => acc.balance))
                          · obtain ⟨cARefund, σRefund, zRefund, outRefund, AInRefund,
                                callGasRefund, kRefund, CRefund, hThetaRefundPack,
                                hrdAfterRefundRaw, houtRefundSize⟩ :=
                              RD.callValueMadeEmptyInOut hrdRefundCall (by native_decide) _hperm
                                (by simpa [amountWord, σEnterEvm] using hrefundBalance)
                                hdepth
                                (by
                                  simpa [amountWord, ownerWord] using hrefundStackLen)
                            obtain ⟨gRefund'', ARefund, hThetaRefund⟩ := hThetaRefundPack
                            let evmRefundE :=
                              { evmEnterE with
                                  accountMap := σRefund,
                                  substate := ARefund,
                                  createdAccounts := cARefund }
                            have hrefundEvmRaw :
                                callViaEVM evmEnterE (AccountAddress.ofUInt256 ownerWord)
                                  (Int.ofNat amountWord.toNat) ByteArray.empty
                                  (zRefund, evmRefundE, outRefund) true := by
                              refine callViaEVM.callMade
                                (valueWord := amountWord) (cA' := cARefund)
                                (σ' := σRefund) (g' := gRefund'') (A' := ARefund)
                                (wordOfInt_ofNat_toNat amountWord).symm
                                ⟨callGasRefund, AInRefund, ?_⟩ (by simp [evmRefundE])
                                ?_ ?_
                              · simpa [evmEnterE, evmSE, initState, accountAddress_roundtrip,
                                  _hperm, amountWord, ownerWord, σEnterEvm,
                                  auctionCreateBidEnterState, auctionCreateBidEnterMap,
                                  storageStore_accountMap, storageStore_executionEnv,
                                  storageStore_createdAccounts,
                                  auctionStorageStore_σ₀, auctionStorageStore_genesisBlockHeader,
                                  auctionStorageStore_blocks] using hThetaRefund
                              · simpa [evmEnterE, evmSE, initState, auctionCreateBidEnterState,
                                  auctionCreateBidEnterMap, storageStore_accountMap,
                                  storageStore_executionEnv, amountWord, σEnterEvm]
                                  using hrefundBalance
                              · simp [evmEnterE, evmSE, initState, auctionCreateBidEnterState]
                                intro hbad
                                have hbadVal : I.depth.val = 1024 := by
                                  simpa [evmEnterE, evmSE, initState,
                                    auctionCreateBidEnterState, storageStore_executionEnv]
                                    using congrArg Fin.val hbad
                                omega
                            cases zRefund
                            · have hrefundEvmFalse :
                                  callViaEVM evmEnterE (AccountAddress.ofUInt256 ownerWord)
                                    (Int.ofNat amountWord.toNat) ByteArray.empty
                                    (false, evmRefundE, outRefund) true := by
                                simpa using hrefundEvmRaw
                              have henterEAccounts :
                                  accountMapEquiv evmEnterE.accountMap evmEnterS.accountMap := by
                                simpa [evmEnterE, evmSE, evmEnterS, evmS,
                                  auctionCreateBidEnterState, auctionCreateBidEnterMap,
                                  initState, storageStore_accountMap,
                                  storageStore_executionEnv] using henterAccounts
                              obtain ⟨σRefundSolm, ARefundSolm, hrefundSolmRaw,
                                  hpostRefund⟩ :=
                                auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
                                  (evm_evm := evmEnterE) (evm_solm := evmEnterS)
                                  (tgt := AccountAddress.ofUInt256 ownerWord)
                                  (value := Int.ofNat amountWord.toNat)
                                  (calldata := ByteArray.empty) (out := outRefund)
                                  (cA' := cARefund) (σ' := σRefund) (A' := ARefund)
                                  (A_in := AInRefund) (z := false) (g'' := gRefund'')
                                  (callGas := callGasRefund) (valueWord := amountWord)
                                  (callPerm := true)
                                  (wordOfInt_ofNat_toNat amountWord).symm
                                  (by
                                    simpa [evmEnterE, evmSE, initState,
                                      accountAddress_roundtrip, _hperm, amountWord,
                                      ownerWord, σEnterEvm, auctionCreateBidEnterState,
                                      auctionCreateBidEnterMap, storageStore_accountMap,
                                      storageStore_executionEnv, storageStore_createdAccounts,
                                      auctionStorageStore_σ₀,
                                      auctionStorageStore_genesisBlockHeader,
                                      auctionStorageStore_blocks] using hThetaRefund)
                                  (by
                                    simpa [evmEnterE, evmSE, initState,
                                      auctionCreateBidEnterState, auctionCreateBidEnterMap,
                                      storageStore_accountMap, storageStore_executionEnv,
                                      amountWord, σEnterEvm] using hrefundBalance)
                                  (by
                                    simp [evmEnterE, evmSE, initState,
                                      auctionCreateBidEnterState]
                                    intro hbad
                                    have hbadVal : I.depth.val = 1024 := by
                                      simpa [evmEnterE, evmSE, initState,
                                        auctionCreateBidEnterState,
                                        storageStore_executionEnv]
                                        using congrArg Fin.val hbad
                                    omega)
                                  henterEAccounts
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      auctionStorageStore_σ₀])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      storageStore_createdAccounts])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      auctionStorageStore_genesisBlockHeader])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      auctionStorageStore_blocks])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      storageStore_executionEnv])
                              let evmRefundS :=
                                { evmEnterS with
                                    accountMap := σRefundSolm,
                                    substate := ARefundSolm,
                                    createdAccounts := cARefund }
                              have hpackedWord :
                                  packedWord =
                                    auctionAuctionPackedWord (auctionCreateBidEnterMap σ_solm I) I :=
                                accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨211⟩ ⟨0⟩
                              have hownerSolmWord :
                                  auctionPackedBidderWord
                                      (Solm.EVM.storageLoad evmEnterS
                                        evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                    ownerWord := by
                                calc
                                  auctionPackedBidderWord
                                      (Solm.EVM.storageLoad evmEnterS
                                        evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                    auctionPackedBidderWord
                                      (auctionAuctionPackedWord
                                        (auctionCreateBidEnterMap σ_solm I) I) := by
                                      simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                                        auctionCreateBidEnterMap, auctionAuctionPackedWord,
                                        auctionSlotWord, storageStore_executionEnv,
                                        storageStore_accountMap, Solm.EVM.storageLoad,
                                        State.lookupAccount, Account.lookupStorage]
                                  _ = auctionPackedBidderWord packedWord := by rw [← hpackedWord]
                                  _ = ownerWord := rfl
                              have hbidderSolm :
                                  AccountAddress.ofNat
                                      (auctionPackedBidderWord
                                        (Solm.EVM.storageLoad evmEnterS
                                          evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
                                    AccountAddress.ofNat 0 := by
                                apply auctionCreateBidPackedBidderAddress_ne_zero
                                intro hzero
                                exact hownerNZ (by simpa [hownerSolmWord] using hzero)
                              have hownerTargetEq :
                                  EVM.address (AccountAddress.ofNat
                                      (auctionPackedBidderWord
                                        (Solm.EVM.storageLoad evmEnterS
                                          evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat) =
                                    AccountAddress.ofUInt256 ownerWord := by
                                rw [hownerSolmWord]
                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                apply Fin.ext
                                simp [EVM.address, EVM.uintN]
                                exact Nat.mod_eq_of_lt
                                  (by
                                    simpa [ownerWord, packedWord, auctionPackedBidderWord,
                                      EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
                                      solcAddrMask_result_canonical packedWord)
                              have hamountEq :
                                  Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨208⟩ =
                                    amountWord := by
                                rw [hamountSolmWord, ← hamountWord]
                              have hrefundSolm :
                                  callViaEVM evmEnterS
                                    (EVM.address (AccountAddress.ofNat
                                      (auctionPackedBidderWord
                                        (Solm.EVM.storageLoad evmEnterS
                                          evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat))
                                    (Int.ofNat
                                      (Solm.EVM.storageLoad evmEnterS
                                        evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat)
                                    ByteArray.empty (false, evmRefundS, outRefund) true := by
                                rw [hownerTargetEq, hamountEq]
                                simpa [evmRefundS] using hrefundSolmRaw
                              have hrefundFailureFallbackCase :
                                  ∀ {mem aw k C},
                                    AuctionWethMemory mem aw amountWord ownerWord finishWord →
                                    RD auctionBytecode I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                      ⟨3347⟩
                                      [⟨0⟩, amountWord, ownerWord, ⟨1715⟩, ownerWord, ⟨128⟩,
                                        auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
                                      mem aw outRefund (cARefund, σRefund) k C →
                                    RuntimeCase (cA := cA) (gh := gh) (bl := bl)
                                      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                                      (A := A) (I := I) g := by
                                intro mem aw k C hm hrdRefundFallback
                                let wethRefund :=
                                  UInt256.land (auctionSlotWord ⟨202⟩ σRefund I) solcAddrMask
                                by_cases hwethCode :
                                    Reasoning.Theory.uniswapExtCodeSizeWord σRefund wethRefund =
                                      ⟨0⟩
                                · have hrdRev :=
                                    auctionCreateBidRefundFallbackWethNoCodeRevertAnyMem
                                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                      (σ₀ := σ₀) (A := A) (I := I)
                                      (g := Sat256.ofUInt256 g) (cA' := cARefund)
                                      (σ' := σRefund) (amount := amountWord)
                                      (owner := ownerWord) (marker := ownerWord)
                                      hwethCode hrdRefundFallback
                                  have hwethCodeSolm :
                                      Reasoning.Theory.uniswapExtCodeSizeWord σRefundSolm
                                          (UInt256.land
                                            (Solm.EVM.storageLoad evmRefundS
                                              evmRefundS.executionEnv.codeOwner ⟨202⟩)
                                            solcAddrMask) =
                                        ⟨0⟩ := by
                                    have hslotEq :=
                                      accountMapEquiv_storage_findD hpostRefund I.codeOwner
                                        ⟨202⟩ ⟨0⟩
                                    have hload :
                                        Solm.EVM.storageLoad evmRefundS
                                            evmRefundS.executionEnv.codeOwner ⟨202⟩ =
                                          auctionSlotWord ⟨202⟩ σRefundSolm I := by
                                      simp [evmRefundS, evmEnterS, evmS, initState,
                                        auctionCreateBidEnterState, auctionSlotWord,
                                        storageStore_executionEnv, Solm.EVM.storageLoad,
                                        State.lookupAccount, Account.lookupStorage]
                                    rw [hload]
                                    have hwethEq :
                                        UInt256.land (auctionSlotWord ⟨202⟩ σRefundSolm I)
                                            solcAddrMask =
                                          wethRefund := by
                                      simp [wethRefund, auctionSlotWord, hslotEq]
                                    rw [hwethEq]
                                    rw [← uniswapExtCodeSizeWord_accountMapEquiv hpostRefund]
                                    exact hwethCode
                                  have hwethLookupZero :
                                      (UInt256.ofNat (((evmRefundS.lookupAccount
                                        (AccountAddress.ofNat
                                          ((UInt256.land
                                            (Solm.EVM.storageLoad evmRefundS
                                              evmRefundS.executionEnv.codeOwner ⟨202⟩)
                                            solcAddrMask).toNat))).option 0
                                          (fun acc => acc.code.size)))).toNat = 0 := by
                                    let wethSolm :=
                                      UInt256.land
                                        (Solm.EVM.storageLoad evmRefundS
                                          evmRefundS.executionEnv.codeOwner ⟨202⟩)
                                        solcAddrMask
                                    have hzero :=
                                      auctionUniswapExtCodeSizeWord_zero_lookup_code_zero
                                        (σ := σRefundSolm) (target := wethSolm)
                                        (addr := AccountAddress.ofUInt256 wethSolm) rfl
                                        (by simpa [wethSolm] using hwethCodeSolm)
                                    have haddr :
                                        AccountAddress.ofNat wethSolm.toNat =
                                          AccountAddress.ofUInt256 wethSolm := by
                                      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                    simpa [State.lookupAccount, evmRefundS, wethSolm, haddr]
                                      using hzero
                                  have hbody :=
                                    auctionCreateBidTransitionReverts_refundLowLevelFailureWethNoCode
                                      evmS evmRefundS I hstatusSolm
                                      (by simpa [evmEnterS] using hnounSolm)
                                      (by simpa [evmEnterS] using htimeSolm)
                                      (by simpa [evmEnterS] using hreserveSolmOk)
                                      (by simpa [evmEnterS] using hmulFitSolm)
                                      (by simpa [evmEnterS] using haddFitSolm)
                                      (by simpa [evmEnterS] using hbidOkSolm)
                                      hbidderSolm hrefundSolm hwethLookupZero
                                  exact hrdRev.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                                · have hamountEq' := hamountEq
                                  have hfinishEq' := hfinishSolmWord
                                  dsimp only [evmEnterS] at hamountEq' hfinishEq'
                                  exact auctionCreateBidWethRuntime evmS evmRefundS rfl
                                    (by simp only [evmRefundS, evmEnterS, evmS,
                                      auctionCreateBidEnterState, storageStore_executionEnv]; rfl)
                                    rfl hpostRefund
                                    (by simp only [evmRefundS, evmEnterS, evmS,
                                      auctionCreateBidEnterState, auctionStorageStore_σ₀]; rfl)
                                    (by simp only [evmRefundS, evmEnterS, evmS,
                                      auctionCreateBidEnterState, auctionStorageStore_genesisBlockHeader]; rfl)
                                    (by simp only [evmRefundS, evmEnterS, evmS,
                                      auctionCreateBidEnterState, auctionStorageStore_blocks]; rfl)
                                    hdepth _hcode _hperm _hsel hsz36 hbig hstatusSolm
                                    hnounSolm htimeSolm hreserveSolmOk hmulFitSolm haddFitSolm
                                    hbidOkSolm hbidderSolm
                                    (by
                                      change AccountAddress.ofNat
                                        (auctionPackedBidderWord (Solm.EVM.storageLoad evmEnterS
                                          evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat = _
                                      rw [hownerSolmWord, accountAddress_ofUInt256_eq_ofNat_toNat])
                                    hrefundSolm
                                    (by
                                      simpa only [hamountEq', hfinishEq', ← hfinishWord] using hm)
                                    hwethCode
                                    (by simpa only [hamountEq'] using ⟨k, C, hrdRefundFallback⟩)
                              by_cases houtZeroFailure : outRefund.size = 0
                              · obtain ⟨_, _, hrdRefundFallback⟩ :=
                                  auctionCreateBidRefundCallFailureEmptyReturnToFallback
                                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                    (σ₀ := σ₀) (A := A) (I := I)
                                    (g := Sat256.ofUInt256 g) (owner := ownerWord)
                                    (marker := ownerWord) (amount := amountWord)
                                    houtZeroFailure
                                    (by
                                      simpa [σEnterEvm, nounWord, amountWord, startWord,
                                        finishWord, packedWord, ownerWord, settledWord]
                                        using hrdAfterRefundRaw)
                                exact hrefundFailureFallbackCase
                                  (by
                                    rw [auctionCreateBidRefundLoopMem_eq_payout]
                                    exact auctionCreateBidWethMemory_empty nounWord amountWord startWord
                                      finishWord ownerWord settledWord ownerWord
                                      (by rw [u256_land_comm]; exact hownerClean)) hrdRefundFallback
                              · obtain ⟨_, _, hrdRefundFallback⟩ :=
                                  auctionCreateBidRefundNonemptyToFallbackExact
                                    (auctionCreateBidRefundLoopMem_mload64 nounWord amountWord startWord
                                      finishWord ownerWord settledWord)
                                    houtRefundSize houtZeroFailure
                                    (by simpa only [amountWord, ownerWord] using hrdAfterRefundRaw)
                                have hsize138 : outRefund.size < 2 ^ 138 :=
                                  Theta_returnData_size_lt_2pow138_of_eq (hΘ := hThetaRefund) (hd := by simp)
                                have hm := auctionCreateBidWethMemory_nonempty nounWord amountWord startWord
                                  finishWord ownerWord settledWord ownerWord hsize138 houtZeroFailure
                                  (by rw [u256_land_comm]; exact hownerClean)
                                exact hrefundFailureFallbackCase
                                  (by
                                    rw [auctionRefundReturnedMem_eq_payout nounWord amountWord startWord
                                      finishWord ownerWord settledWord houtRefundSize]
                                    simpa only [auctionRefundReturnedAw,
                                      auctionSettleAuctionPayoutNonemptyAwCopy,
                                      auctionSettleAuctionPayoutNonemptyOszWord,
                                      UInt256.toNat_ofNat_of_lt houtRefundSize] using hm)
                                  hrdRefundFallback
                            · have hrefundEvmTrue :
                                  callViaEVM evmEnterE (AccountAddress.ofUInt256 ownerWord)
                                    (Int.ofNat amountWord.toNat) ByteArray.empty
                                    (true, evmRefundE, outRefund) true := by
                                simpa using hrefundEvmRaw
                              have henterEAccounts :
                                  accountMapEquiv evmEnterE.accountMap evmEnterS.accountMap := by
                                simpa [evmEnterE, evmSE, evmEnterS, evmS,
                                  auctionCreateBidEnterState, auctionCreateBidEnterMap,
                                  initState, storageStore_accountMap,
                                  storageStore_executionEnv] using henterAccounts
                              obtain ⟨σRefundSolm, ARefundSolm, hrefundSolmRaw,
                                  hpostRefund⟩ :=
                                auctionCallViaEVM_callMade_accountMapEquiv_perm
                                  (storage := auctionConfig.storage) (evm_solm := evmEnterS)
                                  hrefundEvmTrue
                                  henterEAccounts
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      auctionStorageStore_σ₀])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      storageStore_createdAccounts])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      auctionStorageStore_genesisBlockHeader])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      auctionStorageStore_blocks])
                                  (by
                                    simp [evmEnterE, evmSE, evmEnterS, evmS,
                                      auctionCreateBidEnterState, initState,
                                      storageStore_executionEnv])
                              let evmRefundS :=
                                { evmEnterS with
                                    accountMap := σRefundSolm,
                                    substate := ARefundSolm,
                                    createdAccounts := evmRefundE.createdAccounts }
                              have hpackedWord :
                                  packedWord =
                                    auctionAuctionPackedWord
                                      (auctionCreateBidEnterMap σ_solm I) I :=
                                accountMapEquiv_storage_findD henterAccounts I.codeOwner ⟨211⟩ ⟨0⟩
                              have hownerSolmWord :
                                  auctionPackedBidderWord
                                      (Solm.EVM.storageLoad evmEnterS
                                        evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                    ownerWord := by
                                calc
                                  auctionPackedBidderWord
                                      (Solm.EVM.storageLoad evmEnterS
                                        evmEnterS.executionEnv.codeOwner ⟨211⟩) =
                                    auctionPackedBidderWord
                                      (auctionAuctionPackedWord
                                        (auctionCreateBidEnterMap σ_solm I) I) := by
                                      simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                                        auctionCreateBidEnterMap, auctionAuctionPackedWord,
                                        auctionSlotWord, storageStore_executionEnv,
                                        storageStore_accountMap, Solm.EVM.storageLoad,
                                        State.lookupAccount, Account.lookupStorage]
                                  _ = auctionPackedBidderWord packedWord := by rw [← hpackedWord]
                                  _ = ownerWord := rfl
                              have hbidderSolm :
                                  AccountAddress.ofNat
                                      (auctionPackedBidderWord
                                        (Solm.EVM.storageLoad evmEnterS
                                          evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
                                    AccountAddress.ofNat 0 := by
                                apply auctionCreateBidPackedBidderAddress_ne_zero
                                intro hzero
                                exact hownerNZ (by simpa [hownerSolmWord] using hzero)
                              have hownerTargetEq :
                                  EVM.address (AccountAddress.ofNat
                                      (auctionPackedBidderWord
                                        (Solm.EVM.storageLoad evmEnterS
                                          evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat) =
                                    AccountAddress.ofUInt256 ownerWord := by
                                rw [hownerSolmWord]
                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                apply Fin.ext
                                simp [EVM.address, EVM.uintN]
                                exact Nat.mod_eq_of_lt
                                  (by
                                    simpa [ownerWord, packedWord, auctionPackedBidderWord,
                                      EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
                                      solcAddrMask_result_canonical packedWord)
                              have hamountEq :
                                  Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨208⟩ =
                                    amountWord := by
                                calc
                                  Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨208⟩ =
                                    auctionAuctionAmountWord
                                      (auctionCreateBidEnterMap σ_solm I) I :=
                                      hamountSolmWord
                                  _ = auctionAuctionAmountWord σEnterEvm I := by
                                      rw [← hamountWord]
                                  _ = amountWord := rfl
                              have hrefundSolm :
                                  callViaEVM evmEnterS
                                    (EVM.address (AccountAddress.ofNat
                                      (auctionPackedBidderWord
                                        (Solm.EVM.storageLoad evmEnterS
                                          evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat))
                                    (Int.ofNat
                                      (Solm.EVM.storageLoad evmEnterS
                                        evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat)
                                    ByteArray.empty (true, evmRefundS, outRefund) true := by
                                rw [hownerTargetEq, hamountEq]
                                simpa [evmRefundS, evmRefundE] using hrefundSolmRaw
                              have hreturned : ∃ mem aw k C,
                                  auctionLoadWord mem aw ⟨224⟩ = finishWord ∧
                                    RD auctionBytecode I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1715⟩
                                      [ownerWord, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
                                      mem aw outRefund (cARefund, σRefund) k C := by
                                by_cases houtZero : outRefund.size = 0
                                · obtain ⟨_, _, hjoin⟩ := auctionCreateBidRefundCallSuccessEmptyReturnToJoin
                                    houtZero (by simpa only [amountWord, ownerWord] using hrdAfterRefundRaw)
                                  exact ⟨_, _, _, _,
                                    auctionCreateBidRefundLoopMem_mload224 nounWord amountWord startWord
                                      finishWord ownerWord settledWord, hjoin⟩
                                · obtain ⟨_, _, hjoin⟩ := auctionCreateBidRefundNonemptyReturnExact
                                    (auctionCreateBidRefundLoopMem_mload64 nounWord amountWord startWord
                                      finishWord ownerWord settledWord) houtRefundSize houtZero
                                    (by simpa only [amountWord, ownerWord] using hrdAfterRefundRaw)
                                  have hsize138 : outRefund.size < 2 ^ 138 :=
                                    Theta_returnData_size_lt_2pow138_of_eq (hΘ := hThetaRefund) (hd := by simp)
                                  have hload := auctionRefundReturnedMem_load224
                                    (auctionCreateBidRefundLoopMem_size nounWord amountWord startWord
                                      finishWord ownerWord settledWord)
                                    (auctionCreateBidRefundLoopMem_read224_word nounWord amountWord startWord
                                      finishWord ownerWord settledWord) houtZero hsize138
                                  exact ⟨_, _, _, _, hload, hjoin⟩
                              obtain ⟨memJoined, awJoined, kJoined, CJoined, hloadJoined, hjoin⟩ := hreturned
                              have hsafe := auctionSafeTransferBodyReturns_lowLevelSuccess evmEnterS evmRefundS
                                (AccountAddress.ofNat (auctionPackedBidderWord
                                  (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨211⟩)).toNat)
                                (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨208⟩) hrefundSolm
                              exact auctionCreateBidRefundReturnedRuntime evmS evmRefundS rfl
                                (by simp only [evmRefundS, evmEnterS, evmS, auctionCreateBidEnterState,
                                  storageStore_executionEnv]; rfl)
                                rfl hpostRefund _hcode _hperm _hsel hsz36 hbig
                                hstatusSolm hnounSolm htimeSolm hreserveSolmOk hmulFitSolm haddFitSolm
                                hbidOkSolm hbidderSolm hsafe
                                (by
                                  change auctionLoadWord memJoined awJoined ⟨224⟩ =
                                    Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨210⟩
                                  rw [hfinishSolmWord, ← hfinishWord]
                                  exact hloadJoined)
                                ⟨kJoined, CJoined, hjoin⟩
                          · obtain ⟨_, _, hrdAfterRefundRaw⟩ :=
                              RD.callValueInsufficientBalanceEmptyInOut hrdRefundCall _hperm
                                (by native_decide)
                                (by simpa [amountWord, σEnterEvm] using hrefundBalance)
                                hdepth
                                (by
                                  simpa [amountWord, ownerWord] using hrefundStackLen)
                            have hamountLoad :
                                Solm.EVM.storageLoad evmEnterS
                                    evmEnterS.executionEnv.codeOwner ⟨208⟩ =
                                  amountWord := by
                              rw [hamountSolmWord, ← hamountWord]
                            have hbalanceEq :
                                ((σEnterEvm.find? I.codeOwner).elim (⟨0⟩ : UInt256)
                                    (fun acc => acc.balance)) =
                                  ((evmEnterS.accountMap.find?
                                      evmEnterS.executionEnv.codeOwner).elim
                                    (⟨0⟩ : UInt256) (fun acc => acc.balance)) := by
                              have hraw := accountMapEquiv_balance_word henterAccounts I.codeOwner
                              simpa [evmEnterS, evmS, initState,
                                σEnterEvm, auctionCreateBidEnterState, auctionCreateBidEnterMap,
                                storageStore_accountMap, storageStore_executionEnv] using hraw
                            have hnotMadeSolm :
                                ¬ (EVM.wordOfInt (Int.ofNat
                                      (Solm.EVM.storageLoad evmEnterS
                                        evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat) ≤
                                    (evmEnterS.accountMap.find?
                                        evmEnterS.executionEnv.codeOwner |>.elim ⟨0⟩
                                      (·.balance)) ∧
                                  evmEnterS.executionEnv.depth ≠ 1024) := by
                              intro hmade
                              have hmadeBalance := hmade.1
                              have hmadeBalance' :
                                  amountWord ≤
                                    (evmEnterS.accountMap.find?
                                        evmEnterS.executionEnv.codeOwner |>.elim ⟨0⟩
                                      (·.balance)) := by
                                rw [hamountLoad] at hmadeBalance
                                rw [wordOfInt_ofNat_toNat amountWord] at hmadeBalance
                                exact hmadeBalance
                              exact hrefundBalance (by
                                rw [hbalanceEq]
                                exact hmadeBalance')
                            exact hrefundNotMadeCase
                              (by
                                simpa [σEnterEvm, nounWord, amountWord, startWord,
                                  finishWord, packedWord, ownerWord, settledWord]
                                  using hrdAfterRefundRaw)
                              hnotMadeSolm
                        · have hdepthEq : I.depth = 1024 := by
                            apply Fin.ext
                            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                            have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
                            omega
                          obtain ⟨_, _, hrdAfterRefundRaw⟩ :=
                            RD.callValueDepthLimitEmptyInOut hrdRefundCall _hperm
                              (by native_decide)
                              hdepthEq
                              (by
                                simpa [amountWord, ownerWord] using hrefundStackLen)
                          have hdepthSolm : evmEnterS.executionEnv.depth = 1024 := by
                            simpa [evmEnterS, evmS, initState, auctionCreateBidEnterState,
                              storageStore_executionEnv] using hdepthEq
                          have hnotMadeSolm :
                              ¬ (EVM.wordOfInt (Int.ofNat
                                    (Solm.EVM.storageLoad evmEnterS
                                      evmEnterS.executionEnv.codeOwner ⟨208⟩).toNat) ≤
                                  (evmEnterS.accountMap.find?
                                      evmEnterS.executionEnv.codeOwner |>.elim ⟨0⟩
                                    (·.balance)) ∧
                                evmEnterS.executionEnv.depth ≠ 1024) := by
                            intro hmade
                            exact hmade.2 hdepthSolm
                          exact hrefundNotMadeCase
                            (by
                              simpa [σEnterEvm, nounWord, amountWord, startWord,
                                finishWord, packedWord, ownerWord, settledWord]
                                using hrdAfterRefundRaw)
                            hnotMadeSolm
          · have htimeSolm :
                ¬ (UInt256.ofNat evmEnterS.executionEnv.header.timestamp).toNat <
                  (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                    ⟨210⟩).toNat := by
              intro hbad
              have hbadSolm :
                  (UInt256.ofNat I.header.timestamp).toNat <
                    (auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I).toNat := by
                calc
                  (UInt256.ofNat I.header.timestamp).toNat =
                      (UInt256.ofNat evmEnterS.executionEnv.header.timestamp).toNat := by
                    simp [evmEnterS, evmS, auctionCreateBidEnterState, initState,
                      storageStore_executionEnv]
                  _ < (Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner
                      ⟨210⟩).toNat := hbad
                  _ = (auctionAuctionEndWord (auctionCreateBidEnterMap σ_solm I) I).toNat := by
                    rw [hfinishSolmWord]
              exact htime (by simpa [hfinishWord] using hbadSolm)
            have hbody := auctionCreateBidTransitionReverts_expired evmS I hstatusSolm
              (by simpa [evmEnterS] using hnounSolm)
              (by simpa [evmEnterS] using htimeSolm)
            exact (auctionCreateBidX_revert_expired
                (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun htime hbodyReach)
              |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
        · have hnounSolm :
              Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨207⟩ ≠
                auctionCreateBidArgWord I := by
            intro hbad
            exact hnoun (by
              calc
                auctionAuctionNounWord (auctionCreateBidEnterMap σ_evm I) I =
                    auctionAuctionNounWord (auctionCreateBidEnterMap σ_solm I) I := hnounWord
                _ = Solm.EVM.storageLoad evmEnterS evmEnterS.executionEnv.codeOwner ⟨207⟩ :=
                    hnounSolmWord.symm
                _ = auctionCreateBidArgWord I := hbad)
          have hbody := auctionCreateBidTransitionReverts_nounMismatch evmS I hstatusSolm
            (by simpa [evmEnterS] using hnounSolm)
          exact (auctionCreateBidX_revert_nounMismatch
              (g := Sat256.ofUInt256 g) _hperm hstatusEntered hnoun hbodyReach)
            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
    · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact (auctionCreateBidX_decodeRevert_huge (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          (sel := auctionSelWord I) _hsize hbigLe hreach)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_createBid_none_huge (I := I) hbigLe)
  · have hshort : I.calldata.size < 36 := by omega
    exact (auctionCreateBidX_decodeRevert_short (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
        (sel := auctionSelWord I) hsz4 _hsize hshort hreach)
      |>.reEquivDecodingFailed _hcode hdispatch
        (auctionDecode_createBid_none_short (I := I) hshort)

end Auction

import Benchmarks.Dss.Flipper.TendRefund

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flipper

theorem flipperTendBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 13))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 13) rfl hsel
    have hdispatch : dispatchMsg contract I.calldata = some tendTransition :=
      flipperDispatchTend hsel
    have hreach := flipperReachTendBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    have hdecode := flipperDecode_tend_ok (I := I) hsz100
    obtain ⟨_, _, hdecoded⟩ := flipperTendX_decoded (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hpacked :
        flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ_evm I =
          flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidPackedSlotOfWord (tendId I)) ⟨0⟩
    have hlotWordEq : bidLotWord (tendId I) σ_evm I = bidLotWord (tendId I) σ_solm I := by
      simpa [bidLotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (bidSlotOfWord (tendId I) ⟨1⟩) ⟨0⟩
    have htabWordEq : bidTabWord (tendId I) σ_evm I = bidTabWord (tendId I) σ_solm I := by
      simpa [bidTabWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (bidSlotOfWord (tendId I) ⟨5⟩) ⟨0⟩
    have hbidWordEq : bidBidWord (tendId I) σ_evm I = bidBidWord (tendId I) σ_solm I := by
      simpa [bidBidWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (bidBaseOfWord (tendId I)) ⟨0⟩
    have hbegWordEq : tendBegWord σ_evm I = tendBegWord σ_solm I := by
      simpa [tendBegWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
    have hguyEq : bidGuyWord (tendId I) σ_evm I = bidGuyWord (tendId I) σ_solm I := by
      simp [bidGuyWord, flipperAddressReturnWord, hpacked]
    have hticEq : bidTicWord (tendId I) σ_evm I = bidTicWord (tendId I) σ_solm I := by
      simp [bidTicWord, flipperUint48Offset20Word, hpacked]
    have hendEq : bidEndWord (tendId I) σ_evm I = bidEndWord (tendId I) σ_solm I := by
      simp [bidEndWord, flipperUint48Offset26Word, hpacked]
    by_cases hguyEvm : bidGuyWord (tendId I) σ_evm I = ⟨0⟩
    · have hguySolm : bidGuyWord (tendId I) σ_solm I = ⟨0⟩ := by
        simpa [← hguyEq] using hguyEvm
      have hbody :
          ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
        simpa [evm0, locals] using
          (flipperTendSourceBodyGuyNotSet (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hguySolm)
      exact (flipperTendX_guyNotSet (g := Sat256.ofUInt256 g) hguyEvm hdecoded)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hguySolm : bidGuyWord (tendId I) σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact hguyEvm (by simpa [hguyEq] using hzero)
      obtain ⟨_, _, rd2760⟩ :=
        flipperTendX_guyOk (g := Sat256.ofUInt256 g) hguyEvm hdecoded
      by_cases hticNeEvm : bidTicWord (tendId I) σ_evm I ≠ ⟨0⟩
      · by_cases hticLeEvm :
            (bidTicWord (tendId I) σ_evm I).toNat ≤
              (UInt256.ofNat I.header.timestamp).toNat
        · have hticNeSolm : bidTicWord (tendId I) σ_solm I ≠ ⟨0⟩ := by
            intro hzero
            exact hticNeEvm (by simpa [hticEq] using hzero)
          have hticLeSolm :
              (bidTicWord (tendId I) σ_solm I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            simpa [← hticEq] using hticLeEvm
          have hbody :
              ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
            simpa [evm0, locals] using
              (flipperTendSourceBodyAlreadyFinishedTic (cA := cA) (gh := gh)
                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) hwv hguySolm hticNeSolm hticLeSolm)
          exact (flipperTendX_alreadyFinishedTic (g := Sat256.ofUInt256 g)
            hticNeEvm hticLeEvm rd2760)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hticGtEvm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidTicWord (tendId I) σ_evm I).toNat := by
            omega
          have hticGtSolm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidTicWord (tendId I) σ_solm I).toNat := by
            simpa [← hticEq] using hticGtEvm
          have hticGuard :
              evalExpr? config { contract := contract, locals := locals } evm0
                (.binary .or
                  (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                  (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
                  .ok (.bool true) := by
            simpa [evm0, locals] using
              evalExpr_tendTicActive_true_left (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) hticGtSolm
          obtain ⟨_, _, rd2918⟩ :=
            flipperTendX_ticGtOk (g := Sat256.ofUInt256 g) hticGtEvm rd2760
          by_cases hendLeEvm :
              (bidEndWord (tendId I) σ_evm I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat
          · have hendLeSolm :
                (bidEndWord (tendId I) σ_solm I).toNat ≤
                  (UInt256.ofNat I.header.timestamp).toNat := by
              simpa [← hendEq] using hendLeEvm
            have hbody :
                ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
              simpa [evm0, locals] using
                (flipperTendSourceBodyAlreadyFinishedEnd (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) hwv hguySolm hticGuard hendLeSolm)
            exact (flipperTendX_alreadyFinishedEnd (g := Sat256.ofUInt256 g)
              (tendHashMem1_size I) (tendHashMem1_read64 I) hendLeEvm rd2918)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hendGtEvm :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (bidEndWord (tendId I) σ_evm I).toNat := by
              omega
            have hendGtSolm :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (bidEndWord (tendId I) σ_solm I).toNat := by
              simpa [← hendEq] using hendGtEvm
            have hendGuard :
                evalExpr? config { contract := contract, locals := locals } evm0
                  (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
                    .ok (.bool true) := by
              simpa [evm0, locals] using
                evalExpr_tendEndGtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hendGtSolm
            obtain ⟨_, _, rd3035⟩ := flipperTendX_endOk (g := Sat256.ofUInt256 g)
              (tendHashMem1_size I) hendGtEvm rd2918
            by_cases hlotEvm : tendLot I = bidLotWord (tendId I) σ_evm I
            · have hlotSolm : tendLot I = bidLotWord (tendId I) σ_solm I := by
                simpa [← hlotWordEq] using hlotEvm
              have hlotGuard :
                  evalExpr? config { contract := contract, locals := locals } evm0
                    (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
                      .ok (.bool true) := by
                simpa [evm0, locals] using
                  evalExpr_tendLotEqBidLot_true (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) hlotSolm
              obtain ⟨_, _, rd3137⟩ := flipperTendX_lotOk (g := Sat256.ofUInt256 g)
                (tendHashMem2_size I) hlotEvm rd3035
              by_cases htabLeEvm :
                  (tendBid I).toNat ≤ (bidTabWord (tendId I) σ_evm I).toNat
              · have htabLeSolm :
                    (tendBid I).toNat ≤ (bidTabWord (tendId I) σ_solm I).toNat := by
                  simpa [← htabWordEq] using htabLeEvm
                have htabGuard :
                    evalExpr? config { contract := contract, locals := locals } evm0
                      (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
                        .ok (.bool true) := by
                  simpa [evm0, locals] using
                    evalExpr_tendBidLeBidTab_true (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) htabLeSolm
                obtain ⟨_, _, rd3239⟩ := flipperTendX_bidLeTabOk (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
                  htabLeEvm rd3137
                by_cases hbidGtEvm :
                    (bidBidWord (tendId I) σ_evm I).toNat < (tendBid I).toNat
                · have hbidGtSolm :
                      (bidBidWord (tendId I) σ_solm I).toNat < (tendBid I).toNat := by
                    simpa [← hbidWordEq] using hbidGtEvm
                  have hbidGuard :
                      evalExpr? config { contract := contract, locals := locals } evm0
                        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
                          .ok (.bool true) := by
                    simpa [evm0, locals] using
                      evalExpr_tendBidGtBidBid_true (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) hbidGtSolm
                  obtain ⟨_, _, rd3330⟩ := flipperTendX_bidHigherOk (g := Sat256.ofUInt256 g)
                    (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                    hbidGtEvm rd3239
                  have hmem3330Size :=
                    twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                        (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                  have hmem3330Read64 :=
                    twoWordHashMem_read64 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                        (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                      (twoWordHashMem_read64 (tendId I) ⟨1⟩
                        (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
                        (twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem2_size I)
                          (tendHashMem2_read64 I)))
                  by_cases hbidOneOverflow :
                      UInt256.size ≤ (tendBid I).toNat * flipperONEWord.toNat
                  · have hbody :
                        ExecTransitionBody config contract evm0 locals tendTransition.body
                          .reverted := by
                      simpa [evm0, locals] using
                        (flipperTendSourceBodyBidOneOverflow (cA := cA) (gh := gh)
                          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGuard
                          hbidGuard hbidOneOverflow)
                    by_cases hbegOverflow :
                        UInt256.size ≤ (tendBegWord σ_evm I).toNat *
                          (bidBidWord (tendId I) σ_evm I).toNat
                    · exact (flipperTendX_begBidOverflow (g := Sat256.ofUInt256 g)
                        hmem3330Size hbegOverflow rd3330)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hbegFit :
                          (tendBegWord σ_evm I).toNat *
                              (bidBidWord (tendId I) σ_evm I).toNat < UInt256.size := by
                        omega
                      exact (flipperTendX_bidOneOverflow (g := Sat256.ofUInt256 g)
                        hmem3330Size hbegFit hbidOneOverflow rd3330)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hbidOneFit :
                        (tendBid I).toNat * flipperONEWord.toNat < UInt256.size := by
                      omega
                    by_cases hbegOverflow :
                        UInt256.size ≤ (tendBegWord σ_evm I).toNat *
                          (bidBidWord (tendId I) σ_evm I).toNat
                    · have hbegOverflowSolm :
                          UInt256.size ≤ (tendBegWord σ_solm I).toNat *
                            (bidBidWord (tendId I) σ_solm I).toNat := by
                        simpa [← hbegWordEq, ← hbidWordEq] using hbegOverflow
                      have hbody :
                          ExecTransitionBody config contract evm0 locals tendTransition.body
                            .reverted := by
                        simpa [evm0, locals] using
                          (flipperTendSourceBodyBegBidOverflow (cA := cA) (gh := gh)
                            (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                            (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGuard
                            hbidGuard hbidOneFit hbegOverflowSolm)
                      exact (flipperTendX_begBidOverflow (g := Sat256.ofUInt256 g)
                        hmem3330Size hbegOverflow rd3330)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hbegFit :
                          (tendBegWord σ_evm I).toNat *
                              (bidBidWord (tendId I) σ_evm I).toNat < UInt256.size := by
                        omega
                      have hbegFitSolm :
                          (tendBegWord σ_solm I).toNat *
                              (bidBidWord (tendId I) σ_solm I).toNat < UInt256.size := by
                        simpa [← hbegWordEq, ← hbidWordEq] using hbegFit
                      obtain ⟨_, _, rd3376⟩ := flipperTendX_checkedMulOk
                        (g := Sat256.ofUInt256 g) hmem3330Size hbegFit hbidOneFit rd3330
                      have hmem3376Size :=
                        twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmem3330Size
                      have hmem3376Read64 :=
                        twoWordHashMem_read64 (tendId I) ⟨1⟩ hmem3330Size hmem3330Read64
                      by_cases hincGe :
                          (tendBegBidWord σ_evm I).toNat ≤ (tendBidOneWord I).toNat
                      · obtain ⟨_, _, _rd3486⟩ :=
                          flipperTendX_increaseOkByGe (g := Sat256.ofUInt256 g)
                            hincGe rd3376
                        by_cases hcallerEvm :
                            solcSourceWord I = bidGuyWord (tendId I) σ_evm I
                        · have hcallerSolm :
                              solcSourceWord I = bidGuyWord (tendId I) σ_solm I := by
                            simpa [← hguyEq] using hcallerEvm
                          have hincGeSolm :
                              (tendBegBidWord σ_solm I).toNat ≤
                                (tendBidOneWord I).toNat := by
                            simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using
                              hincGe
                          have hincSolm :
                              evalExpr? config
                                { contract := contract,
                                  locals := tendLocalsBidOneBegBid σ_solm I }
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                (.binary .or
                                  (.binary .ge (.var "bidOne") (.var "begBid"))
                                  (.binary .eq (.var "bid")
                                    (.storage (bidsF (.var "id") "tab")))) =
                                  .ok (.bool true) := by
                            exact evalExpr_tendIncreaseRequire_true_of_ge
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) hincGeSolm
                          exact flipperTendBodyFrom3486SameCaller
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                            (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                            hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                            hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                            hmem3376Size hmem3376Read64 _rd3486
                        · have hcallerSolm :
                              solcSourceWord I ≠ bidGuyWord (tendId I) σ_solm I := by
                            intro hcallerSolm
                            exact hcallerEvm (by simpa [← hguyEq] using hcallerSolm)
                          have hincGeSolm :
                              (tendBegBidWord σ_solm I).toNat ≤
                                (tendBidOneWord I).toNat := by
                            simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using
                              hincGe
                          have hincSolm :
                              evalExpr? config
                                { contract := contract,
                                  locals := tendLocalsBidOneBegBid σ_solm I }
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                (.binary .or
                                  (.binary .ge (.var "bidOne") (.var "begBid"))
                                  (.binary .eq (.var "bid")
                                    (.storage (bidsF (.var "id") "tab")))) =
                                  .ok (.bool true) := by
                            exact evalExpr_tendIncreaseRequire_true_of_ge
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) hincGeSolm
                          exact flipperTendBodyFrom3486Refund
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                            (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                            hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                            hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                            hmem3376Size hmem3376Read64 _rd3486
                      · have hincLt :
                            (tendBidOneWord I).toNat < (tendBegBidWord σ_evm I).toNat := by
                          omega
                        by_cases htabEq : tendBid I = bidTabWord (tendId I) σ_evm I
                        · obtain ⟨_, _, _rd3486⟩ :=
                            flipperTendX_increaseOkByTab (g := Sat256.ofUInt256 g)
                              hmem3376Size hincLt htabEq rd3376
                          by_cases hcallerEvm :
                              solcSourceWord I = bidGuyWord (tendId I) σ_evm I
                          · have hcallerSolm :
                                solcSourceWord I = bidGuyWord (tendId I) σ_solm I := by
                              simpa [← hguyEq] using hcallerEvm
                            have hincLtSolm :
                                (tendBidOneWord I).toNat <
                                  (tendBegBidWord σ_solm I).toNat := by
                              simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using
                                hincLt
                            have htabSolm : tendBid I = bidTabWord (tendId I) σ_solm I := by
                              simpa [← htabWordEq] using htabEq
                            have hincSolm :
                                evalExpr? config
                                  { contract := contract,
                                    locals := tendLocalsBidOneBegBid σ_solm I }
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  (.binary .or
                                    (.binary .ge (.var "bidOne") (.var "begBid"))
                                    (.binary .eq (.var "bid")
                                      (.storage (bidsF (.var "id") "tab")))) =
                                    .ok (.bool true) := by
                              exact evalExpr_tendIncreaseRequire_true_of_tab
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) hincLtSolm htabSolm
                            have hmem3486Size :=
                              twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmem3376Size
                            have hmem3486Read64 :=
                              twoWordHashMem_read64 (tendId I) ⟨1⟩ hmem3376Size
                                hmem3376Read64
                            exact flipperTendBodyFrom3486SameCaller
                              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                              (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                              hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                              hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                              hmem3486Size hmem3486Read64 _rd3486
                          · have hcallerSolm :
                                solcSourceWord I ≠ bidGuyWord (tendId I) σ_solm I := by
                              intro hcallerSolm
                              exact hcallerEvm (by simpa [← hguyEq] using hcallerSolm)
                            have hincLtSolm :
                                (tendBidOneWord I).toNat <
                                  (tendBegBidWord σ_solm I).toNat := by
                              simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using
                                hincLt
                            have htabSolm : tendBid I = bidTabWord (tendId I) σ_solm I := by
                              simpa [← htabWordEq] using htabEq
                            have hincSolm :
                                evalExpr? config
                                  { contract := contract,
                                    locals := tendLocalsBidOneBegBid σ_solm I }
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  (.binary .or
                                    (.binary .ge (.var "bidOne") (.var "begBid"))
                                    (.binary .eq (.var "bid")
                                      (.storage (bidsF (.var "id") "tab")))) =
                                    .ok (.bool true) := by
                              exact evalExpr_tendIncreaseRequire_true_of_tab
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) hincLtSolm htabSolm
                            have hmem3486Size :=
                              twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmem3376Size
                            have hmem3486Read64 :=
                              twoWordHashMem_read64 (tendId I) ⟨1⟩ hmem3376Size
                                hmem3376Read64
                            exact flipperTendBodyFrom3486Refund
                              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                              (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                              hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                              hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                              hmem3486Size hmem3486Read64 _rd3486
                        · have hincLtSolm :
                              (tendBidOneWord I).toNat <
                                  (tendBegBidWord σ_solm I).toNat := by
                            simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using hincLt
                          have htabNeSolm :
                              tendBid I ≠ bidTabWord (tendId I) σ_solm I := by
                            intro htabSolm
                            exact htabEq (by simpa [htabWordEq] using htabSolm)
                          have hbody :
                              ExecTransitionBody config contract evm0 locals tendTransition.body
                                .reverted := by
                            simpa [evm0, locals] using
                              (flipperTendSourceBodyInsufficientIncrease (cA := cA)
                                (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                (A := A) (I := I) (g := g) hwv hguySolm hticGuard
                                hendGuard hlotGuard htabGuard hbidGuard hbidOneFit
                                hbegFitSolm hincLtSolm htabNeSolm)
                          exact (flipperTendX_insufficientIncrease (g := Sat256.ofUInt256 g)
                            hmem3376Size hmem3376Read64 hincLt htabEq rd3376)
                            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hbidLeEvm :
                      (tendBid I).toNat ≤ (bidBidWord (tendId I) σ_evm I).toNat := by
                    omega
                  have hbidLeSolm :
                      (tendBid I).toNat ≤ (bidBidWord (tendId I) σ_solm I).toNat := by
                    simpa [← hbidWordEq] using hbidLeEvm
                  have hbody :
                      ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
                    simpa [evm0, locals] using
                      (flipperTendSourceBodyBidNotHigher (cA := cA) (gh := gh)
                        (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGuard
                        hbidLeSolm)
                  exact (flipperTendX_bidNotHigher (g := Sat256.ofUInt256 g)
                    (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                    (twoWordHashMem_read64 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
                      (twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem2_size I)
                        (tendHashMem2_read64 I)))
                    hbidLeEvm rd3239)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have htabGtEvm :
                    (bidTabWord (tendId I) σ_evm I).toNat < (tendBid I).toNat := by
                  omega
                have htabGtSolm :
                    (bidTabWord (tendId I) σ_solm I).toNat < (tendBid I).toNat := by
                  simpa [← htabWordEq] using htabGtEvm
                have hbody :
                    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
                  simpa [evm0, locals] using
                    (flipperTendSourceBodyHigherThanTab (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGtSolm)
                exact (flipperTendX_higherThanTab (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
                  (twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem2_size I)
                    (tendHashMem2_read64 I))
                  htabGtEvm rd3137)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hlotSolm : tendLot I ≠ bidLotWord (tendId I) σ_solm I := by
                intro hlot
                exact hlotEvm (by simpa [hlotWordEq] using hlot)
              have hbody :
                  ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
                simpa [evm0, locals] using
                  (flipperTendSourceBodyLotNotMatching (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) hwv hguySolm hticGuard hendGuard hlotSolm)
              exact (flipperTendX_lotNotMatching (g := Sat256.ofUInt256 g)
                (tendHashMem2_size I) (tendHashMem2_read64 I) hlotEvm rd3035)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hticZeroEvm : bidTicWord (tendId I) σ_evm I = ⟨0⟩ := by
          exact Classical.not_not.mp hticNeEvm
        have hticZeroSolm : bidTicWord (tendId I) σ_solm I = ⟨0⟩ := by
          simpa [← hticEq] using hticZeroEvm
        have hticGuard :
            evalExpr? config { contract := contract, locals := locals } evm0
              (.binary .or
                (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
                .ok (.bool true) := by
          simpa [evm0, locals] using
            evalExpr_tendTicActive_true_right (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) hticZeroSolm
        obtain ⟨_, _, rd2918⟩ :=
          flipperTendX_ticZeroOk (g := Sat256.ofUInt256 g) hticZeroEvm rd2760
        by_cases hendLeEvm :
            (bidEndWord (tendId I) σ_evm I).toNat ≤
              (UInt256.ofNat I.header.timestamp).toNat
        · have hendLeSolm :
              (bidEndWord (tendId I) σ_solm I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            simpa [← hendEq] using hendLeEvm
          have hbody :
              ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
            simpa [evm0, locals] using
              (flipperTendSourceBodyAlreadyFinishedEnd (cA := cA) (gh := gh)
                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) hwv hguySolm hticGuard hendLeSolm)
          exact (flipperTendX_alreadyFinishedEnd (g := Sat256.ofUInt256 g)
            (tendHashMem2_size I) (tendHashMem2_read64 I) hendLeEvm rd2918)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hendGtEvm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidEndWord (tendId I) σ_evm I).toNat := by
            omega
          have hendGtSolm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidEndWord (tendId I) σ_solm I).toNat := by
            simpa [← hendEq] using hendGtEvm
          have hendGuard :
              evalExpr? config { contract := contract, locals := locals } evm0
                (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
                  .ok (.bool true) := by
            simpa [evm0, locals] using
              evalExpr_tendEndGtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) hendGtSolm
          obtain ⟨_, _, rd3035⟩ := flipperTendX_endOk (g := Sat256.ofUInt256 g)
            (tendHashMem2_size I) hendGtEvm rd2918
          by_cases hlotEvm : tendLot I = bidLotWord (tendId I) σ_evm I
          · have hlotSolm : tendLot I = bidLotWord (tendId I) σ_solm I := by
              simpa [← hlotWordEq] using hlotEvm
            have hlotGuard :
                evalExpr? config { contract := contract, locals := locals } evm0
                  (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
                    .ok (.bool true) := by
              simpa [evm0, locals] using
                evalExpr_tendLotEqBidLot_true (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hlotSolm
            obtain ⟨_, _, rd3137⟩ := flipperTendX_lotOk (g := Sat256.ofUInt256 g)
              (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
              hlotEvm rd3035
            by_cases htabLeEvm :
                (tendBid I).toNat ≤ (bidTabWord (tendId I) σ_evm I).toNat
            · have htabLeSolm :
                  (tendBid I).toNat ≤ (bidTabWord (tendId I) σ_solm I).toNat := by
                simpa [← htabWordEq] using htabLeEvm
              have htabGuard :
                  evalExpr? config { contract := contract, locals := locals } evm0
                    (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
                      .ok (.bool true) := by
                simpa [evm0, locals] using
                  evalExpr_tendBidLeBidTab_true (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) htabLeSolm
              obtain ⟨_, _, rd3239⟩ := flipperTendX_bidLeTabOk (g := Sat256.ofUInt256 g)
                (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                  (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                htabLeEvm rd3137
              by_cases hbidGtEvm :
                  (bidBidWord (tendId I) σ_evm I).toNat < (tendBid I).toNat
              · have hbidGtSolm :
                    (bidBidWord (tendId I) σ_solm I).toNat < (tendBid I).toNat := by
                  simpa [← hbidWordEq] using hbidGtEvm
                have hbidGuard :
                    evalExpr? config { contract := contract, locals := locals } evm0
                      (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
                        .ok (.bool true) := by
                  simpa [evm0, locals] using
                    evalExpr_tendBidGtBidBid_true (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) hbidGtSolm
                obtain ⟨_, _, rd3330⟩ := flipperTendX_bidHigherOk (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                    (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))))
                  hbidGtEvm rd3239
                have hmem3330Size :=
                  twoWordHashMem_size_96 (tendId I) ⟨1⟩
                    (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                        (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))))
                have hmem3330Read64 :=
                  twoWordHashMem_read64 (tendId I) ⟨1⟩
                    (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                        (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))))
                    (twoWordHashMem_read64 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                        (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                      (twoWordHashMem_read64 (tendId I) ⟨1⟩
                        (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
                        (twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem2_size I)
                          (tendHashMem2_read64 I))))
                by_cases hbidOneOverflow :
                    UInt256.size ≤ (tendBid I).toNat * flipperONEWord.toNat
                · have hbody :
                      ExecTransitionBody config contract evm0 locals tendTransition.body
                        .reverted := by
                    simpa [evm0, locals] using
                      (flipperTendSourceBodyBidOneOverflow (cA := cA) (gh := gh)
                        (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGuard
                        hbidGuard hbidOneOverflow)
                  by_cases hbegOverflow :
                      UInt256.size ≤ (tendBegWord σ_evm I).toNat *
                        (bidBidWord (tendId I) σ_evm I).toNat
                  · exact (flipperTendX_begBidOverflow (g := Sat256.ofUInt256 g)
                      hmem3330Size hbegOverflow rd3330)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hbegFit :
                        (tendBegWord σ_evm I).toNat *
                            (bidBidWord (tendId I) σ_evm I).toNat < UInt256.size := by
                      omega
                    exact (flipperTendX_bidOneOverflow (g := Sat256.ofUInt256 g)
                      hmem3330Size hbegFit hbidOneOverflow rd3330)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hbidOneFit :
                      (tendBid I).toNat * flipperONEWord.toNat < UInt256.size := by
                    omega
                  by_cases hbegOverflow :
                      UInt256.size ≤ (tendBegWord σ_evm I).toNat *
                        (bidBidWord (tendId I) σ_evm I).toNat
                  · have hbegOverflowSolm :
                        UInt256.size ≤ (tendBegWord σ_solm I).toNat *
                          (bidBidWord (tendId I) σ_solm I).toNat := by
                      simpa [← hbegWordEq, ← hbidWordEq] using hbegOverflow
                    have hbody :
                        ExecTransitionBody config contract evm0 locals tendTransition.body
                          .reverted := by
                      simpa [evm0, locals] using
                        (flipperTendSourceBodyBegBidOverflow (cA := cA) (gh := gh)
                          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGuard
                          hbidGuard hbidOneFit hbegOverflowSolm)
                    exact (flipperTendX_begBidOverflow (g := Sat256.ofUInt256 g)
                      hmem3330Size hbegOverflow rd3330)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hbegFit :
                        (tendBegWord σ_evm I).toNat *
                            (bidBidWord (tendId I) σ_evm I).toNat < UInt256.size := by
                      omega
                    have hbegFitSolm :
                        (tendBegWord σ_solm I).toNat *
                            (bidBidWord (tendId I) σ_solm I).toNat < UInt256.size := by
                      simpa [← hbegWordEq, ← hbidWordEq] using hbegFit
                    obtain ⟨_, _, rd3376⟩ := flipperTendX_checkedMulOk
                      (g := Sat256.ofUInt256 g) hmem3330Size hbegFit hbidOneFit rd3330
                    have hmem3376Size :=
                      twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmem3330Size
                    have hmem3376Read64 :=
                      twoWordHashMem_read64 (tendId I) ⟨1⟩ hmem3330Size hmem3330Read64
                    by_cases hincGe :
                        (tendBegBidWord σ_evm I).toNat ≤ (tendBidOneWord I).toNat
                    · obtain ⟨_, _, _rd3486⟩ :=
                        flipperTendX_increaseOkByGe (g := Sat256.ofUInt256 g)
                          hincGe rd3376
                      by_cases hcallerEvm :
                          solcSourceWord I = bidGuyWord (tendId I) σ_evm I
                      · have hcallerSolm :
                            solcSourceWord I = bidGuyWord (tendId I) σ_solm I := by
                          simpa [← hguyEq] using hcallerEvm
                        have hincGeSolm :
                            (tendBegBidWord σ_solm I).toNat ≤
                              (tendBidOneWord I).toNat := by
                          simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using hincGe
                        have hincSolm :
                            evalExpr? config
                              { contract := contract,
                                locals := tendLocalsBidOneBegBid σ_solm I }
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              (.binary .or
                                (.binary .ge (.var "bidOne") (.var "begBid"))
                                (.binary .eq (.var "bid")
                                  (.storage (bidsF (.var "id") "tab")))) =
                                .ok (.bool true) := by
                          exact evalExpr_tendIncreaseRequire_true_of_ge
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I)
                            (g := Sat256.ofUInt256 g) hincGeSolm
                        exact flipperTendBodyFrom3486SameCaller
                          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                          hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                          hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                          hmem3376Size hmem3376Read64 _rd3486
                      · have hcallerSolm :
                            solcSourceWord I ≠ bidGuyWord (tendId I) σ_solm I := by
                          intro hcallerSolm
                          exact hcallerEvm (by simpa [← hguyEq] using hcallerSolm)
                        have hincGeSolm :
                            (tendBegBidWord σ_solm I).toNat ≤
                              (tendBidOneWord I).toNat := by
                          simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using hincGe
                        have hincSolm :
                            evalExpr? config
                              { contract := contract,
                                locals := tendLocalsBidOneBegBid σ_solm I }
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              (.binary .or
                                (.binary .ge (.var "bidOne") (.var "begBid"))
                                (.binary .eq (.var "bid")
                                  (.storage (bidsF (.var "id") "tab")))) =
                                .ok (.bool true) := by
                          exact evalExpr_tendIncreaseRequire_true_of_ge
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I)
                            (g := Sat256.ofUInt256 g) hincGeSolm
                        exact flipperTendBodyFrom3486Refund
                          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                          hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                          hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                          hmem3376Size hmem3376Read64 _rd3486
                    · have hincLt :
                          (tendBidOneWord I).toNat < (tendBegBidWord σ_evm I).toNat := by
                        omega
                      by_cases htabEq : tendBid I = bidTabWord (tendId I) σ_evm I
                      · obtain ⟨_, _, _rd3486⟩ :=
                          flipperTendX_increaseOkByTab (g := Sat256.ofUInt256 g)
                            hmem3376Size hincLt htabEq rd3376
                        by_cases hcallerEvm :
                            solcSourceWord I = bidGuyWord (tendId I) σ_evm I
                        · have hcallerSolm :
                              solcSourceWord I = bidGuyWord (tendId I) σ_solm I := by
                            simpa [← hguyEq] using hcallerEvm
                          have hincLtSolm :
                              (tendBidOneWord I).toNat <
                                (tendBegBidWord σ_solm I).toNat := by
                            simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using
                              hincLt
                          have htabSolm : tendBid I = bidTabWord (tendId I) σ_solm I := by
                            simpa [← htabWordEq] using htabEq
                          have hincSolm :
                              evalExpr? config
                                { contract := contract,
                                  locals := tendLocalsBidOneBegBid σ_solm I }
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                (.binary .or
                                  (.binary .ge (.var "bidOne") (.var "begBid"))
                                  (.binary .eq (.var "bid")
                                    (.storage (bidsF (.var "id") "tab")))) =
                                  .ok (.bool true) := by
                            exact evalExpr_tendIncreaseRequire_true_of_tab
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) hincLtSolm htabSolm
                          have hmem3486Size :=
                            twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmem3376Size
                          have hmem3486Read64 :=
                            twoWordHashMem_read64 (tendId I) ⟨1⟩ hmem3376Size
                              hmem3376Read64
                          exact flipperTendBodyFrom3486SameCaller
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                            (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                            hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                            hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                            hmem3486Size hmem3486Read64 _rd3486
                        · have hcallerSolm :
                              solcSourceWord I ≠ bidGuyWord (tendId I) σ_solm I := by
                            intro hcallerSolm
                            exact hcallerEvm (by simpa [← hguyEq] using hcallerSolm)
                          have hincLtSolm :
                              (tendBidOneWord I).toNat <
                                (tendBegBidWord σ_solm I).toNat := by
                            simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using
                              hincLt
                          have htabSolm : tendBid I = bidTabWord (tendId I) σ_solm I := by
                            simpa [← htabWordEq] using htabEq
                          have hincSolm :
                              evalExpr? config
                                { contract := contract,
                                  locals := tendLocalsBidOneBegBid σ_solm I }
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                (.binary .or
                                  (.binary .ge (.var "bidOne") (.var "begBid"))
                                  (.binary .eq (.var "bid")
                                    (.storage (bidsF (.var "id") "tab")))) =
                                  .ok (.bool true) := by
                            exact evalExpr_tendIncreaseRequire_true_of_tab
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) hincLtSolm htabSolm
                          have hmem3486Size :=
                            twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmem3376Size
                          have hmem3486Read64 :=
                            twoWordHashMem_read64 (tendId I) ⟨1⟩ hmem3376Size
                              hmem3376Read64
                          exact flipperTendBodyFrom3486Refund
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                            (g := g) hcode hdispatch hdecode hperm hwv hAccounts
                            hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard
                            hbidOneFit hbegFitSolm hincSolm hcallerEvm hcallerSolm
                            hmem3486Size hmem3486Read64 _rd3486
                      · have hincLtSolm :
                            (tendBidOneWord I).toNat <
                                (tendBegBidWord σ_solm I).toNat := by
                          simpa [tendBegBidWord, ← hbegWordEq, ← hbidWordEq] using hincLt
                        have htabNeSolm :
                            tendBid I ≠ bidTabWord (tendId I) σ_solm I := by
                          intro htabSolm
                          exact htabEq (by simpa [htabWordEq] using htabSolm)
                        have hbody :
                            ExecTransitionBody config contract evm0 locals tendTransition.body
                              .reverted := by
                          simpa [evm0, locals] using
                            (flipperTendSourceBodyInsufficientIncrease (cA := cA)
                              (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                              (A := A) (I := I) (g := g) hwv hguySolm hticGuard
                              hendGuard hlotGuard htabGuard hbidGuard hbidOneFit
                              hbegFitSolm hincLtSolm htabNeSolm)
                        exact (flipperTendX_insufficientIncrease (g := Sat256.ofUInt256 g)
                          hmem3376Size hmem3376Read64 hincLt htabEq rd3376)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hbidLeEvm :
                    (tendBid I).toNat ≤ (bidBidWord (tendId I) σ_evm I).toNat := by
                  omega
                have hbidLeSolm :
                    (tendBid I).toNat ≤ (bidBidWord (tendId I) σ_solm I).toNat := by
                  simpa [← hbidWordEq] using hbidLeEvm
                have hbody :
                    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
                  simpa [evm0, locals] using
                    (flipperTendSourceBodyBidNotHigher (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGuard
                      hbidLeSolm)
                exact (flipperTendX_bidNotHigher (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                    (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))))
                  (twoWordHashMem_read64 (tendId I) ⟨1⟩
                    (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                    (twoWordHashMem_read64 (tendId I) ⟨1⟩
                      (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
                      (twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem2_size I)
                        (tendHashMem2_read64 I))))
                  hbidLeEvm rd3239)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have htabGtEvm :
                  (bidTabWord (tendId I) σ_evm I).toNat < (tendBid I).toNat := by
                omega
              have htabGtSolm :
                  (bidTabWord (tendId I) σ_solm I).toNat < (tendBid I).toNat := by
                simpa [← htabWordEq] using htabGtEvm
              have hbody :
                  ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
                simpa [evm0, locals] using
                  (flipperTendSourceBodyHigherThanTab (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) hwv hguySolm hticGuard hendGuard hlotGuard htabGtSolm)
              exact (flipperTendX_higherThanTab (g := Sat256.ofUInt256 g)
                (twoWordHashMem_size_96 (tendId I) ⟨1⟩
                  (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I)))
                (twoWordHashMem_read64 (tendId I) ⟨1⟩
                  (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
                  (twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem2_size I)
                    (tendHashMem2_read64 I)))
                htabGtEvm rd3137)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hlotSolm : tendLot I ≠ bidLotWord (tendId I) σ_solm I := by
              intro hlot
              exact hlotEvm (by simpa [hlotWordEq] using hlot)
            have hbody :
                ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
              simpa [evm0, locals] using
                (flipperTendSourceBodyLotNotMatching (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) hwv hguySolm hticGuard hendGuard hlotSolm)
            exact (flipperTendX_lotNotMatching (g := Sat256.ofUInt256 g)
              (twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem2_size I))
              (twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem2_size I)
                (tendHashMem2_read64 I))
              hlotEvm rd3035)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 13) rfl hsel
    have hshort : I.calldata.size < 100 := by omega
    have hdispatch : dispatchMsg contract I.calldata = some tendTransition :=
      flipperDispatchTend hsel
    have hreach := flipperReachTendBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    exact (flipperTendX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_tend_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper

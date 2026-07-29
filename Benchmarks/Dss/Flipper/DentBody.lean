import Benchmarks.Dss.Flipper.DentBodyBranch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

theorem flipperDentBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 4) rfl hsel
    have hdispatch : dispatchMsg contract I.calldata = some dentTransition :=
      flipperDispatchDent hsel
    have hreach := flipperReachDentBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    have hdecode := flipperDecode_dent_ok (I := I) hsz100
    obtain ⟨_, _, hdecoded⟩ := flipperDentX_decoded (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hpacked :
        flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ_evm I =
          flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidPackedSlotOfWord (dentId I)) ⟨0⟩
    have hbidWordEq : bidBidWord (dentId I) σ_evm I = bidBidWord (dentId I) σ_solm I := by
      simpa [bidBidWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (bidBaseOfWord (dentId I)) ⟨0⟩
    have htabWordEq : bidTabWord (dentId I) σ_evm I = bidTabWord (dentId I) σ_solm I := by
      simpa [bidTabWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (bidSlotOfWord (dentId I) ⟨5⟩) ⟨0⟩
    have hlotWordEq : bidLotWord (dentId I) σ_evm I = bidLotWord (dentId I) σ_solm I := by
      simpa [bidLotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) ⟨0⟩
    have hbegWordEq : dentBegWord σ_evm I = dentBegWord σ_solm I := by
      simpa [dentBegWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
    have hguyEq : bidGuyWord (dentId I) σ_evm I = bidGuyWord (dentId I) σ_solm I := by
      simp [bidGuyWord, flipperAddressReturnWord, hpacked]
    have hticEq : bidTicWord (dentId I) σ_evm I = bidTicWord (dentId I) σ_solm I := by
      simp [bidTicWord, flipperUint48Offset20Word, hpacked]
    have hendEq : bidEndWord (dentId I) σ_evm I = bidEndWord (dentId I) σ_solm I := by
      simp [bidEndWord, flipperUint48Offset26Word, hpacked]
    by_cases hguyEvm : bidGuyWord (dentId I) σ_evm I = ⟨0⟩
    · have hguySolm : bidGuyWord (dentId I) σ_solm I = ⟨0⟩ := by
        simpa [← hguyEq] using hguyEvm
      have hbody :
          ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
        simpa [evm0, locals] using
          (flipperDentSourceBodyGuyNotSet (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hguySolm)
      exact (flipperDentX_guyNotSet (g := Sat256.ofUInt256 g) hguyEvm hdecoded)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hguySolm : bidGuyWord (dentId I) σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact hguyEvm (by simpa [hguyEq] using hzero)
      obtain ⟨_, _, rd4033⟩ :=
        flipperDentX_guyOk (g := Sat256.ofUInt256 g) hguyEvm hdecoded
      by_cases hticNeEvm : bidTicWord (dentId I) σ_evm I ≠ ⟨0⟩
      · by_cases hticLeEvm :
            (bidTicWord (dentId I) σ_evm I).toNat ≤
              (UInt256.ofNat I.header.timestamp).toNat
        · have hticNeSolm : bidTicWord (dentId I) σ_solm I ≠ ⟨0⟩ := by
            intro hzero
            exact hticNeEvm (by simpa [hticEq] using hzero)
          have hticLeSolm :
              (bidTicWord (dentId I) σ_solm I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            simpa [← hticEq] using hticLeEvm
          have hbody :
              ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
            simpa [evm0, locals] using
              (flipperDentSourceBodyAlreadyFinishedTic (cA := cA) (gh := gh)
                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) hwv hguySolm hticNeSolm hticLeSolm)
          exact (flipperDentX_alreadyFinishedTic (g := Sat256.ofUInt256 g)
            hticNeEvm hticLeEvm rd4033)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hticGtEvm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidTicWord (dentId I) σ_evm I).toNat := by
            omega
          have hticGtSolm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidTicWord (dentId I) σ_solm I).toNat := by
            simpa [← hticEq] using hticGtEvm
          have hticGuard :
              evalExpr? config { contract := contract, locals := locals } evm0
                (.binary .or
                  (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                  (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
                  .ok (.bool true) := by
            simpa [evm0, locals] using
              evalExpr_dentTicActive_true_left (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) hticGtSolm
          obtain ⟨_, _, rd4191⟩ :=
            flipperDentX_ticGtOk (g := Sat256.ofUInt256 g) hticGtEvm rd4033
          by_cases hendLeEvm :
              (bidEndWord (dentId I) σ_evm I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat
          · have hendLeSolm :
                (bidEndWord (dentId I) σ_solm I).toNat ≤
                  (UInt256.ofNat I.header.timestamp).toNat := by
              simpa [← hendEq] using hendLeEvm
            have hbody :
                ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
              simpa [evm0, locals] using
                (flipperDentSourceBodyAlreadyFinishedEnd (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) hwv hguySolm hticGuard hendLeSolm)
            exact (flipperDentX_alreadyFinishedEnd (g := Sat256.ofUInt256 g)
              (dentHashMem1_size I) (dentHashMem1_read64 I) hendLeEvm rd4191)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hendGtEvm :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (bidEndWord (dentId I) σ_evm I).toNat := by
              omega
            have hendGtSolm :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (bidEndWord (dentId I) σ_solm I).toNat := by
              simpa [← hendEq] using hendGtEvm
            have hendGuard :
                evalExpr? config { contract := contract, locals := locals } evm0
                  (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
                    .ok (.bool true) := by
              simpa [evm0, locals] using
                evalExpr_dentEndGtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hendGtSolm
            obtain ⟨_, _, rd4308⟩ := flipperDentX_endOk (g := Sat256.ofUInt256 g)
              (dentHashMem1_size I) hendGtEvm rd4191
            by_cases hbidEvm : dentBid I = bidBidWord (dentId I) σ_evm I
            · have hbidSolm : dentBid I = bidBidWord (dentId I) σ_solm I := by
                simpa [← hbidWordEq] using hbidEvm
              have hbidGuard :
                  evalExpr? config { contract := contract, locals := locals } evm0
                    (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
                      .ok (.bool true) := by
                simpa [evm0, locals] using
                  evalExpr_dentBidEqBidBid_true (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) hbidSolm
              obtain ⟨_, _, rd4406⟩ := flipperDentX_bidOk (g := Sat256.ofUInt256 g)
                (dentHashMem2_size I) hbidEvm rd4308
              by_cases htabEvm : dentBid I = bidTabWord (dentId I) σ_evm I
              · have htabSolm : dentBid I = bidTabWord (dentId I) σ_solm I := by
                  simpa [← htabWordEq] using htabEvm
                have htabGuard :
                    evalExpr? config { contract := contract, locals := locals } evm0
                      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
                        .ok (.bool true) := by
                  simpa [evm0, locals] using
                    evalExpr_dentBidEqBidTab_true (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) htabSolm
                obtain ⟨_, _, rd4507⟩ := flipperDentX_bidEqTabOk (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                  htabEvm rd4406
                by_cases hlotLtEvm :
                    (dentLot I).toNat < (bidLotWord (dentId I) σ_evm I).toNat
                · have hlotLtSolm :
                      (dentLot I).toNat < (bidLotWord (dentId I) σ_solm I).toNat := by
                    simpa [← hlotWordEq] using hlotLtEvm
                  have hlotGuard :
                      evalExpr? config { contract := contract, locals := locals } evm0
                        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
                          .ok (.bool true) := by
                    simpa [evm0, locals] using
                      evalExpr_dentLotLtBidLot_true (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) hlotLtSolm
                  obtain ⟨_, _, rd4601⟩ := flipperDentX_lotLowerOk (g := Sat256.ofUInt256 g)
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                    hlotLtEvm rd4507
                  have hmem4601Size :
                      (twoWordHashMem (dentId I) ⟨1⟩
                        (twoWordHashMem (dentId I) ⟨1⟩
                          (twoWordHashMem (dentId I) ⟨1⟩ (dentHashMem2 I)))).size = 96 :=
                    twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                        (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                  have hmem4601Read64 :
                      (twoWordHashMem (dentId I) ⟨1⟩
                        (twoWordHashMem (dentId I) ⟨1⟩
                          (twoWordHashMem (dentId I) ⟨1⟩ (dentHashMem2 I)))).readWithPadding
                          64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                    twoWordHashMem_read64 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                        (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                      (twoWordHashMem_read64 (dentId I) ⟨1⟩
                        (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                        (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                          (dentHashMem2_read64 I)))
                  exact flipperDentBodyFrom4601LotLower hcode hdispatch hdecode hperm hwv
                    hAccounts hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard
                    hmem4601Size hmem4601Read64 rd4601
                · have hlotLeEvm :
                      (bidLotWord (dentId I) σ_evm I).toNat ≤ (dentLot I).toNat := by
                    omega
                  have hlotLeSolm :
                      (bidLotWord (dentId I) σ_solm I).toNat ≤ (dentLot I).toNat := by
                    simpa [← hlotWordEq] using hlotLeEvm
                  have hbody :
                      ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
                    simpa [evm0, locals] using
                      (flipperDentSourceBodyLotNotLower (cA := cA) (gh := gh)
                        (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := g) hwv hguySolm hticGuard hendGuard hbidGuard htabGuard
                        hlotLeSolm)
                  exact (flipperDentX_lotNotLower (g := Sat256.ofUInt256 g)
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                    (twoWordHashMem_read64 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                      (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                        (dentHashMem2_read64 I)))
                    hlotLeEvm rd4507)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have htabSolm : dentBid I ≠ bidTabWord (dentId I) σ_solm I := by
                  intro htab
                  exact htabEvm (by simpa [htabWordEq] using htab)
                have hbody :
                    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
                  simpa [evm0, locals] using
                    (flipperDentSourceBodyTendNotFinished (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) hwv hguySolm hticGuard hendGuard hbidGuard htabSolm)
                exact (flipperDentX_tendNotFinished (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                  (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                    (dentHashMem2_read64 I))
                  htabEvm rd4406)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hbidSolm : dentBid I ≠ bidBidWord (dentId I) σ_solm I := by
                intro hbid
                exact hbidEvm (by simpa [hbidWordEq] using hbid)
              have hbody :
                  ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
                simpa [evm0, locals] using
                  (flipperDentSourceBodyNotMatchingBid (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) hwv hguySolm hticGuard hendGuard hbidSolm)
              exact (flipperDentX_notMatchingBid (g := Sat256.ofUInt256 g)
                (dentHashMem2_size I) (dentHashMem2_read64 I) hbidEvm rd4308)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hticZeroEvm : bidTicWord (dentId I) σ_evm I = ⟨0⟩ := by
          exact Classical.not_not.mp hticNeEvm
        have hticZeroSolm : bidTicWord (dentId I) σ_solm I = ⟨0⟩ := by
          simpa [← hticEq] using hticZeroEvm
        have hticGuard :
            evalExpr? config { contract := contract, locals := locals } evm0
              (.binary .or
                (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
                .ok (.bool true) := by
          simpa [evm0, locals] using
            evalExpr_dentTicActive_true_right (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) hticZeroSolm
        obtain ⟨_, _, rd4191⟩ :=
          flipperDentX_ticZeroOk (g := Sat256.ofUInt256 g) hticZeroEvm rd4033
        by_cases hendLeEvm :
            (bidEndWord (dentId I) σ_evm I).toNat ≤
              (UInt256.ofNat I.header.timestamp).toNat
        · have hendLeSolm :
              (bidEndWord (dentId I) σ_solm I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            simpa [← hendEq] using hendLeEvm
          have hbody :
              ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
            simpa [evm0, locals] using
              (flipperDentSourceBodyAlreadyFinishedEnd (cA := cA) (gh := gh)
                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) hwv hguySolm hticGuard hendLeSolm)
          exact (flipperDentX_alreadyFinishedEnd (g := Sat256.ofUInt256 g)
            (dentHashMem2_size I) (dentHashMem2_read64 I) hendLeEvm rd4191)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hendGtEvm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidEndWord (dentId I) σ_evm I).toNat := by
            omega
          have hendGtSolm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidEndWord (dentId I) σ_solm I).toNat := by
            simpa [← hendEq] using hendGtEvm
          have hendGuard :
              evalExpr? config { contract := contract, locals := locals } evm0
                (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
                  .ok (.bool true) := by
            simpa [evm0, locals] using
              evalExpr_dentEndGtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) hendGtSolm
          obtain ⟨_, _, rd4308⟩ := flipperDentX_endOk (g := Sat256.ofUInt256 g)
            (dentHashMem2_size I) hendGtEvm rd4191
          by_cases hbidEvm : dentBid I = bidBidWord (dentId I) σ_evm I
          · have hbidSolm : dentBid I = bidBidWord (dentId I) σ_solm I := by
              simpa [← hbidWordEq] using hbidEvm
            have hbidGuard :
                evalExpr? config { contract := contract, locals := locals } evm0
                  (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
                    .ok (.bool true) := by
              simpa [evm0, locals] using
                evalExpr_dentBidEqBidBid_true (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hbidSolm
            obtain ⟨_, _, rd4406⟩ := flipperDentX_bidOk (g := Sat256.ofUInt256 g)
              (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
              hbidEvm rd4308
            by_cases htabEvm : dentBid I = bidTabWord (dentId I) σ_evm I
            · have htabSolm : dentBid I = bidTabWord (dentId I) σ_solm I := by
                simpa [← htabWordEq] using htabEvm
              have htabGuard :
                  evalExpr? config { contract := contract, locals := locals } evm0
                    (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
                      .ok (.bool true) := by
                simpa [evm0, locals] using
                  evalExpr_dentBidEqBidTab_true (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) htabSolm
              obtain ⟨_, _, rd4507⟩ := flipperDentX_bidEqTabOk (g := Sat256.ofUInt256 g)
                (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                htabEvm rd4406
              by_cases hlotLtEvm :
                  (dentLot I).toNat < (bidLotWord (dentId I) σ_evm I).toNat
              · have hlotLtSolm :
                    (dentLot I).toNat < (bidLotWord (dentId I) σ_solm I).toNat := by
                  simpa [← hlotWordEq] using hlotLtEvm
                have hlotGuard :
                    evalExpr? config { contract := contract, locals := locals } evm0
                      (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
                        .ok (.bool true) := by
                  simpa [evm0, locals] using
                    evalExpr_dentLotLtBidLot_true (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) hlotLtSolm
                obtain ⟨_, _, rd4601⟩ := flipperDentX_lotLowerOk (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))))
                  hlotLtEvm rd4507
                have hmem4601Size :
                    (twoWordHashMem (dentId I) ⟨1⟩
                      (twoWordHashMem (dentId I) ⟨1⟩
                        (twoWordHashMem (dentId I) ⟨1⟩
                          (twoWordHashMem (dentId I) ⟨1⟩ (dentHashMem2 I))))).size = 96 :=
                  twoWordHashMem_size_96 (dentId I) ⟨1⟩
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                        (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))))
                have hmem4601Read64 :
                    (twoWordHashMem (dentId I) ⟨1⟩
                      (twoWordHashMem (dentId I) ⟨1⟩
                        (twoWordHashMem (dentId I) ⟨1⟩
                          (twoWordHashMem (dentId I) ⟨1⟩ (dentHashMem2 I))))).readWithPadding
                        64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  twoWordHashMem_read64 (dentId I) ⟨1⟩
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                        (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))))
                    (twoWordHashMem_read64 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                        (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                      (twoWordHashMem_read64 (dentId I) ⟨1⟩
                        (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                        (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                          (dentHashMem2_read64 I))))
                exact flipperDentBodyFrom4601LotLower hcode hdispatch hdecode hperm hwv
                  hAccounts hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard
                  hmem4601Size hmem4601Read64 rd4601
              · have hlotLeEvm :
                    (bidLotWord (dentId I) σ_evm I).toNat ≤ (dentLot I).toNat := by
                  omega
                have hlotLeSolm :
                    (bidLotWord (dentId I) σ_solm I).toNat ≤ (dentLot I).toNat := by
                  simpa [← hlotWordEq] using hlotLeEvm
                have hbody :
                    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
                  simpa [evm0, locals] using
                    (flipperDentSourceBodyLotNotLower (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) hwv hguySolm hticGuard hendGuard hbidGuard htabGuard
                      hlotLeSolm)
                exact (flipperDentX_lotNotLower (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))))
                  (twoWordHashMem_read64 (dentId I) ⟨1⟩
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                    (twoWordHashMem_read64 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                      (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                        (dentHashMem2_read64 I))))
                  hlotLeEvm rd4507)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have htabSolm : dentBid I ≠ bidTabWord (dentId I) σ_solm I := by
                intro htab
                exact htabEvm (by simpa [htabWordEq] using htab)
              have hbody :
                  ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
                simpa [evm0, locals] using
                  (flipperDentSourceBodyTendNotFinished (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) hwv hguySolm hticGuard hendGuard hbidGuard htabSolm)
              exact (flipperDentX_tendNotFinished (g := Sat256.ofUInt256 g)
                (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                (twoWordHashMem_read64 (dentId I) ⟨1⟩
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                  (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                    (dentHashMem2_read64 I)))
                htabEvm rd4406)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hbidSolm : dentBid I ≠ bidBidWord (dentId I) σ_solm I := by
              intro hbid
              exact hbidEvm (by simpa [hbidWordEq] using hbid)
            have hbody :
                ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
              simpa [evm0, locals] using
                (flipperDentSourceBodyNotMatchingBid (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) hwv hguySolm hticGuard hendGuard hbidSolm)
            exact (flipperDentX_notMatchingBid (g := Sat256.ofUInt256 g)
              (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
              (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                (dentHashMem2_read64 I))
              hbidEvm rd4308)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 4) rfl hsel
    have hshort : I.calldata.size < 100 := by omega
    have hdispatch : dispatchMsg contract I.calldata = some dentTransition :=
      flipperDispatchDent hsel
    have hreach := flipperReachDentBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    exact (flipperDentX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_dent_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper

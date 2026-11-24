import Benchmarks.Dss.Flipper.DentBodyBranch

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

theorem flipperDentBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 4)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 4) rfl hsel
    have hdispatch : dispatchMsg contract I.calldata = some dentTransition :=
      flipperDispatchDent hsel
    have hreach := flipperReachDentBody (fork := fork)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    have hdecode := flipperDecode_dent_ok (I := I) hsz100
    obtain ⟨_, _, hdecoded⟩ := flipperDentX_decoded (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    let locals := dentLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hpacked :
        solcSlotWordAt (bidPackedSlotOfWord (dentId I)) σ I =
          solcSlotWordAt (bidPackedSlotOfWord (dentId I)) σ I := rfl
    have hbidWordEq : bidBidWord (dentId I) σ I = bidBidWord (dentId I) σ I := rfl
    have htabWordEq : bidTabWord (dentId I) σ I = bidTabWord (dentId I) σ I := rfl
    have hlotWordEq : bidLotWord (dentId I) σ I = bidLotWord (dentId I) σ I := rfl
    have hbegWordEq : dentBegWord σ I = dentBegWord σ I := rfl
    have hguyEq : bidGuyWord (dentId I) σ I = bidGuyWord (dentId I) σ I := by
      simp [bidGuyWord, solcAddressSlotWord, hpacked]
    have hticEq : bidTicWord (dentId I) σ I = bidTicWord (dentId I) σ I := by
      simp [bidTicWord, flipperUint48Offset20Word, hpacked]
    have hendEq : bidEndWord (dentId I) σ I = bidEndWord (dentId I) σ I := by
      simp [bidEndWord, flipperUint48Offset26Word, hpacked]
    by_cases hguyEvm : bidGuyWord (dentId I) σ I = ⟨0⟩
    · have hguyStele : bidGuyWord (dentId I) σ I = ⟨0⟩ := by
        simpa [← hguyEq] using hguyEvm
      have hbody :
          ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
        simpa [evm0, locals] using
          (flipperDentSourceBodyGuyNotSet
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hguyStele)
      exact (flipperDentX_guyNotSet (g := Sat256.ofUInt256 g) hguyEvm hdecoded)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hguyStele : bidGuyWord (dentId I) σ I ≠ ⟨0⟩ := by
        intro hzero
        exact hguyEvm (by simpa [hguyEq] using hzero)
      obtain ⟨_, _, rd4033⟩ :=
        flipperDentX_guyOk (g := Sat256.ofUInt256 g) hguyEvm hdecoded
      by_cases hticNeEvm : bidTicWord (dentId I) σ I ≠ ⟨0⟩
      · by_cases hticLeEvm :
            (bidTicWord (dentId I) σ I).toNat ≤
              (UInt256.ofNat I.header.timestamp).toNat
        · have hticNeStele : bidTicWord (dentId I) σ I ≠ ⟨0⟩ := by
            intro hzero
            exact hticNeEvm (by simpa [hticEq] using hzero)
          have hticLeStele :
              (bidTicWord (dentId I) σ I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            simpa [← hticEq] using hticLeEvm
          have hbody :
              ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
            simpa [evm0, locals] using
              (flipperDentSourceBodyAlreadyFinishedTic
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) hwv hguyStele hticNeStele hticLeStele)
          exact (flipperDentX_alreadyFinishedTic (g := Sat256.ofUInt256 g)
            hticNeEvm hticLeEvm rd4033)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hticGtEvm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidTicWord (dentId I) σ I).toNat := by
            omega
          have hticGtStele :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidTicWord (dentId I) σ I).toNat := by
            simpa [← hticEq] using hticGtEvm
          have hticGuard :
              evalExpr? config { contract := contract, locals := locals } evm0
                (.binary .or
                  (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                  (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
                  .ok (.bool true) := by
            simpa [evm0, locals] using
              evalExpr_dentTicActive_true_left
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) hticGtStele
          obtain ⟨_, _, rd4191⟩ :=
            flipperDentX_ticGtOk (g := Sat256.ofUInt256 g) hticGtEvm rd4033
          by_cases hendLeEvm :
              (bidEndWord (dentId I) σ I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat
          · have hendLeStele :
                (bidEndWord (dentId I) σ I).toNat ≤
                  (UInt256.ofNat I.header.timestamp).toNat := by
              simpa [← hendEq] using hendLeEvm
            have hbody :
                ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
              simpa [evm0, locals] using
                (flipperDentSourceBodyAlreadyFinishedEnd
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) hwv hguyStele hticGuard hendLeStele)
            exact (flipperDentX_alreadyFinishedEnd (g := Sat256.ofUInt256 g)
              (dentHashMem1_size I) (dentHashMem1_read64 I) hendLeEvm rd4191)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hendGtEvm :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (bidEndWord (dentId I) σ I).toNat := by
              omega
            have hendGtStele :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (bidEndWord (dentId I) σ I).toNat := by
              simpa [← hendEq] using hendGtEvm
            have hendGuard :
                evalExpr? config { contract := contract, locals := locals } evm0
                  (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
                    .ok (.bool true) := by
              simpa [evm0, locals] using
                evalExpr_dentEndGtTimestamp_true
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hendGtStele
            obtain ⟨_, _, rd4308⟩ := flipperDentX_endOk (g := Sat256.ofUInt256 g)
              (dentHashMem1_size I) hendGtEvm rd4191
            by_cases hbidEvm : dentBid I = bidBidWord (dentId I) σ I
            · have hbidStele : dentBid I = bidBidWord (dentId I) σ I := by
                simpa [← hbidWordEq] using hbidEvm
              have hbidGuard :
                  evalExpr? config { contract := contract, locals := locals } evm0
                    (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
                      .ok (.bool true) := by
                simpa [evm0, locals] using
                  evalExpr_dentBidEqBidBid_true
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) hbidStele
              obtain ⟨_, _, rd4406⟩ := flipperDentX_bidOk (g := Sat256.ofUInt256 g)
                (dentHashMem2_size I) hbidEvm rd4308
              by_cases htabEvm : dentBid I = bidTabWord (dentId I) σ I
              · have htabStele : dentBid I = bidTabWord (dentId I) σ I := by
                  simpa [← htabWordEq] using htabEvm
                have htabGuard :
                    evalExpr? config { contract := contract, locals := locals } evm0
                      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
                        .ok (.bool true) := by
                  simpa [evm0, locals] using
                    evalExpr_dentBidEqBidTab_true
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) htabStele
                obtain ⟨_, _, rd4507⟩ := flipperDentX_bidEqTabOk (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                  htabEvm rd4406
                by_cases hlotLtEvm :
                    (dentLot I).toNat < (bidLotWord (dentId I) σ I).toNat
                · have hlotLtStele :
                      (dentLot I).toNat < (bidLotWord (dentId I) σ I).toNat := by
                    simpa [← hlotWordEq] using hlotLtEvm
                  have hlotGuard :
                      evalExpr? config { contract := contract, locals := locals } evm0
                        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
                          .ok (.bool true) := by
                    simpa [evm0, locals] using
                      evalExpr_dentLotLtBidLot_true
                        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) hlotLtStele
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
                  exact flipperDentBodyFrom4601LotLower hcode hdispatch hdecode hwv
                    hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard
                    hmem4601Size hmem4601Read64 rd4601
                · have hlotLeEvm :
                      (bidLotWord (dentId I) σ I).toNat ≤ (dentLot I).toNat := by
                    omega
                  have hlotLeStele :
                      (bidLotWord (dentId I) σ I).toNat ≤ (dentLot I).toNat := by
                    simpa [← hlotWordEq] using hlotLeEvm
                  have hbody :
                      ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
                    simpa [evm0, locals] using
                      (flipperDentSourceBodyLotNotLower
                        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                        (g := g) hwv hguyStele hticGuard hendGuard hbidGuard htabGuard
                        hlotLeStele)
                  exact (flipperDentX_lotNotLower (g := Sat256.ofUInt256 g)
                    (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                    (twoWordHashMem_read64 (dentId I) ⟨1⟩
                      (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                      (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                        (dentHashMem2_read64 I)))
                    hlotLeEvm rd4507)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have htabStele : dentBid I ≠ bidTabWord (dentId I) σ I := by
                  intro htab
                  exact htabEvm (by simpa [htabWordEq] using htab)
                have hbody :
                    ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
                  simpa [evm0, locals] using
                    (flipperDentSourceBodyTendNotFinished
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) hwv hguyStele hticGuard hendGuard hbidGuard htabStele)
                exact (flipperDentX_tendNotFinished (g := Sat256.ofUInt256 g)
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                  (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                    (dentHashMem2_read64 I))
                  htabEvm rd4406)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hbidStele : dentBid I ≠ bidBidWord (dentId I) σ I := by
                intro hbid
                exact hbidEvm (by simpa [hbidWordEq] using hbid)
              have hbody :
                  ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
                simpa [evm0, locals] using
                  (flipperDentSourceBodyNotMatchingBid
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) hwv hguyStele hticGuard hendGuard hbidStele)
              exact (flipperDentX_notMatchingBid (g := Sat256.ofUInt256 g)
                (dentHashMem2_size I) (dentHashMem2_read64 I) hbidEvm rd4308)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hticZeroEvm : bidTicWord (dentId I) σ I = ⟨0⟩ := by
          exact Classical.not_not.mp hticNeEvm
        have hticZeroStele : bidTicWord (dentId I) σ I = ⟨0⟩ := by
          simpa [← hticEq] using hticZeroEvm
        have hticGuard :
            evalExpr? config { contract := contract, locals := locals } evm0
              (.binary .or
                (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
                .ok (.bool true) := by
          simpa [evm0, locals] using
            evalExpr_dentTicActive_true_right
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) hticZeroStele
        obtain ⟨_, _, rd4191⟩ :=
          flipperDentX_ticZeroOk (g := Sat256.ofUInt256 g) hticZeroEvm rd4033
        by_cases hendLeEvm :
            (bidEndWord (dentId I) σ I).toNat ≤
              (UInt256.ofNat I.header.timestamp).toNat
        · have hendLeStele :
              (bidEndWord (dentId I) σ I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            simpa [← hendEq] using hendLeEvm
          have hbody :
              ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
            simpa [evm0, locals] using
              (flipperDentSourceBodyAlreadyFinishedEnd
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) hwv hguyStele hticGuard hendLeStele)
          exact (flipperDentX_alreadyFinishedEnd (g := Sat256.ofUInt256 g)
            (dentHashMem2_size I) (dentHashMem2_read64 I) hendLeEvm rd4191)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hendGtEvm :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidEndWord (dentId I) σ I).toNat := by
            omega
          have hendGtStele :
              (UInt256.ofNat I.header.timestamp).toNat <
                (bidEndWord (dentId I) σ I).toNat := by
            simpa [← hendEq] using hendGtEvm
          have hendGuard :
              evalExpr? config { contract := contract, locals := locals } evm0
                (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
                  .ok (.bool true) := by
            simpa [evm0, locals] using
              evalExpr_dentEndGtTimestamp_true
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) hendGtStele
          obtain ⟨_, _, rd4308⟩ := flipperDentX_endOk (g := Sat256.ofUInt256 g)
            (dentHashMem2_size I) hendGtEvm rd4191
          by_cases hbidEvm : dentBid I = bidBidWord (dentId I) σ I
          · have hbidStele : dentBid I = bidBidWord (dentId I) σ I := by
              simpa [← hbidWordEq] using hbidEvm
            have hbidGuard :
                evalExpr? config { contract := contract, locals := locals } evm0
                  (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
                    .ok (.bool true) := by
              simpa [evm0, locals] using
                evalExpr_dentBidEqBidBid_true
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hbidStele
            obtain ⟨_, _, rd4406⟩ := flipperDentX_bidOk (g := Sat256.ofUInt256 g)
              (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
              hbidEvm rd4308
            by_cases htabEvm : dentBid I = bidTabWord (dentId I) σ I
            · have htabStele : dentBid I = bidTabWord (dentId I) σ I := by
                simpa [← htabWordEq] using htabEvm
              have htabGuard :
                  evalExpr? config { contract := contract, locals := locals } evm0
                    (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
                      .ok (.bool true) := by
                simpa [evm0, locals] using
                  evalExpr_dentBidEqBidTab_true
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) htabStele
              obtain ⟨_, _, rd4507⟩ := flipperDentX_bidEqTabOk (g := Sat256.ofUInt256 g)
                (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                htabEvm rd4406
              by_cases hlotLtEvm :
                  (dentLot I).toNat < (bidLotWord (dentId I) σ I).toNat
              · have hlotLtStele :
                    (dentLot I).toNat < (bidLotWord (dentId I) σ I).toNat := by
                  simpa [← hlotWordEq] using hlotLtEvm
                have hlotGuard :
                    evalExpr? config { contract := contract, locals := locals } evm0
                      (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
                        .ok (.bool true) := by
                  simpa [evm0, locals] using
                    evalExpr_dentLotLtBidLot_true
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) hlotLtStele
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
                exact flipperDentBodyFrom4601LotLower hcode hdispatch hdecode hwv
                  hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard
                  hmem4601Size hmem4601Read64 rd4601
              · have hlotLeEvm :
                    (bidLotWord (dentId I) σ I).toNat ≤ (dentLot I).toNat := by
                  omega
                have hlotLeStele :
                    (bidLotWord (dentId I) σ I).toNat ≤ (dentLot I).toNat := by
                  simpa [← hlotWordEq] using hlotLeEvm
                have hbody :
                    ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
                  simpa [evm0, locals] using
                    (flipperDentSourceBodyLotNotLower
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) hwv hguyStele hticGuard hendGuard hbidGuard htabGuard
                      hlotLeStele)
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
            · have htabStele : dentBid I ≠ bidTabWord (dentId I) σ I := by
                intro htab
                exact htabEvm (by simpa [htabWordEq] using htab)
              have hbody :
                  ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
                simpa [evm0, locals] using
                  (flipperDentSourceBodyTendNotFinished
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) hwv hguyStele hticGuard hendGuard hbidGuard htabStele)
              exact (flipperDentX_tendNotFinished (g := Sat256.ofUInt256 g)
                (twoWordHashMem_size_96 (dentId I) ⟨1⟩
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I)))
                (twoWordHashMem_read64 (dentId I) ⟨1⟩
                  (twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem2_size I))
                  (twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem2_size I)
                    (dentHashMem2_read64 I)))
                htabEvm rd4406)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hbidStele : dentBid I ≠ bidBidWord (dentId I) σ I := by
              intro hbid
              exact hbidEvm (by simpa [hbidWordEq] using hbid)
            have hbody :
                ExecTransitionBody fork config contract evm0 locals dentTransition.body .reverted := by
              simpa [evm0, locals] using
                (flipperDentSourceBodyNotMatchingBid
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) hwv hguyStele hticGuard hendGuard hbidStele)
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
    have hreach := flipperReachDentBody (fork := fork)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    exact (flipperDentX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_dent_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper

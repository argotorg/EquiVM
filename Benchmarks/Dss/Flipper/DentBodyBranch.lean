import Benchmarks.Dss.Flipper.DentRefundMain

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Shared `dent` branch after the lot-lower guard -/

theorem flipperDentBodyFrom4601LotLower
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {k C : ℕ} {mem : ByteArray} {sel : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hguySolm : bidGuyWord (dentId I) σ_solm I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4601⟩
      [dentBid I, dentLot I, dentId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let locals := dentLocals I
  have hlotWordEq : bidLotWord (dentId I) σ_evm I = bidLotWord (dentId I) σ_solm I := by
    simpa [bidLotWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) ⟨0⟩
  have hbegWordEq : dentBegWord σ_evm I = dentBegWord σ_solm I := by
    simpa [dentBegWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  have hpacked :
      flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ_evm I =
        flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner
      (bidPackedSlotOfWord (dentId I)) ⟨0⟩
  have hguyEq : bidGuyWord (dentId I) σ_evm I = bidGuyWord (dentId I) σ_solm I := by
    simp [bidGuyWord, flipperAddressReturnWord, hpacked]
  have hlotOneWordEq : dentLotOneWord σ_evm I = dentLotOneWord σ_solm I := by
    simp [dentLotOneWord, hlotWordEq]
  have hbegLotWordEq : dentBegLotWord σ_evm I = dentBegLotWord σ_solm I := by
    simp [dentBegLotWord, hbegWordEq]
  by_cases hoverLot :
      UInt256.size ≤ (bidLotWord (dentId I) σ_evm I).toNat * flipperONEWord.toNat
  · have hoverLotSolm :
        UInt256.size ≤ (bidLotWord (dentId I) σ_solm I).toNat * flipperONEWord.toNat := by
      simpa [← hlotWordEq] using hoverLot
    have hbody :
        ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
      simpa [evm0, locals] using
        (flipperDentSourceBodyLotOneOverflow (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hoverLotSolm)
    exact (flipperDentX_lotOneOverflow hmemSize hoverLot h)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hfitLotEvm :
        (bidLotWord (dentId I) σ_evm I).toNat * flipperONEWord.toNat < UInt256.size :=
      Nat.lt_of_not_ge hoverLot
    have hfitLotSolm :
        (bidLotWord (dentId I) σ_solm I).toNat * flipperONEWord.toNat < UInt256.size := by
      simpa [← hlotWordEq] using hfitLotEvm
    by_cases hoverBeg : UInt256.size ≤ (dentBegWord σ_evm I).toNat * (dentLot I).toNat
    · have hoverBegSolm :
          UInt256.size ≤ (dentBegWord σ_solm I).toNat * (dentLot I).toNat := by
        simpa [← hbegWordEq] using hoverBeg
      have hbody :
          ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
        simpa [evm0, locals] using
          (flipperDentSourceBodyBegLotOverflow (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLotSolm
            hoverBegSolm)
      exact (flipperDentX_begLotOverflow hmemSize hfitLotEvm hoverBeg h)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hfitBegEvm :
          (dentBegWord σ_evm I).toNat * (dentLot I).toNat < UInt256.size :=
        Nat.lt_of_not_ge hoverBeg
      have hfitBegSolm :
          (dentBegWord σ_solm I).toNat * (dentLot I).toNat < UInt256.size := by
        simpa [← hbegWordEq] using hfitBegEvm
      obtain ⟨_, _, rd4650⟩ :=
        flipperDentX_checkedMulOk hmemSize hfitLotEvm hfitBegEvm h
      let mem4650 := twoWordHashMem (dentId I) ⟨1⟩ mem
      have hmem4650Size : mem4650.size = 96 := by
        dsimp [mem4650]
        exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
      have hmem4650Read64 :
          mem4650.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        dsimp [mem4650]
        exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
      by_cases hdecEvm :
          (dentBegLotWord σ_evm I).toNat ≤ (dentLotOneWord σ_evm I).toNat
      · have hdecSolmNat :
            (dentBegLotWord σ_solm I).toNat ≤ (dentLotOneWord σ_solm I).toNat := by
          simpa [← hbegLotWordEq, ← hlotOneWordEq] using hdecEvm
        have hdec :
            evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ_solm I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true) :=
          evalExpr_dentDecreaseRequire_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
            hdecSolmNat
        obtain ⟨_, _, rd4733⟩ := flipperDentX_decreaseOk hdecEvm rd4650
        by_cases hcallerEvm : solcSourceWord I = bidGuyWord (dentId I) σ_evm I
        · have hcallerSolm : solcSourceWord I = bidGuyWord (dentId I) σ_solm I := by
            simpa [hguyEq] using hcallerEvm
          exact flipperDentBodyFrom4733SameCaller hcode hdispatch hdecode hperm hwv
            hAccounts hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLotSolm
            hfitBegSolm hdec hcallerEvm hcallerSolm hmem4650Size hmem4650Read64 rd4733
        · have hcallerSolm : solcSourceWord I ≠ bidGuyWord (dentId I) σ_solm I := by
            intro hcaller
            exact hcallerEvm (by simpa [hguyEq] using hcaller)
          exact flipperDentBodyFrom4733Refund hcode hdispatch hdecode hperm hwv hAccounts
            hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLotSolm hfitBegSolm
            hdec hcallerEvm hcallerSolm hmem4650Size hmem4650Read64 rd4733
      · have hgtEvm :
            (dentLotOneWord σ_evm I).toNat < (dentBegLotWord σ_evm I).toNat :=
          Nat.lt_of_not_ge hdecEvm
        have hgtSolm :
            (dentLotOneWord σ_solm I).toNat < (dentBegLotWord σ_solm I).toNat := by
          simpa [← hlotOneWordEq, ← hbegLotWordEq] using hgtEvm
        have hbody :
            ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
          simpa [evm0, locals] using
            (flipperDentSourceBodyInsufficientDecrease (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitBegSolm
              hfitLotSolm hgtSolm)
        exact (flipperDentX_insufficientDecrease hmem4650Size hmem4650Read64 hgtEvm rd4650)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Flipper

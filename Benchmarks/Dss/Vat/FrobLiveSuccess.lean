import Benchmarks.Dss.Vat.FrobLiveBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vat

suppress_compilation

/- This wrapper timed out by itself; the source-body proof calls
   `execFrobFinalStoreTailOk` directly below instead. -/
/- set_option maxHeartbeats 0 in
theorem execFrobFinalStoreTailFromConstructedLocals {evmDebt : EVM.State} {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld gemOld gemNew daiOld daiNew dtabWord : UInt256)
    (hdtabRange : -((2 : Int) ^ 255) ≤ dtab ∧ dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hloadGem :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hloadDai :
      let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) gemNew
      Solm.EVM.storageLoad evmGem evmGem.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hgemNew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hdaiNew : daiNew = dtabWord + daiOld)
    (hGemPosS :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt gemNew gemOld = ⟨0⟩)
    (hGemNegS :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt gemNew gemOld = ⟨0⟩)
    (hDaiNegS :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt daiNew daiOld = ⟨0⟩)
    (hDaiPosS :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt daiNew daiOld = ⟨0⟩) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
    let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) ilkRate
    let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) ilkSpot
    let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) ilkLine
    let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) ilkDust
    ExecBlock config { contract := contract, locals := localsSafe } evmDebt
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
      (.ok
        { contract := contract,
          locals :=
            (localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert
              "daiNew" (.int (Int.ofNat daiNew.toNat)) }
        evmDust) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab debtNew
    localsDebt ceilingDebt inkSpot localsSafe evmGem evmDai evmInk evmArt evmIlk
    evmRate evmSpot evmLine evmDust
  have hparam :
      localsSafe.get? "i" = some (frobIValue I) ∧
      localsSafe.get? "u" = some (frobUValue I) ∧
      localsSafe.get? "v" = some (frobVValue I) ∧
      localsSafe.get? "w" = some (frobWValue I) ∧
      localsSafe.get? "dink" = some (frobDinkValue I) := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsParamFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hcomputed :
      localsSafe.get? "dtab" = some (.int dtab) ∧
      localsSafe.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) ∧
      localsSafe.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) ∧
      localsSafe.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsComputedFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hilks :
      localsSafe.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) ∧
      localsSafe.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) ∧
      localsSafe.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) ∧
      localsSafe.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)) := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsIlkFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hbase :
      localsSafe.get? "gem" = none ∧
      localsSafe.get? "dai" = none ∧
      localsSafe.get? "urns" = none ∧
      localsSafe.get? "ilks" = none := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsBaseFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  rcases hparam with ⟨hsafeI, hsafeU, hsafeV, hsafeW, hsafeDink⟩
  rcases hcomputed with
    ⟨hsafeDtab, hsafeUrnInkNew, hsafeUrnArtNew, hsafeIlkArtNew⟩
  rcases hilks with
    ⟨hsafeIlkRate, hsafeIlkSpot, hsafeIlkLine, hsafeIlkDust⟩
  rcases hbase with
    ⟨hsafeBaseGem, hsafeBaseDai, hsafeBaseUrns, hsafeBaseIlks⟩
  exact execFrobFinalStoreTailOk (evm := evmDebt) (I := I) localsSafe
    gemOld gemNew daiOld daiNew dtabWord dtab urnInkNew urnArtNew ilkArtNew
    ilkRate ilkSpot ilkLine ilkDust hsz196
    hsafeI hsafeU hsafeV hsafeW hsafeDink hsafeDtab hsafeUrnInkNew
    hsafeUrnArtNew hsafeIlkArtNew hsafeIlkRate hsafeIlkSpot hsafeIlkLine
    hsafeIlkDust hsafeBaseGem hsafeBaseDai hsafeBaseUrns hsafeBaseIlks
    hloadGem
    hloadDai
    hgemNew
    hdaiNew
    hdtabMod
    (frobDinkSubGuardNegCond hGemPosS)
    (frobDinkSubGuardPosCond hGemNegS)
    (signedAddGuardNegCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod hDaiNegS)
    (signedAddGuardPosCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod hDaiPosS)
-/

set_option maxHeartbeats 0 in
theorem execFrobGemDaiUpdatesOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (gemOld gemNew daiOld daiNew dtabWord : UInt256) (dtab : Int)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (frobIValue I))
    (hv : locals.get? "v" = some (frobVValue I))
    (hw : locals.get? "w" = some (frobWValue I))
    (hdink : locals.get? "dink" = some (frobDinkValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbaseGem : locals.get? "gem" = none)
    (hbaseDai : locals.get? "dai" = none)
    (hloadGem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hloadDai :
      let evmGem := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (frobGemVSourceSlot I) gemNew
      Solm.EVM.storageLoad evmGem evmGem.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hgemNew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hdaiNew : daiNew = dtabWord + daiOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hGemNeg : frobDinkInt I ≤ 0 ∨ gemNew.toNat ≤ gemOld.toNat)
    (hGemPos : 0 ≤ frobDinkInt I ∨ gemOld.toNat ≤ gemNew.toNat)
    (hDaiNeg : 0 ≤ dtab ∨ daiNew.toNat ≤ daiOld.toNat)
    (hDaiPos : dtab ≤ 0 ∨ daiOld.toNat ≤ daiNew.toNat) :
    let evmGem := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
    let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    let localsGem := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
    let localsDai := localsGem.insert "daiNew" (.int (Int.ofNat daiNew.toNat))
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew") ])
      (.ok { contract := contract, locals := localsDai } evmDai) := by
  intro evmGem evmDai localsGem localsDai
  have hgemBlock :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
        (.ok { contract := contract, locals := localsGem } evmGem) := by
    simpa [localsGem, evmGem] using
      execFrobGemUpdateOk (evm := evm) (I := I) locals gemOld gemNew hsz196
        hi hv hdink hbaseGem hloadGem hgemNew hGemNeg hGemPos
  have hwGem : localsGem.get? "w" = some (frobWValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "w" =
      some (frobWValue I)
    rw [store_get_ne _ _ (by decide)]
    exact hw
  have hdtabGem : localsGem.get? "dtab" = some (.int dtab) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dtab" =
      some (.int dtab)
    rw [store_get_ne _ _ (by decide)]
    exact hdtab
  have hbaseDaiGem : localsGem.get? "dai" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dai" = none
    rw [store_get_ne _ _ (by decide)]
    exact hbaseDai
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := localsGem } evmGem
        (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew") ])
        (.ok { contract := contract, locals := localsDai } evmDai) := by
    simpa [localsGem, localsDai, evmGem, evmDai] using
      execFrobDaiUpdateOk (evm := evmGem) (I := I) localsGem daiOld daiNew
        dtabWord dtab hwGem hdtabGem hbaseDaiGem (by simpa [evmGem] using hloadDai)
        hdtabMod hdaiNew hDaiNeg hDaiPos
  have h := execBlock_append hgemBlock hdaiBlock
  simpa [localsGem, localsDai, evmGem, evmDai, List.append_assoc] using h

set_option maxHeartbeats 0 in
theorem execFrobFinalStorageAssignmentsOk {evmDai : EVM.State} {I : ExecutionEnv}
    (localsDai : Store)
    (urnInkNew urnArtNew ilkArtNew ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : localsDai.get? "i" = some (frobIValue I))
    (hu : localsDai.get? "u" = some (frobUValue I))
    (hbaseUrns : localsDai.get? "urns" = none)
    (hbaseIlks : localsDai.get? "ilks" = none)
    (hurnInkNew :
      localsDai.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)))
    (hurnArtNew :
      localsDai.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)))
    (hilkArtNew :
      localsDai.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)))
    (hilkRate :
      localsDai.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hilkSpot :
      localsDai.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)))
    (hilkLine :
      localsDai.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)))
    (hilkDust :
      localsDai.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat))) :
    let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) ilkRate
    let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) ilkSpot
    let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) ilkLine
    let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) ilkDust
    ExecBlock config { contract := contract, locals := localsDai } evmDai
      [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ]
      (.ok { contract := contract, locals := localsDai } evmDust) := by
  intro evmInk evmArt evmIlk evmRate evmSpot evmLine evmDust
  have evalVarAfterDai {evm' : EVM.State} {name : Ident} {value : UInt256}
      (hget : localsDai.get? name = some (.int (Int.ofNat value.toNat))) :
      evalExpr? config { contract := contract, locals := localsDai } evm' (.var name) =
        .ok (.int (Int.ofNat value.toNat)) :=
    vatEvalExpr_varUInt256 hget
  have hassignInk :
      assignStorageRef? config { contract := contract, locals := localsDai } evmDai
        .storage (urnsF (.var "i") (.var "u") "ink")
        (.int (Int.ofNat urnInkNew.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmInk) := by
    simpa [evmInk] using
      assignStorageRef_frob_urn_ink evmDai I localsDai urnInkNew hsz196 hi hu hbaseUrns
  have hassignArt :
      assignStorageRef? config { contract := contract, locals := localsDai } evmInk
        .storage (urnsF (.var "i") (.var "u") "art")
        (.int (Int.ofNat urnArtNew.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmArt) := by
    simpa [evmArt] using
      assignStorageRef_frob_urn_art evmInk I localsDai urnArtNew hsz196 hi hu hbaseUrns
  have hassignIlkArt :
      assignStorageRef? config { contract := contract, locals := localsDai } evmArt
        .storage (ilksF (.var "i") "Art") (.int (Int.ofNat ilkArtNew.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmIlk) := by
    simpa [evmIlk] using
      assignStorageRef_frob_ilk_art evmArt I localsDai ilkArtNew hsz196 hi hbaseIlks
  have hassignRate :
      assignStorageRef? config { contract := contract, locals := localsDai } evmIlk
        .storage (ilksF (.var "i") "rate") (.int (Int.ofNat ilkRate.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmRate) := by
    simpa [evmRate] using
      assignStorageRef_frob_ilk_rate evmIlk I localsDai ilkRate hsz196 hi hbaseIlks
  have hassignSpot :
      assignStorageRef? config { contract := contract, locals := localsDai } evmRate
        .storage (ilksF (.var "i") "spot") (.int (Int.ofNat ilkSpot.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmSpot) := by
    simpa [evmSpot] using
      assignStorageRef_frob_ilk_spot evmRate I localsDai ilkSpot hsz196 hi hbaseIlks
  have hassignLine :
      assignStorageRef? config { contract := contract, locals := localsDai } evmSpot
        .storage (ilksF (.var "i") "line") (.int (Int.ofNat ilkLine.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmLine) := by
    simpa [evmLine] using
      assignStorageRef_frob_ilk_line evmSpot I localsDai ilkLine hsz196 hi hbaseIlks
  have hassignDust :
      assignStorageRef? config { contract := contract, locals := localsDai } evmLine
        .storage (ilksF (.var "i") "dust") (.int (Int.ofNat ilkDust.toNat)) =
      .ok ({ contract := contract, locals := localsDai }, evmDust) := by
    simpa [evmDust] using
      assignStorageRef_frob_ilk_dust evmLine I localsDai ilkDust hsz196 hi hbaseIlks
  refine ExecBlock.consNormal (ExecStmt.assign (evalVarAfterDai hurnInkNew) hassignInk) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalVarAfterDai hurnArtNew) hassignArt) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalVarAfterDai hilkArtNew) hassignIlkArt) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalVarAfterDai hilkRate) hassignRate) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalVarAfterDai hilkSpot) hassignSpot) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalVarAfterDai hilkLine) hassignLine) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (evalVarAfterDai hilkDust) hassignDust)
    ExecBlock.nil

set_option maxHeartbeats 0 in
theorem frobConstructedLocalsParamFacts {I : ExecutionEnv}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld dtabWord : UInt256) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    localsSafe.get? "i" = some (frobIValue I) ∧
    localsSafe.get? "u" = some (frobUValue I) ∧
    localsSafe.get? "v" = some (frobVValue I) ∧
    localsSafe.get? "w" = some (frobWValue I) ∧
    localsSafe.get? "dink" = some (frobDinkValue I) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab debtNew
    localsDebt ceilingDebt inkSpot localsSafe
  exact ⟨
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "i" =
          some (frobIValue I)
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded, frobStoreIlkDust] using
        frobStoreIlkLine_get_i I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "u" =
          some (frobUValue I)
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_u I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
          ilkDust),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "v" =
          some (frobVValue I)
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_v I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
          ilkDust),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "w" =
          some (frobWValue I)
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_w I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
          ilkDust),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "dink" =
          some (frobDinkValue I)
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
          ilkDust)⟩

set_option maxHeartbeats 0 in
theorem frobConstructedLocalsComputedFacts {I : ExecutionEnv}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld dtabWord : UInt256) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    localsSafe.get? "dtab" = some (.int dtab) ∧
    localsSafe.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) ∧
    localsSafe.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) ∧
    localsSafe.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab debtNew
    localsDebt ceilingDebt inkSpot localsSafe
  exact ⟨
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "dtab" = some (.int dtab)
      repeat rw [store_get_ne _ _ (by decide)]
      rw [store_get_self]),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "urnInkNew" =
          some (.int (Int.ofNat urnInkNew.toNat))
      repeat rw [store_get_ne _ _ (by decide)]
      rw [store_get_self]),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "urnArtNew" =
          some (.int (Int.ofNat urnArtNew.toNat))
      repeat rw [store_get_ne _ _ (by decide)]
      rw [store_get_self]),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "ilkArtNew" =
          some (.int (Int.ofNat ilkArtNew.toNat))
      repeat rw [store_get_ne _ _ (by decide)]
      rw [store_get_self])⟩

set_option maxHeartbeats 0 in
theorem frobConstructedLocalsIlkFacts {I : ExecutionEnv}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld dtabWord : UInt256) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    localsSafe.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) ∧
    localsSafe.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) ∧
    localsSafe.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) ∧
    localsSafe.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab debtNew
    localsDebt ceilingDebt inkSpot localsSafe
  exact ⟨
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot
          ilkLine ilkDust),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "ilkSpot" =
          some (.int (Int.ofNat ilkSpot.toNat))
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_spot I urnInk urnArt ilkArt ilkRate ilkSpot
          ilkLine ilkDust),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "ilkLine" =
          some (.int (Int.ofNat ilkLine.toNat))
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_line I urnInk urnArt ilkArt ilkRate ilkSpot
          ilkLine ilkDust),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "ilkDust" =
          some (.int (Int.ofNat ilkDust.toNat))
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded, frobStoreIlkDust] using
        store_get_self (frobStoreIlkLine I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine)
          "ilkDust" (.int (Int.ofNat ilkDust.toNat)))⟩

set_option maxHeartbeats 0 in
theorem frobConstructedLocalsBaseFacts {I : ExecutionEnv}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld dtabWord : UInt256) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    localsSafe.get? "gem" = none ∧
    localsSafe.get? "dai" = none ∧
    localsSafe.get? "urns" = none ∧
    localsSafe.get? "ilks" = none := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab debtNew
    localsDebt ceilingDebt inkSpot localsSafe
  exact ⟨
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "gem" = none
      repeat rw [store_get_ne _ _ (by decide)]
      simp [localsLoaded, frobStoreIlkDust, frobStoreIlkLine, frobStoreIlkSpot,
        frobStoreIlkRate, frobStoreIlkArt, frobStoreUrnArt, frobStoreUrnInk,
        frobStore]),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "dai" = none
      repeat rw [store_get_ne _ _ (by decide)]
      simp [localsLoaded, frobStoreIlkDust, frobStoreIlkLine, frobStoreIlkSpot,
        frobStoreIlkRate, frobStoreIlkArt, frobStoreUrnArt, frobStoreUrnInk,
        frobStore]),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "urns" = none
      repeat rw [store_get_ne _ _ (by decide)]
      simp [localsLoaded, frobStoreIlkDust, frobStoreIlkLine, frobStoreIlkSpot,
        frobStoreIlkRate, frobStoreIlkArt, frobStoreUrnArt, frobStoreUrnInk,
        frobStore]),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "ilks" = none
      repeat rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded, frobStoreIlkDust] using
        frobStoreIlkLine_ilks I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine)⟩

/- This wrapper stalls under the current dependency set. The source-body proof below calls
   `execFrobFinalStoreTailOk` directly, as the earlier note in this file intended. -/
/- set_option maxHeartbeats 0 in
theorem execFrobFinalStoreTailFromConstructedLocalsSplit {evmDebt : EVM.State}
    {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size)
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld gemOld gemNew daiOld daiNew dtabWord : UInt256)
    (hdtabRange : -((2 : Int) ^ 255) ≤ dtab ∧ dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hloadGem :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld)
    (hloadDai :
      let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) gemNew
      Solm.EVM.storageLoad evmGem evmGem.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld)
    (hgemNew : gemNew = UInt256.sub gemOld (frobDinkWord I))
    (hdaiNew : daiNew = dtabWord + daiOld)
    (hGemPosS :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt gemNew gemOld = ⟨0⟩)
    (hGemNegS :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt gemNew gemOld = ⟨0⟩)
    (hDaiNegS :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt daiNew daiOld = ⟨0⟩)
    (hDaiPosS :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt daiNew daiOld = ⟨0⟩) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
    let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) ilkRate
    let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) ilkSpot
    let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) ilkLine
    let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) ilkDust
    ExecBlock config { contract := contract, locals := localsSafe } evmDebt
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
      (.ok
        { contract := contract,
          locals :=
            (localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert
              "daiNew" (.int (Int.ofNat daiNew.toNat)) }
        evmDust) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab debtNew
    localsDebt ceilingDebt inkSpot localsSafe evmGem evmDai evmInk evmArt evmIlk
    evmRate evmSpot evmLine evmDust
  have hparam :
      localsSafe.get? "i" = some (frobIValue I) ∧
      localsSafe.get? "u" = some (frobUValue I) ∧
      localsSafe.get? "v" = some (frobVValue I) ∧
      localsSafe.get? "w" = some (frobWValue I) ∧
      localsSafe.get? "dink" = some (frobDinkValue I) := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsParamFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hcomputed :
      localsSafe.get? "dtab" = some (.int dtab) ∧
      localsSafe.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) ∧
      localsSafe.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) ∧
      localsSafe.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsComputedFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hilks :
      localsSafe.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) ∧
      localsSafe.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) ∧
      localsSafe.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) ∧
      localsSafe.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)) := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsIlkFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hbase :
      localsSafe.get? "gem" = none ∧
      localsSafe.get? "dai" = none ∧
      localsSafe.get? "urns" = none ∧
      localsSafe.get? "ilks" = none := by
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
      using frobConstructedLocalsBaseFacts (I := I) urnInk urnArt ilkArt
        ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  rcases hparam with ⟨hsafeI, hsafeU, hsafeV, hsafeW, hsafeDink⟩
  rcases hcomputed with
    ⟨hsafeDtab, hsafeUrnInkNew, hsafeUrnArtNew, hsafeIlkArtNew⟩
  rcases hilks with
    ⟨hsafeIlkRate, hsafeIlkSpot, hsafeIlkLine, hsafeIlkDust⟩
  rcases hbase with
    ⟨hsafeBaseGem, hsafeBaseDai, hsafeBaseUrns, hsafeBaseIlks⟩
  let localsGem := localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  let localsDai := localsGem.insert "daiNew" (.int (Int.ofNat daiNew.toNat))
  have hgemDai :
      ExecBlock config { contract := contract, locals := localsSafe } evmDebt
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew") ])
        (.ok { contract := contract, locals := localsDai } evmDai) := by
    simpa [localsGem, localsDai, evmGem, evmDai] using
      execFrobGemDaiUpdatesOk (evm := evmDebt) (I := I) localsSafe
        gemOld gemNew daiOld daiNew dtabWord dtab hsz196
        hsafeI hsafeV hsafeW hsafeDink hsafeDtab hsafeBaseGem hsafeBaseDai
        hloadGem hloadDai hgemNew hdaiNew hdtabMod
        (frobDinkSubGuardNegCond hGemPosS)
        (frobDinkSubGuardPosCond hGemNegS)
        (signedAddGuardNegCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod hDaiNegS)
        (signedAddGuardPosCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod hDaiPosS)
  have hTailBaseI : localsDai.get? "i" = some (frobIValue I) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "i" = some (frobIValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeI
  have hTailBaseU : localsDai.get? "u" = some (frobUValue I) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "u" = some (frobUValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeU
  have hTailUrns : localsDai.get? "urns" = none := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "urns" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeBaseUrns
  have hTailIlks : localsDai.get? "ilks" = none := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "ilks" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeBaseIlks
  have hTailUrnInkNew :
      localsDai.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "urnInkNew" =
      some (.int (Int.ofNat urnInkNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeUrnInkNew
  have hTailUrnArtNew :
      localsDai.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "urnArtNew" =
      some (.int (Int.ofNat urnArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeUrnArtNew
  have hTailIlkArtNew :
      localsDai.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "ilkArtNew" =
      some (.int (Int.ofNat ilkArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeIlkArtNew
  have hTailIlkRate :
      localsDai.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "ilkRate" =
      some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeIlkRate
  have hTailIlkSpot :
      localsDai.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "ilkSpot" =
      some (.int (Int.ofNat ilkSpot.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeIlkSpot
  have hTailIlkLine :
      localsDai.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "ilkLine" =
      some (.int (Int.ofNat ilkLine.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeIlkLine
  have hTailIlkDust :
      localsDai.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)) := by
    change ((localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert "daiNew"
      (.int (Int.ofNat daiNew.toNat))).get? "ilkDust" =
      some (.int (Int.ofNat ilkDust.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    exact hsafeIlkDust
  have hstores :
      ExecBlock config { contract := contract, locals := localsDai } evmDai
        [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ]
        (.ok { contract := contract, locals := localsDai } evmDust) := by
    simpa [evmInk, evmArt, evmIlk, evmRate, evmSpot, evmLine, evmDust] using
      execFrobFinalStorageAssignmentsOk (evmDai := evmDai) (I := I) localsDai
        urnInkNew urnArtNew ilkArtNew ilkRate ilkSpot ilkLine ilkDust hsz196
        hTailBaseI hTailBaseU hTailUrns hTailIlks hTailUrnInkNew hTailUrnArtNew
        hTailIlkArtNew hTailIlkRate hTailIlkSpot hTailIlkLine hTailIlkDust
  have h := execBlock_append hgemDai hstores
  simpa [localsGem, localsDai, evmGem, evmDai, evmInk, evmArt, evmIlk, evmRate,
    evmSpot, evmLine, evmDust, List.append_assoc] using h
-/

set_option maxHeartbeats 0 in
theorem vatFrobSourceBodySuccessFromDustBlock
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size)
    (hsourceDust :
      let urnInk := vatSlotWord (frobUrnInkSlot I) σ I
      let urnArt := vatSlotWord (frobUrnArtSlot I) σ I
      let ilkArt := vatSlotWord (frobIlkArtSlot I) σ I
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ I
      let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ I
      let ilkLine := vatSlotWord (frobIlkLineSlot I) σ I
      let ilkDust := vatSlotWord (frobIlkDustSlot I) σ I
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
      let localsDtab := localsIlk.insert "dtab" (.int dtab)
      let tab := UInt256.mul ilkRate urnArtNew
      let debtOld := vatSlotWord foldDebtSlot σ I
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate
      let debtNew := dtabWord + debtOld
      let localsDebt :=
        (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
          "debtNew" (.int (Int.ofNat debtNew.toNat))
      let evmDebt :=
        Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
          debtNew
      let ceilingDebt := UInt256.mul ilkArtNew ilkRate
      let inkSpot := UInt256.mul urnInkNew ilkSpot
      let localsSafe :=
        (localsDebt.insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ])
        (.ok { contract := contract, locals := localsSafe } evmDebt))
    (hdtabRange :
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ I;
      let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I;
      -((2 : Int) ^ 255) ≤ dtab ∧ dtab < (2 : Int) ^ 255)
    (hGemPosS :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobGemNew σ I)
          (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩)
    (hGemNegS :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobGemNew σ I)
          (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩)
    (hDaiNegS :
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ I;
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate;
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDaiNew σ I)
          (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩)
    (hDaiPosS :
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ I;
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate;
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDaiNew σ I)
          (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩) :
    let urnInk := vatSlotWord (frobUrnInkSlot I) σ I
    let urnArt := vatSlotWord (frobUrnArtSlot I) σ I
    let ilkArt := vatSlotWord (frobIlkArtSlot I) σ I
    let ilkRate := vatSlotWord (frobIlkRateSlot I) σ I
    let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ I
    let ilkLine := vatSlotWord (frobIlkLineSlot I) σ I
    let ilkDust := vatSlotWord (frobIlkDustSlot I) σ I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtOld := vatSlotWord foldDebtSlot σ I
    let dtabWord := UInt256.mul (frobDartWord I) ilkRate
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let evmDebt :=
      Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
        debtNew
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    let gemOld := solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)
    let gemNew := frobGemNew σ I
    let evmGem :=
      Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) gemNew
    let daiOld := solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)
    let daiNew := frobDaiNew σ I
    let finalLocals :=
      (localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert
        "daiNew" (.int (Int.ofNat daiNew.toNat))
    let evmDai :=
      Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
        (frobDaiWSourceSlot I) daiNew
    let evmInk :=
      Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
        (frobUrnInkSourceSlot I) urnInkNew
    let evmArt :=
      Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
        (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk :=
      Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
        (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate :=
      Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
        (frobIlkRateSourceSlot I) ilkRate
    let evmSpot :=
      Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
        (frobIlkSpotSourceSlot I) ilkSpot
    let evmLine :=
      Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
        (frobIlkLineSourceSlot I) ilkLine
    let evmDust :=
      Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
        (frobIlkDustSourceSlot I) ilkDust
    let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
    let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
    let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
    let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
    let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) ilkRate
    let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) ilkSpot
    let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) ilkLine
    let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) ilkDust
    ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
      (.returned { contract := contract, locals := finalLocals } evmDust none) := by
  intro urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust evm0 localsLoaded
    urnInkNew urnArtNew ilkArtNew localsIlk dtab localsDtab tab debtOld dtabWord
    debtNew localsDebt evmDebt ceilingDebt inkSpot localsSafe gemOld gemNew evmGem
    daiOld daiNew finalLocals evmDai evmInk evmArt evmIlk evmRate evmSpot evmLine
    evmDust
  have hdtabMod :
      dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat := by
    change
      (Int.ofNat ilkRate.toNat * frobDartInt I) %
          (Int.ofNat EVM.wordModulus) =
        Int.ofNat (UInt256.mul (frobDartWord I) ilkRate).toNat
    exact frobDtab_mod_word I ilkRate
  have hloadGem :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld := by
    simp [evmDebt, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageStore_accountMap, storageStore_executionEnv,
      frobAfterDebt, frobDebtNew, gemOld, debtNew, dtabWord, debtOld,
      frobDtabWord, ilkRate, vatSlotWord, frobGemVSourceSlot_eq I hsz196]
  have hloadDai :
      Solm.EVM.storageLoad evmGem evmGem.executionEnv.codeOwner
        (frobDaiWSourceSlot I) = daiOld := by
    simp [evmGem, evmDebt, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
      storageStore_executionEnv, frobAfterGem, frobAfterDebt, frobDebtNew,
      frobGemNew, gemNew, gemOld, daiOld, debtNew, dtabWord, debtOld,
      frobDtabWord, ilkRate, vatSlotWord, frobGemVSourceSlot_eq I hsz196,
      frobDaiWSourceSlot_eq I]
  have htail :
      let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) gemNew
      let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
        (frobDaiWSourceSlot I) daiNew
      let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
        (frobUrnInkSourceSlot I) urnInkNew
      let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
        (frobUrnArtSourceSlot I) urnArtNew
      let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
        (frobIlkArtSourceSlot I) ilkArtNew
      let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
        (frobIlkRateSourceSlot I) ilkRate
      let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
        (frobIlkSpotSourceSlot I) ilkSpot
      let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
        (frobIlkLineSourceSlot I) ilkLine
      let evmDust := Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
        (frobIlkDustSourceSlot I) ilkDust
      ExecBlock config { contract := contract, locals := localsSafe } evmDebt
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        (.ok
          { contract := contract,
            locals :=
              (localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert
                "daiNew" (.int (Int.ofNat daiNew.toNat)) }
          evmDust) := by
    intro evmGem evmDai evmInk evmArt evmIlk evmRate evmSpot evmLine evmDust
    have hparam :
        localsSafe.get? "i" = some (frobIValue I) ∧
        localsSafe.get? "u" = some (frobUValue I) ∧
        localsSafe.get? "v" = some (frobVValue I) ∧
        localsSafe.get? "w" = some (frobWValue I) ∧
        localsSafe.get? "dink" = some (frobDinkValue I) := by
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
        localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
        using frobConstructedLocalsParamFacts (I := I) urnInk urnArt ilkArt
          ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
    have hcomputed :
        localsSafe.get? "dtab" = some (.int dtab) ∧
        localsSafe.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) ∧
        localsSafe.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) ∧
        localsSafe.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
        localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
        using frobConstructedLocalsComputedFacts (I := I) urnInk urnArt ilkArt
          ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
    have hilks :
        localsSafe.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) ∧
        localsSafe.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) ∧
        localsSafe.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) ∧
        localsSafe.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)) := by
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
        localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
        using frobConstructedLocalsIlkFacts (I := I) urnInk urnArt ilkArt
          ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
    have hbase :
        localsSafe.get? "gem" = none ∧
        localsSafe.get? "dai" = none ∧
        localsSafe.get? "urns" = none ∧
        localsSafe.get? "ilks" = none := by
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
        localsDtab, tab, debtNew, localsDebt, ceilingDebt, inkSpot, localsSafe]
        using frobConstructedLocalsBaseFacts (I := I) urnInk urnArt ilkArt
          ilkRate ilkSpot ilkLine ilkDust dtab debtOld dtabWord
    rcases hparam with ⟨hsafeI, hsafeU, hsafeV, hsafeW, hsafeDink⟩
    rcases hcomputed with
      ⟨hsafeDtab, hsafeUrnInkNew, hsafeUrnArtNew, hsafeIlkArtNew⟩
    rcases hilks with
      ⟨hsafeIlkRate, hsafeIlkSpot, hsafeIlkLine, hsafeIlkDust⟩
    rcases hbase with
      ⟨hsafeBaseGem, hsafeBaseDai, hsafeBaseUrns, hsafeBaseIlks⟩
    exact execFrobFinalStoreTailOk (evm := evmDebt) (I := I) localsSafe
      gemOld gemNew daiOld daiNew dtabWord dtab urnInkNew urnArtNew ilkArtNew
      ilkRate ilkSpot ilkLine ilkDust hsz196
      hsafeI hsafeU hsafeV hsafeW hsafeDink hsafeDtab hsafeUrnInkNew
      hsafeUrnArtNew hsafeIlkArtNew hsafeIlkRate hsafeIlkSpot hsafeIlkLine
      hsafeIlkDust hsafeBaseGem hsafeBaseDai hsafeBaseUrns hsafeBaseIlks
      hloadGem
      hloadDai
      (by
        change frobGemNew σ I =
          UInt256.sub (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I))
            (frobDinkWord I)
        rfl)
      (by
        change frobDaiNew σ I =
          UInt256.mul (frobDartWord I) ilkRate +
            solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)
        rfl)
      hdtabMod
      (frobDinkSubGuardNegCond hGemPosS)
      (frobDinkSubGuardPosCond hGemNegS)
      (signedAddGuardNegCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod hDaiNegS)
      (signedAddGuardPosCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod hDaiPosS)
  have hfull := execBlock_append
    (s2 :=
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
          .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
          .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
          .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
          .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
          .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
          .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simpa only [urnInk, urnArt, ilkArt, ilkRate, ilkSpot, ilkLine, ilkDust, evm0,
      localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, dtab, localsDtab,
      tab, debtOld, dtabWord, debtNew, localsDebt, evmDebt, ceilingDebt, inkSpot,
      localsSafe] using hsourceDust)
    (by simpa only [List.append_assoc] using htail)
  change ExecFuncBody config { contract := contract, locals := frobStore I } evm0
    frobTransition.body
    (.returned { contract := contract, locals := finalLocals } evmDust none)
  exact ExecFuncBody.execBlockOK (by
    simpa [frobTransition, evmDai, evmInk, evmArt, evmIlk, evmRate, evmSpot,
      evmLine, evmDust, finalLocals, List.append_assoc] using hfull)

set_option maxHeartbeats 0 in
theorem vatFrobLiveSuccessFinish
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hsel : selIs I (vatSelBytes 11))
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hret : RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, frobAfterRuntimeFinal σ_evm I) ByteArray.empty)
    (hsourceDust :
      let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
      let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
      let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
      let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
      let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
      let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
      let localsDtab := localsIlk.insert "dtab" (.int dtab)
      let tab := UInt256.mul ilkRate urnArtNew
      let debtOld := vatSlotWord foldDebtSlot σ_solm I
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate
      let debtNew := dtabWord + debtOld
      let localsDebt :=
        (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
          "debtNew" (.int (Int.ofNat debtNew.toNat))
      let evmDebt :=
        Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
          debtNew
      let ceilingDebt := UInt256.mul ilkArtNew ilkRate
      let inkSpot := UInt256.mul urnInkNew ilkSpot
      let localsSafe :=
        (localsDebt.insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ])
        (.ok { contract := contract, locals := localsSafe } evmDebt))
    (hdtabRange :
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I;
      let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I;
      -((2 : Int) ^ 255) ≤ dtab ∧ dtab < (2 : Int) ^ 255)
    (hGemPosS :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobGemNew σ_solm I)
          (solcSlotWord (frobAfterDebt σ_solm I) I (frobGemVSlot I)) = ⟨0⟩)
    (hGemNegS :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobGemNew σ_solm I)
          (solcSlotWord (frobAfterDebt σ_solm I) I (frobGemVSlot I)) = ⟨0⟩)
    (hDaiNegS :
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I;
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate;
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDaiNew σ_solm I)
          (solcSlotWord (frobAfterGem σ_solm I) I (frobDaiWSlot I)) = ⟨0⟩)
    (hDaiPosS :
      let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I;
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate;
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDaiNew σ_solm I)
          (solcSlotWord (frobAfterGem σ_solm I) I (frobDaiWSlot I)) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
  let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
  let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
  let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
  let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
  let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
  let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let tab := UInt256.mul ilkRate urnArtNew
  let debtOld := vatSlotWord foldDebtSlot σ_solm I
  let dtabWord := UInt256.mul (frobDartWord I) ilkRate
  let debtNew := dtabWord + debtOld
  let localsDebt :=
    (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
      "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt :=
    Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
      debtNew
  let ceilingDebt := UInt256.mul ilkArtNew ilkRate
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  let localsSafe :=
    (localsDebt.insert "ceilingDebt"
      (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
      (.int (Int.ofNat inkSpot.toNat))
  let gemOld := solcSlotWord (frobAfterDebt σ_solm I) I (frobGemVSlot I)
  let gemNew := frobGemNew σ_solm I
  let evmGem :=
    Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
      (frobGemVSourceSlot I) gemNew
  let daiOld := solcSlotWord (frobAfterGem σ_solm I) I (frobDaiWSlot I)
  let daiNew := frobDaiNew σ_solm I
  let finalLocals :=
    (localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert
      "daiNew" (.int (Int.ofNat daiNew.toNat))
  let evmDai :=
    Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
      (frobDaiWSourceSlot I) daiNew
  let evmInk :=
    Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
      (frobUrnInkSourceSlot I) urnInkNew
  let evmArt :=
    Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
      (frobUrnArtSourceSlot I) urnArtNew
  let evmIlk :=
    Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
      (frobIlkArtSourceSlot I) ilkArtNew
  let evmRate :=
    Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
      (frobIlkRateSourceSlot I) ilkRate
  let evmSpot :=
    Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
      (frobIlkSpotSourceSlot I) ilkSpot
  let evmLine :=
    Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
      (frobIlkLineSourceSlot I) ilkLine
  let evmDust :=
    Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
      (frobIlkDustSourceSlot I) ilkDust
  have hbody :
      ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
        (.returned { contract := contract, locals := finalLocals } evmDust none) := by
    exact vatFrobSourceBodySuccessFromDustBlock
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hsz196
      hsourceDust hdtabRange hGemPosS hGemNegS hDaiNegS hDaiPosS
  have hcreated :
      (cA, frobAfterRuntimeFinal σ_evm I).1 = evmDust.createdAccounts := by
    change (cA, frobAfterRuntimeFinal σ_solm I).1 = evmDust.createdAccounts
    change
      (cA, frobAfterRuntimeFinal σ_solm I).1 =
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmDebt := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
          foldDebtSlot (frobDebtNew σ_solm I)
         let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
          (frobGemVSourceSlot I) (frobGemNew σ_solm I)
         let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
          (frobDaiWSourceSlot I) (frobDaiNew σ_solm I)
         let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
          (frobUrnInkSourceSlot I) (frobUrnInkNew σ_solm I)
         let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
          (frobUrnArtSourceSlot I) (frobUrnArtNew σ_solm I)
         let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
          (frobIlkArtSourceSlot I) (frobIlkArtNew σ_solm I)
         let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
          (frobIlkRateSourceSlot I) (solcSlotWord σ_solm I (frobIlkRateSlot I))
         let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
          (frobIlkSpotSourceSlot I) (solcSlotWord σ_solm I (frobIlkSpotSlot I))
         let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
          (frobIlkLineSourceSlot I) (solcSlotWord σ_solm I (frobIlkLineSlot I))
         Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
          (frobIlkDustSourceSlot I) (solcSlotWord σ_solm I (frobIlkDustSlot I))).createdAccounts
    exact frobSourceFinal_createdAccounts
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g)
      (frobUrnInkNew σ_solm I) (frobUrnArtNew σ_solm I)
      (frobIlkArtNew σ_solm I) (frobGemNew σ_solm I)
      (frobDaiNew σ_solm I)
  have hsourceAccounts :
      accountMapEquiv (frobAfterRuntimeFinal σ_solm I) evmDust.accountMap := by
    change
      accountMapEquiv (frobAfterRuntimeFinal σ_solm I)
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmDebt := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
          foldDebtSlot (frobDebtNew σ_solm I)
         let evmGem := Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
          (frobGemVSourceSlot I) (frobGemNew σ_solm I)
         let evmDai := Solm.EVM.storageStore evmGem evmGem.executionEnv.codeOwner
          (frobDaiWSourceSlot I) (frobDaiNew σ_solm I)
         let evmInk := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner
          (frobUrnInkSourceSlot I) (frobUrnInkNew σ_solm I)
         let evmArt := Solm.EVM.storageStore evmInk evmInk.executionEnv.codeOwner
          (frobUrnArtSourceSlot I) (frobUrnArtNew σ_solm I)
         let evmIlk := Solm.EVM.storageStore evmArt evmArt.executionEnv.codeOwner
          (frobIlkArtSourceSlot I) (frobIlkArtNew σ_solm I)
         let evmRate := Solm.EVM.storageStore evmIlk evmIlk.executionEnv.codeOwner
          (frobIlkRateSourceSlot I) (solcSlotWord σ_solm I (frobIlkRateSlot I))
         let evmSpot := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner
          (frobIlkSpotSourceSlot I) (solcSlotWord σ_solm I (frobIlkSpotSlot I))
         let evmLine := Solm.EVM.storageStore evmSpot evmSpot.executionEnv.codeOwner
          (frobIlkLineSourceSlot I) (solcSlotWord σ_solm I (frobIlkLineSlot I))
         Solm.EVM.storageStore evmLine evmLine.executionEnv.codeOwner
          (frobIlkDustSourceSlot I) (solcSlotWord σ_solm I (frobIlkDustSlot I))).accountMap
    exact accountMapEquiv_frobSourceFinal
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hsz196
      (frobUrnInkNew σ_solm I) (frobUrnArtNew σ_solm I)
      (frobIlkArtNew σ_solm I) (frobGemNew σ_solm I)
      (frobDaiNew σ_solm I) rfl rfl rfl rfl rfl
  exact vatFrobSuccessEquivFromFinalState hcode (vatDispatchFrob hsel) hdecode hret
    hbody hcreated ((accountMapEquiv_frobAfterRuntimeFinal hAccounts).trans hsourceAccounts)

set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveSuccessGuards
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hSuccess : frobLiveSuccessGuards σ_evm I)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, hafterLive⟩ := vatFrobLiveOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := vatSelWord I) hlive hdecoded
  by_cases hrateZeroEvm : solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩
  · let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
    let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
    let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
    let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
    let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
    let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
    let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
    have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
      rw [← hliveWord]
      exact hlive
    have hrateWord :
        vatSlotWord (frobIlkRateSlot I) σ_solm I = ⟨0⟩ := by
      have heq :
          vatSlotWord (frobIlkRateSlot I) σ_evm I =
            vatSlotWord (frobIlkRateSlot I) σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner
          (frobIlkRateSlot I) ⟨0⟩
      rw [← heq]
      simpa [vatSlotWord] using hrateZeroEvm
    have hbodyRaw :
        let locals := frobStore I
        let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        ExecTransitionBody config contract evm0' locals frobTransition.body
          .reverted := by
      exact vatFrobSourceBodyRateZero
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g)
          (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
          (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
          (ilkDust := ilkDust)
          hwv hsz196 hliveSolm
          (by simpa [urnInk] using
            (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [urnArt] using
            (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkArt] using
            (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkRate] using
            (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkSpot] using
            (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkLine] using
            (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkDust] using
            (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by
            rw [show ilkRate = vatSlotWord (frobIlkRateSlot I) σ_solm I from rfl,
              hrateWord]
            native_decide)
    have hbody :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      simpa [evm0] using hbodyRaw
    obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
    have hrev := RD.vatFrobIlkLoadsRateZero hafterUrn hrateZeroEvm
    exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode hbody
  · let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
    let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
    let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
    let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
    let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
    let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
    let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
    have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
      rw [← hliveWord]
      exact hlive
    have hrateWordNe :
        vatSlotWord (frobIlkRateSlot I) σ_solm I ≠ ⟨0⟩ := by
      intro hzeroSolm
      apply hrateZeroEvm
      have heq :
          vatSlotWord (frobIlkRateSlot I) σ_evm I =
            vatSlotWord (frobIlkRateSlot I) σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner
          (frobIlkRateSlot I) ⟨0⟩
      simpa [vatSlotWord, hzeroSolm] using heq.trans hzeroSolm
    have hratePos : 0 < ilkRate.toNat := by
      have hnat : ilkRate.toNat ≠ 0 := by
        intro hzeroNat
        apply hrateWordNe
        apply u256_inj
        simpa [ilkRate, hzeroNat]
      exact Nat.pos_of_ne_zero hnat
    have hsourcePrefixRaw :
        let locals := frobStore I
        let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        ExecBlock config { contract := contract, locals := locals } evm0'
          (nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
          (.ok
            { contract := contract,
              locals :=
                frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
            evm0') := by
      exact vatFrobSourceRateNonzeroPrefix
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g)
          (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
          (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
          (ilkDust := ilkDust)
          hwv hsz196 hliveSolm
          (by simpa [urnInk] using
            (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [urnArt] using
            (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkArt] using
            (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkRate] using
            (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkSpot] using
            (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkLine] using
            (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          (by simpa [ilkDust] using
            (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
          hratePos
    have hsourcePrefix :
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          (nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
          (.ok
            { contract := contract,
              locals :=
                frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
            evm0) := by
      simpa [evm0] using hsourcePrefixRaw
    obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
    obtain ⟨_, _, hafterRateNonzero⟩ :=
      RD.vatFrobIlkLoadsRateNonzero hafterUrn hrateZeroEvm
    have hthreeAddsEvm :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        ∃ k' C',
          RD vatBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3306⟩
            [frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I),
              ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
              frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
              frobIWord I, ⟨524⟩, vatSelWord I]
            (frobUrnArtUpdatedMem σ_evm I
              (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (UInt256.ofNat 18) ByteArray.empty (cA, σ_evm) k' C' := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
      obtain ⟨_, _, hInk⟩ :=
        RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
      obtain ⟨_, _, hArt⟩ :=
        RD.vatFrobUrnArtAddSuccess (h := by simpa using hInk) hArtNeg hArtPos
      obtain ⟨_, _, hIlk⟩ :=
        RD.vatFrobIlkArtAddSuccess (h := by simpa using hArt) hIlkNeg hIlkPos
      exact ⟨_, _, by simpa using hIlk⟩
    have hthroughDtabEvm :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ∃ k' C',
          RD vatBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3329⟩
            [UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)),
              ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
              frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
              frobIWord I, ⟨524⟩, vatSelWord I]
            (frobIlkArtUpdatedMem σ_evm I
              (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)))
            (UInt256.ofNat 18) ByteArray.empty (cA, σ_evm) k' C' := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
      obtain ⟨_, _, hIlk⟩ :=
        hthreeAddsEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
      obtain ⟨_, _, hDtab⟩ :=
        RD.vatFrobDtabMulSuccess (h := by simpa using hIlk) hRateMax hDtabMul
      exact ⟨_, _, by simpa using hDtab⟩
    have hthroughTabEvm :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ∃ k' C',
          RD vatBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3351⟩
            [UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)),
              UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)),
              ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
              frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
              frobIWord I, ⟨524⟩, vatSelWord I]
            (frobIlkArtUpdatedMem σ_evm I
              (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)))
            (UInt256.ofNat 18) ByteArray.empty (cA, σ_evm) k' C' := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul
      obtain ⟨_, _, hDtab⟩ :=
        hthroughDtabEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hRateMax hDtabMul
      obtain ⟨_, _, hTab⟩ :=
        RD.vatFrobTabMulSuccess
          (h := by simpa using hDtab)
          (urnArtNew := frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
          (ilkArtNew := frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
          (dtabWord :=
            UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I)))
          (by simpa using hTabMul)
      exact ⟨_, _, by simpa using hTab⟩
    have hUrnInkEq :
        solcSlotWord σ_evm I (frobUrnInkSlot I) =
          solcSlotWord σ_solm I (frobUrnInkSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnInkSlot I) ⟨0⟩
    have hUrnArtEq :
        solcSlotWord σ_evm I (frobUrnArtSlot I) =
          solcSlotWord σ_solm I (frobUrnArtSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnArtSlot I) ⟨0⟩
    have hIlkArtEq :
        solcSlotWord σ_evm I (frobIlkArtSlot I) =
          solcSlotWord σ_solm I (frobIlkArtSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkArtSlot I) ⟨0⟩
    have hIlkRateEq :
        solcSlotWord σ_evm I (frobIlkRateSlot I) =
          solcSlotWord σ_solm I (frobIlkRateSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkRateSlot I) ⟨0⟩
    let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
    have hthreeAddsSource :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        let localsLoaded :=
          frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        let urnInkNew := frobDinkWord I + urnInk
        let urnArtNew := frobDartWord I + urnArt
        let ilkArtNew := frobDartWord I + ilkArt
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          ((nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
            checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
            checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
            checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
          (.ok
            { contract := contract,
              locals :=
                (((localsLoaded.insert "urnInkNew"
                    (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
                  (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
                  (.int (Int.ofNat ilkArtNew.toNat))) }
            evm0) := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
      exact
        execFrobLoadedPrefixThreeAdds
          (evm := evm0) (I := I)
          urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
          hsourcePrefix
          (frobDinkAddGuardNegCond (by
            simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg))
          (frobDinkAddGuardPosCond (by
            simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos))
          (frobDartAddGuardNegCond (by
            simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg))
          (frobDartAddGuardPosCond (by
            simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtPos))
          (frobDartAddGuardNegCond (by
            simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkNeg))
          (frobDartAddGuardPosCond (by
            simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkPos))
    have hthroughDtabSource :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        -((2 : Int) ^ 255) ≤ dtab →
        dtab < (2 : Int) ^ 255 →
        evalExpr? config
          { contract := contract,
            locals :=
              ((((frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
                  ilkDust).insert "urnInkNew"
                  (.int (Int.ofNat (frobDinkWord I + urnInk).toNat))).insert
                "urnArtNew" (.int (Int.ofNat (frobDartWord I + urnArt).toNat))).insert
                "ilkArtNew" (.int (Int.ofNat (frobDartWord I + ilkArt).toNat))).insert
                "dtab" (.int dtab) } evm0
          (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
          .ok (.bool true) →
        evalExpr? config
          { contract := contract,
            locals :=
              ((((frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
                  ilkDust).insert "urnInkNew"
                  (.int (Int.ofNat (frobDinkWord I + urnInk).toNat))).insert
                "urnArtNew" (.int (Int.ofNat (frobDartWord I + urnArt).toNat))).insert
                "ilkArtNew" (.int (Int.ofNat (frobDartWord I + ilkArt).toNat))).insert
                "dtab" (.int dtab) } evm0
          (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
            (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
              (.var "ilkRate"))) =
          .ok (.bool true) →
        let localsLoaded :=
          frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        let urnInkNew := frobDinkWord I + urnInk
        let urnArtNew := frobDartWord I + urnArt
        let ilkArtNew := frobDartWord I + ilkArt
        let localsIlk :=
          (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
              "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat)))
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          ((nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
            checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
            checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
            checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
            checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
          (.ok
            { contract := contract,
              locals := localsIlk.insert "dtab" (.int dtab) }
            evm0) := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtabLo hdtabHi
        hguardMax hguardMul
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      have hsourceAdds :=
        hthreeAddsSource hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
      have hdtabBlock :
          ExecBlock config { contract := contract, locals := localsIlk } evm0
            (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
            (.ok
              { contract := contract,
                locals := localsIlk.insert "dtab" (.int dtab) }
              evm0) := by
        exact execFrobDtabMulCheckedOk
          (evm := evm0) (I := I) localsIlk ilkRate dtab
          (by
            change (((localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
              (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
              (.int (Int.ofNat ilkArtNew.toNat))).get? "ilkRate" =
              some (.int (Int.ofNat ilkRate.toNat))
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            simpa [localsLoaded] using
              frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot
                ilkLine ilkDust)
          (by
            change (((localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
              (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
              (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" =
              some (frobDartValue I)
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            simpa [localsLoaded] using
              frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot
                ilkLine ilkDust)
          (by rfl)
          hdtabLo hdtabHi
          (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk]
            using hguardMax)
          (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk]
            using hguardMul)
      have h04 := execBlock_append
        (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk]
          using hsourceAdds)
        hdtabBlock
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
        List.append_assoc] using h04
    have hDtabSourceGuards :
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        let localsLoaded :=
          frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        let urnInkNew := frobDinkWord I + urnInk
        let urnArtNew := frobDartWord I + urnArt
        let ilkArtNew := frobDartWord I + ilkArt
        let localsIlk :=
          (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
              "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat)))
        evalExpr? config
          { contract := contract, locals := localsIlk.insert "dtab" (.int dtab) }
          evm0 (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
          .ok (.bool true) ∧
        evalExpr? config
          { contract := contract, locals := localsIlk.insert "dtab" (.int dtab) }
          evm0
          (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
            (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
              (.var "ilkRate"))) =
          .ok (.bool true) := by
      intro hRateMax
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      have hrateGet :
          localsIlk.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
        change (((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust
      have hdartGet :
          localsIlk.get? "dart" = some (frobDartValue I) := by
        change (((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" =
          some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust
      have hRateMaxS : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩ := by
        simpa [ilkRate, vatSlotWord, hIlkRateEq] using hRateMax
      have hrateEval :
          evalExpr? config
            { contract := contract, locals := localsIlk.insert "dtab" (.int dtab) }
            evm0 (.var "ilkRate") =
          .ok (.int (Int.ofNat ilkRate.toNat)) := by
        have hget :
            (localsIlk.insert "dtab" (.int dtab)).get? "ilkRate" =
              some (.int (Int.ofNat ilkRate.toNat)) := by
          rw [store_get_ne _ _ (by decide)]
          exact hrateGet
        exact vatEvalExpr_varUInt256 hget
      have hMaxLit :
          evalExpr? config
            { contract := contract, locals := localsIlk.insert "dtab" (.int dtab) }
            evm0 (.intLit maxInt256) = .ok (.int maxInt256) := by
        simp [evalExpr?, pure]
      have hguardMax :
          evalExpr? config
            { contract := contract, locals := localsIlk.insert "dtab" (.int dtab) }
            evm0 (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
          .ok (.bool true) :=
        vatEvalExpr_le_int_true hrateEval hMaxLit
          (uintWordLeMaxInt256_of_slt_zero hRateMaxS)
      have hguardMul :
          evalExpr? config
            { contract := contract, locals := localsIlk.insert "dtab" (.int dtab) }
            evm0
            (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
              (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
                (.var "ilkRate"))) =
          .ok (.bool true) := by
        by_cases hwordZero : frobDartWord I = ⟨0⟩
        · exact
            evalExpr_frob_dtab_mul_guard_dart_zero_true
              (evm := evm0) (locals := localsIlk) I hdartGet
              (frobDartInt_zero_of_word_zero I hwordZero)
        · have hdartNe : frobDartInt I ≠ 0 :=
            frobDartInt_ne_zero_of_word_ne I hwordZero
          have hdiv : dtab / frobDartInt I = Int.ofNat ilkRate.toNat := by
            change
              (Int.ofNat ilkRate.toNat * frobDartInt I) / frobDartInt I =
                Int.ofNat ilkRate.toNat
            exact Int.mul_ediv_cancel (Int.ofNat ilkRate.toNat) hdartNe
          exact
            evalExpr_frob_dtab_mul_guard_exact_true
              (evm := evm0) (locals := localsIlk) (rate := ilkRate) I hdartGet
              hrateGet hdartNe hdiv
      exact ⟨hguardMax, hguardMul⟩
    have hDtabRangeOfGuards :
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        -((2 : Int) ^ 255) ≤ dtab ∧ dtab < (2 : Int) ^ 255 := by
      intro hRateMax hDtabMul
      have hRateMaxS : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩ := by
        simpa [ilkRate, vatSlotWord, hIlkRateEq] using hRateMax
      have hRateLowS : ilkRate.toNat < EVM.twoPow 255 :=
        u256_toNat_lt_sign_of_slt_zero hRateMaxS
      have hMulGuardEqS :
          frobDartWord I = ⟨0⟩ ∨
            UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
              (frobDartWord I) = ilkRate := by
        cases hDtabMul with
        | inl hzero => exact Or.inl hzero
        | inr hne =>
            exact Or.inr (u256_eq_ne_zero_to_eq (by
              simpa [ilkRate, vatSlotWord, hIlkRateEq] using hne))
      change
        -((2 : Int) ^ 255) ≤ Int.ofNat ilkRate.toNat * frobDartInt I ∧
          Int.ofNat ilkRate.toNat * frobDartInt I < (2 : Int) ^ 255
      exact frob_dtab_product_range_of_guard I hRateLowS hMulGuardEqS
    have hthroughTabSource :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        let localsLoaded :=
          frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        let urnInkNew := frobDinkWord I + urnInk
        let urnArtNew := frobDartWord I + urnArt
        let ilkArtNew := frobDartWord I + ilkArt
        let localsIlk :=
          (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
              "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat)))
        let localsDtab := localsIlk.insert "dtab" (.int dtab)
        let tab := UInt256.mul ilkRate urnArtNew
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          ((nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
            checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
            checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
            checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
            checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
            checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
          (.ok
            { contract := contract,
              locals := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat)) }
            evm0) := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      let localsDtab := localsIlk.insert "dtab" (.int dtab)
      let tab := UInt256.mul ilkRate urnArtNew
      have hdtabRange := hDtabRangeOfGuards hRateMax hDtabMul
      have hdtabGuards := hDtabSourceGuards hRateMax
      have hsourceDtab :=
        hthroughDtabSource hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hdtabRange.1 hdtabRange.2 hdtabGuards.1 hdtabGuards.2
      have hTabMulS :
          urnArtNew = ⟨0⟩ ∨
            UInt256.eq (UInt256.div (UInt256.mul ilkRate urnArtNew) urnArtNew)
              ilkRate ≠ ⟨0⟩ := by
        simpa [urnArtNew, urnArt, ilkRate, vatSlotWord, hUrnArtEq, hIlkRateEq]
          using hTabMul
      have htabFitGuard :=
        uintCheckedMulGuard_to_fit_and_source_guard hTabMulS
      have hrateGet :
          localsDtab.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
        change ((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).get?
          "ilkRate" = some (.int (Int.ofNat ilkRate.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
            ilkDust
      have hurnArtNewGet :
          localsDtab.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) := by
        change ((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).get?
          "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self]
      have htabBlock :
          ExecBlock config { contract := contract, locals := localsDtab } evm0
            (checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
            (.ok
              { contract := contract,
                locals := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat)) }
              evm0) := by
        exact execFrobTabMulCheckedOk (evm := evm0) (locals := localsDtab)
          ilkRate urnArtNew tab hrateGet hurnArtNewGet (by rfl)
          htabFitGuard.1 htabFitGuard.2
      have h05 := execBlock_append
        (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
          localsDtab] using hsourceDtab)
        htabBlock
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
        tab, List.append_assoc] using h05
    have hDebtEq :
        solcSlotWord σ_evm I foldDebtSlot =
          solcSlotWord σ_solm I foldDebtSlot :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner foldDebtSlot ⟨0⟩
    have hIlkSpotEq :
        solcSlotWord σ_evm I (frobIlkSpotSlot I) =
          solcSlotWord σ_solm I (frobIlkSpotSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkSpotSlot I) ⟨0⟩
    have hIlkLineEq :
        solcSlotWord σ_evm I (frobIlkLineSlot I) =
          solcSlotWord σ_solm I (frobIlkLineSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkLineSlot I) ⟨0⟩
    have hIlkDustEq :
        solcSlotWord σ_evm I (frobIlkDustSlot I) =
          solcSlotWord σ_solm I (frobIlkDustSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkDustSlot I) ⟨0⟩
    have hLineEq :
        solcSlotWord σ_evm I ⟨9⟩ =
          solcSlotWord σ_solm I ⟨9⟩ :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨9⟩ ⟨0⟩
    have hthroughDebtEvm :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        (UInt256.slt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (UInt256.sgt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        ∃ k' C',
          RD vatBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3369⟩
            [UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)),
              UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)),
              ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
              frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
              frobIWord I, ⟨524⟩, vatSelWord I]
            (frobIlkArtUpdatedMem σ_evm I
              (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)))
            (UInt256.ofNat 18) ByteArray.empty
            (cA, sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)) k' C' := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul hDebtNeg hDebtPos
      obtain ⟨_, _, hTab⟩ :=
        hthroughTabEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hRateMax hDtabMul hTabMul
      obtain ⟨_, _, hDebt⟩ :=
        RD.vatFrobDebtAddStoreSuccess
          (h := by simpa using hTab)
          (hperm := hperm)
          (by simpa using hDebtNeg)
          (by simpa using hDebtPos)
      exact ⟨_, _, by simpa [foldDebtSlot] using hDebt⟩
    have hthroughDebtSource :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        (UInt256.slt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (UInt256.sgt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        let localsLoaded :=
          frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        let urnInkNew := frobDinkWord I + urnInk
        let urnArtNew := frobDartWord I + urnArt
        let ilkArtNew := frobDartWord I + ilkArt
        let localsIlk :=
          (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
              "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat)))
        let localsDtab := localsIlk.insert "dtab" (.int dtab)
        let tab := UInt256.mul ilkRate urnArtNew
        let debtOld := vatSlotWord foldDebtSlot σ_solm I
        let dtabWord := UInt256.mul (frobDartWord I) ilkRate
        let debtNew := dtabWord + debtOld
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          ((nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
            checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
            checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
            checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
            checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
            checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
            checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
            [ .assign .storage debtRef (.var "debtNew") ])
          (.ok
            { contract := contract,
              locals :=
                (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
                  "debtNew" (.int (Int.ofNat debtNew.toNat)) }
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
              debtNew)) := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul hDebtNeg hDebtPos
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      let localsDtab := localsIlk.insert "dtab" (.int dtab)
      let tab := UInt256.mul ilkRate urnArtNew
      let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
      let debtOld := vatSlotWord foldDebtSlot σ_solm I
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate
      let debtNew := dtabWord + debtOld
      have hsourceTab :=
        hthroughTabSource hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hRateMax hDtabMul hTabMul
      have hDebtNegS :
          UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
            UInt256.gt debtNew debtOld = ⟨0⟩ := by
        simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
          hDebtEq] using hDebtNeg
      have hDebtPosS :
          UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt debtNew debtOld = ⟨0⟩ := by
        simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
          hDebtEq] using hDebtPos
      have hdtabRange := hDtabRangeOfGuards hRateMax hDtabMul
      have hdtabMod :
          dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat := by
        change
          (Int.ofNat ilkRate.toNat * frobDartInt I) %
              (Int.ofNat EVM.wordModulus) =
            Int.ofNat (UInt256.mul (frobDartWord I) ilkRate).toNat
        exact frobDtab_mod_word I ilkRate
      have hdebtLoad :
          Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner foldDebtSlot =
            debtOld := by
        simpa [evm0, debtOld, vatSlotWord, solcSlotWord,
          codeOwnerStorageWord] using
          (codeOwnerStorageWord_initState
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) foldDebtSlot)
      have hdebtBlock :
          ExecBlock config { contract := contract, locals := localsTab } evm0
            (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
              [ .assign .storage debtRef (.var "debtNew") ])
            (.ok
              { contract := contract,
                locals :=
                  localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat)) }
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                foldDebtSlot debtNew)) := by
        exact execFrobDebtAddStoreOk
          (evm := evm0) (locals := localsTab)
          debtOld debtNew dtabWord dtab
          (by
            change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get?
              "debt" = none
            rw [store_get_ne _ _ (by decide)]
            change (localsIlk.insert "dtab" (.int dtab)).get? "debt" = none
            rw [store_get_ne _ _ (by decide)]
            change (((localsLoaded.insert "urnInkNew"
              (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
              (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
              (.int (Int.ofNat ilkArtNew.toNat))).get? "debt" = none
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            simp [localsLoaded, frobStoreIlkDust, frobStore])
          (by
            change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get?
              "dtab" = some (.int dtab)
            rw [store_get_ne _ _ (by decide)]
            simp [localsDtab])
          hdebtLoad hdtabMod (by rfl)
          (signedAddGuardNegCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod
            hDebtNegS)
          (signedAddGuardPosCond_of_word hdtabRange.1 hdtabRange.2 hdtabMod
            hDebtPosS)
      have h06 := execBlock_append
        (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
          localsDtab, tab, localsTab] using hsourceTab)
        hdebtBlock
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
        tab, localsTab, debtOld, dtabWord, debtNew, List.append_assoc] using h06
    have hthroughSafetySource :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        (UInt256.slt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (UInt256.sgt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (solcSlotWord σ_evm I (frobIlkRateSlot I)))
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.land
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)
                (solcSlotWord σ_evm I ⟨9⟩)))
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul
                  (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)))
                (solcSlotWord σ_evm I (frobIlkLineSlot I)))))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        (((sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) =
          UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot) →
        (solcSlotWord σ_evm I (frobIlkSpotSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
              (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.isZero
            (UInt256.gt
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ →
        let localsLoaded :=
          frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        let urnInkNew := frobDinkWord I + urnInk
        let urnArtNew := frobDartWord I + urnArt
        let ilkArtNew := frobDartWord I + ilkArt
        let localsIlk :=
          (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
              "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat)))
        let localsDtab := localsIlk.insert "dtab" (.int dtab)
        let tab := UInt256.mul ilkRate urnArtNew
        let debtOld := vatSlotWord foldDebtSlot σ_solm I
        let dtabWord := UInt256.mul (frobDartWord I) ilkRate
        let debtNew := dtabWord + debtOld
        let localsDebt :=
          (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
            "debtNew" (.int (Int.ofNat debtNew.toNat))
        let evmDebt :=
          Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
            debtNew
        let ceilingDebt := UInt256.mul ilkArtNew ilkRate
        let inkSpot := UInt256.mul urnInkNew ilkSpot
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          ((nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
            checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
            checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
            checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
            checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
            checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
            checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
            [ .assign .storage debtRef (.var "debtNew") ] ++
            checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
            checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
            [ .require
                (eitherExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (bothExpr
                    (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                    (.binary .le (.var "debtNew") (.storage LineRef)))),
              .require
                (eitherExpr
                  (bothExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (.binary .ge (.var "dink") (.intLit 0)))
                  (.binary .le (.var "tab") (.var "inkSpot"))) ])
          (.ok
            { contract := contract,
              locals :=
                (localsDebt.insert "ceilingDebt"
                  (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
                  (.int (Int.ofNat inkSpot.toNat)) }
            evmDebt) := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk _hDebtLoadStore hInkMul
        hSafetyOk
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      let localsDtab := localsIlk.insert "dtab" (.int dtab)
      let tab := UInt256.mul ilkRate urnArtNew
      let localsDebt :=
        ((localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat
            (UInt256.mul (frobDartWord I) ilkRate +
              vatSlotWord foldDebtSlot σ_solm I).toNat)))
      let debtOld := vatSlotWord foldDebtSlot σ_solm I
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate
      let debtNew := dtabWord + debtOld
      let evmDebt :=
        Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
      let ceilingDebt := UInt256.mul ilkArtNew ilkRate
      let inkSpot := UInt256.mul urnInkNew ilkSpot
      have hsourceDebt :=
        hthroughDebtSource hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hRateMax hDtabMul hTabMul hDebtNeg hDebtPos
      have hCeilingMulS :
          ilkRate = ⟨0⟩ ∨
            UInt256.eq (UInt256.div (UInt256.mul ilkArtNew ilkRate) ilkRate)
              ilkArtNew ≠ ⟨0⟩ := by
        simpa [ilkArtNew, ilkArt, ilkRate, vatSlotWord, hIlkArtEq, hIlkRateEq]
          using hCeilingMul
      have hceilingFitGuard :=
        uintCheckedMulGuard_to_fit_and_source_guard hCeilingMulS
      have hInkMulS :
          ilkSpot = ⟨0⟩ ∨
            UInt256.eq (UInt256.div (UInt256.mul urnInkNew ilkSpot) ilkSpot)
              urnInkNew ≠ ⟨0⟩ := by
        simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq, hIlkSpotEq]
          using hInkMul
      have hinkFitGuard := uintCheckedMulGuard_to_fit_and_source_guard hInkMulS
      have hCeilingOkS :
          UInt256.lor
            (UInt256.land
              (UInt256.isZero
                (UInt256.gt debtNew (vatSlotWord ⟨9⟩ σ_solm I)))
              (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ := by
        simpa [ceilingDebt, debtNew, dtabWord, debtOld, ilkArtNew, ilkArt,
          ilkRate, ilkLine, vatSlotWord, hIlkArtEq, hIlkRateEq, hIlkLineEq,
          hDebtEq, hLineEq] using hCeilingOk
      have hSafetyOkS :
          UInt256.lor
            (UInt256.isZero (UInt256.gt tab inkSpot))
            (UInt256.land
              (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
              (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ := by
        simpa [tab, inkSpot, urnInkNew, urnInk, urnArtNew, urnArt, ilkRate,
          ilkSpot, vatSlotWord, hUrnInkEq, hUrnArtEq, hIlkRateEq, hIlkSpotEq]
          using hSafetyOk
      have hlineLoad :
          Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner ⟨9⟩ =
            vatSlotWord ⟨9⟩ σ_solm I := by
        have hne : (⟨9⟩ : UInt256) ≠ foldDebtSlot := by
          simp [foldDebtSlot]
        have hload0 :
            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ =
              vatSlotWord ⟨9⟩ σ_solm I := by
          simpa [evm0, initState, vatSlotWord, solcSlotWord,
            codeOwnerStorageWord] using
            (codeOwnerStorageWord_initState
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) ⟨9⟩)
        have hstore :
            Solm.EVM.storageLoad
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
                  debtNew)
                evm0.executionEnv.codeOwner ⟨9⟩ =
              Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ :=
          storageLoad_storageStore_ne evm0 evm0.executionEnv.codeOwner hne
        simpa [evmDebt, storageStore_executionEnv] using hstore.trans hload0
      have hlocalsDebtIlkArtNew :
          localsDebt.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "ilkArtNew" =
              some (.int (Int.ofNat ilkArtNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self]
      have hlocalsDebtRate :
          localsDebt.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "ilkRate" =
              some (.int (Int.ofNat ilkRate.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtUrnInkNew :
          localsDebt.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "urnInkNew" =
              some (.int (Int.ofNat urnInkNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self]
      have hlocalsDebtSpot :
          localsDebt.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "ilkSpot" =
              some (.int (Int.ofNat ilkSpot.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_spot I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtDart :
          localsDebt.get? "dart" = some (frobDartValue I) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "dart" =
              some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtDink :
          localsDebt.get? "dink" = some (frobDinkValue I) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "dink" =
              some (frobDinkValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtLine :
          localsDebt.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "ilkLine" =
              some (.int (Int.ofNat ilkLine.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_line I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtDebtNew :
          localsDebt.get? "debtNew" = some (.int (Int.ofNat debtNew.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "debtNew" =
              some (.int (Int.ofNat debtNew.toNat))
        rw [store_get_self]
      have hlocalsDebtTab :
          localsDebt.get? "tab" = some (.int (Int.ofNat tab.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "tab" =
              some (.int (Int.ofNat tab.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self]
      have hlocalsDebtLineBase :
          localsDebt.get? "Line" = none := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "Line" = none
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simp [localsLoaded, frobStoreIlkDust, frobStore]
      have hsafeBlock :
          ExecBlock config { contract := contract, locals := localsDebt } evmDebt
            (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
              checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
              [ .require
                  (eitherExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (bothExpr
                      (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                      (.binary .le (.var "debtNew") (.storage LineRef)))),
                .require
                  (eitherExpr
                    (bothExpr
                      (.binary .le (.var "dart") (.intLit 0))
                      (.binary .ge (.var "dink") (.intLit 0)))
                    (.binary .le (.var "tab") (.var "inkSpot"))) ])
            (.ok
              { contract := contract,
                locals :=
                  (localsDebt.insert "ceilingDebt"
                    (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
                    (.int (Int.ofNat inkSpot.toNat)) }
              evmDebt) := by
        exact execFrobCeilingSafetyOk
          (evm := evmDebt) (locals := localsDebt)
          ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot
          hlocalsDebtIlkArtNew hlocalsDebtRate hlocalsDebtUrnInkNew
          hlocalsDebtSpot
          (by rfl) hceilingFitGuard.1 hceilingFitGuard.2
          (by rfl) hinkFitGuard.1 hinkFitGuard.2
          (evalExpr_frob_ceiling_req_true
            (evm := evmDebt) (I := I)
            (ceilingDebt := ceilingDebt) (ilkLine := ilkLine)
            (debtNew := debtNew) (Line := vatSlotWord ⟨9⟩ σ_solm I)
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_ne _ _ (by decide)]
              exact hlocalsDebtDart)
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_self])
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_ne _ _ (by decide)]
              exact hlocalsDebtLine)
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_ne _ _ (by decide)]
              exact hlocalsDebtDebtNew)
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_ne _ _ (by decide)]
              exact hlocalsDebtLineBase)
            hlineLoad
            (frobCeilingSourceCond_of_evm (I := I) hCeilingOkS))
          (evalExpr_frob_safety_req_true
            (evm := evmDebt) (I := I) (tab := tab) (inkSpot := inkSpot)
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_ne _ _ (by decide)]
              exact hlocalsDebtDart)
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_ne _ _ (by decide)]
              exact hlocalsDebtDink)
            (by
              rw [store_get_ne _ _ (by decide)]
              rw [store_get_ne _ _ (by decide)]
              exact hlocalsDebtTab)
            (by
              rw [store_get_self])
            (frobSafetySourceCond_of_evm (I := I) hSafetyOkS))
      have h07 := execBlock_append
        (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
          localsDtab, tab, localsDebt, debtOld, dtabWord, debtNew, evmDebt]
          using hsourceDebt)
        hsafeBlock
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
        tab, localsDebt, debtOld, dtabWord, debtNew, evmDebt, ceilingDebt, inkSpot,
        List.append_assoc] using h07
    have hthroughDustSource :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        (UInt256.slt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (UInt256.sgt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (solcSlotWord σ_evm I (frobIlkRateSlot I)))
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.land
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)
                (solcSlotWord σ_evm I ⟨9⟩)))
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul
                  (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)))
                (solcSlotWord σ_evm I (frobIlkLineSlot I)))))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        (((sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) =
          UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot) →
        (solcSlotWord σ_evm I (frobIlkSpotSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
              (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.isZero
            (UInt256.gt
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobUWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobVWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
          (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobWWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
          (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.isZero
            (UInt256.lt
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (solcSlotWord σ_evm I (frobIlkDustSlot I))))
          (UInt256.eq ⟨0⟩
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))) ≠ ⟨0⟩ →
        let localsLoaded :=
          frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        let urnInkNew := frobDinkWord I + urnInk
        let urnArtNew := frobDartWord I + urnArt
        let ilkArtNew := frobDartWord I + ilkArt
        let localsIlk :=
          (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
              "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat)))
        let localsDtab := localsIlk.insert "dtab" (.int dtab)
        let tab := UInt256.mul ilkRate urnArtNew
        let debtOld := vatSlotWord foldDebtSlot σ_solm I
        let dtabWord := UInt256.mul (frobDartWord I) ilkRate
        let debtNew := dtabWord + debtOld
        let localsDebt :=
          (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
            "debtNew" (.int (Int.ofNat debtNew.toNat))
        let evmDebt :=
          Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
            debtNew
        let ceilingDebt := UInt256.mul ilkArtNew ilkRate
        let inkSpot := UInt256.mul urnInkNew ilkSpot
        let localsSafe :=
          (localsDebt.insert "ceilingDebt"
            (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
            (.int (Int.ofNat inkSpot.toNat))
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          ((nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
            checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
            checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
            checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
            checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
            checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
            checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
            [ .assign .storage debtRef (.var "debtNew") ] ++
            checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
            checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
            [ .require
                (eitherExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (bothExpr
                    (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                    (.binary .le (.var "debtNew") (.storage LineRef)))),
              .require
                (eitherExpr
                  (bothExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (.binary .ge (.var "dink") (.intLit 0)))
                  (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
            [ .require
                (eitherExpr
                  (bothExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (.binary .ge (.var "dink") (.intLit 0)))
                  (wishExpr (.var "u") sender)),
              .require
                (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                  (wishExpr (.var "v") sender)),
              .require
                (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                  (wishExpr (.var "w") sender)),
              .require
                (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                  (.binary .ge (.var "tab") (.var "ilkDust"))) ])
          (.ok { contract := contract, locals := localsSafe } evmDebt) := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk hDebtLoadStore hInkMul
        hSafetyOk hU hV hW hDust
      let localsLoaded :=
        frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
      let urnInkNew := frobDinkWord I + urnInk
      let urnArtNew := frobDartWord I + urnArt
      let ilkArtNew := frobDartWord I + ilkArt
      let localsIlk :=
        (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
            "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat)))
      let localsDtab := localsIlk.insert "dtab" (.int dtab)
      let tab := UInt256.mul ilkRate urnArtNew
      let localsDebt :=
        ((localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat
            (UInt256.mul (frobDartWord I) ilkRate +
              vatSlotWord foldDebtSlot σ_solm I).toNat)))
      let debtOld := vatSlotWord foldDebtSlot σ_solm I
      let dtabWord := UInt256.mul (frobDartWord I) ilkRate
      let debtNew := dtabWord + debtOld
      let evmDebt :=
        Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
      let ceilingDebt := UInt256.mul ilkArtNew ilkRate
      let inkSpot := UInt256.mul urnInkNew ilkSpot
      let localsSafe :=
        (localsDebt.insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))
      let uWish := vatSlotWord (frobUWishSlot I)
        (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
      let vWish := vatSlotWord (frobVWishSlot I)
        (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
      let wWish := vatSlotWord (frobWWishSlot I)
        (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
      have hsourceSafe :=
        hthroughSafetySource hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hRateMax hDtabMul hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk
          hDebtLoadStore hInkMul hSafetyOk
      have hUWishEq :
          vatSlotWord (frobUWishSlot I)
            (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)) I = uWish := by
        simpa [uWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord,
          hIlkRateEq, hDebtEq] using
          (vatSlotWord_debtStore_accountMapEquiv
            (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
            (frobUWishSlot I) debtNew)
      have hVWishEq :
          vatSlotWord (frobVWishSlot I)
            (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)) I = vWish := by
        simpa [vWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord,
          hIlkRateEq, hDebtEq] using
          (vatSlotWord_debtStore_accountMapEquiv
            (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
            (frobVWishSlot I) debtNew)
      have hWWishEq :
          vatSlotWord (frobWWishSlot I)
            (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)) I = wWish := by
        simpa [wWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord,
          hIlkRateEq, hDebtEq] using
          (vatSlotWord_debtStore_accountMapEquiv
            (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
            (frobWWishSlot I) debtNew)
      have hU' := hU
      rw [hUWishEq] at hU'
      have hV' := hV
      rw [hVWishEq] at hV'
      have hW' := hW
      rw [hWWishEq] at hW'
      have hDustS :
          UInt256.lor
            (UInt256.isZero (UInt256.lt tab ilkDust))
            (UInt256.eq ⟨0⟩ urnArtNew) ≠ ⟨0⟩ := by
        simpa [tab, urnArtNew, urnArt, ilkRate, ilkDust, vatSlotWord,
          hUrnArtEq, hIlkRateEq, hIlkDustEq] using hDust
      have hloadU :
          Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
            (frobUWishSlot I) = uWish := by
        have hmap :
            evmDebt.accountMap =
              sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
          simpa [evmDebt, evm0, initState] using
            storageStore_accountMap evm0 evm0.executionEnv.codeOwner
              foldDebtSlot debtNew
        change
          Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
            (frobUWishSlot I) =
          solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot
            debtNew) I (frobUWishSlot I)
        simp only [Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage]
        rw [hmap]
        simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
      have hloadV :
          Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
            (frobVWishSlot I) = vWish := by
        have hmap :
            evmDebt.accountMap =
              sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
          simpa [evmDebt, evm0, initState] using
            storageStore_accountMap evm0 evm0.executionEnv.codeOwner
              foldDebtSlot debtNew
        change
          Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
            (frobVWishSlot I) =
          solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot
            debtNew) I (frobVWishSlot I)
        simp only [Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage]
        rw [hmap]
        simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
      have hloadW :
          Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
            (frobWWishSlot I) = wWish := by
        have hmap :
            evmDebt.accountMap =
              sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
          simpa [evmDebt, evm0, initState] using
            storageStore_accountMap evm0 evm0.executionEnv.codeOwner
              foldDebtSlot debtNew
        change
          Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
            (frobWWishSlot I) =
          solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot
            debtNew) I (frobWWishSlot I)
        simp only [Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage]
        rw [hmap]
        simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
      have hsrcDebt : evmDebt.executionEnv.source = I.source := by
        simp [evmDebt, evm0, initState, storageStore_executionEnv]
      have hlocalsDebtU :
          localsDebt.get? "u" = some (frobUValue I) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "u" = some (frobUValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_u I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtV :
          localsDebt.get? "v" = some (frobVValue I) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "v" = some (frobVValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_v I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtW :
          localsDebt.get? "w" = some (frobWValue I) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "w" = some (frobWValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_w I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtDart :
          localsDebt.get? "dart" = some (frobDartValue I) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "dart" =
              some (frobDartValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtDink :
          localsDebt.get? "dink" = some (frobDinkValue I) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "dink" =
              some (frobDinkValue I)
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simpa [localsLoaded] using
          frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot
            ilkLine ilkDust
      have hlocalsDebtCan :
          localsDebt.get? "can" = none := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "can" = none
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simp [localsLoaded, frobStoreIlkDust, frobStore]
      have hlocalsDebtUrnArtNew :
          localsDebt.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "urnArtNew" =
              some (.int (Int.ofNat urnArtNew.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self]
      have hlocalsDebtTab :
          localsDebt.get? "tab" = some (.int (Int.ofNat tab.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "tab" =
              some (.int (Int.ofNat tab.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self]
      have hlocalsDebtIlkDust :
          localsDebt.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)) := by
        change
          ((((((localsLoaded.insert "urnInkNew"
            (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
            (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
            (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
            "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
            (.int (Int.ofNat debtNew.toNat))).get? "ilkDust" =
              some (.int (Int.ofNat ilkDust.toNat))
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        simp [localsLoaded, frobStoreIlkDust]
      have hauthBlock :
          ExecBlock config { contract := contract, locals := localsSafe } evmDebt
            [ .require
                (eitherExpr
                  (bothExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (.binary .ge (.var "dink") (.intLit 0)))
                  (wishExpr (.var "u") sender)),
              .require
                (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                  (wishExpr (.var "v") sender)),
              .require
                (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                  (wishExpr (.var "w") sender)),
              .require
                (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                  (.binary .ge (.var "tab") (.var "ilkDust"))) ]
            (.ok { contract := contract, locals := localsSafe } evmDebt) := by
        exact execFrobAuthorizationDustOk_from_sourceConds
          (evm := evmDebt) (I := I) (locals := localsSafe)
          uWish vWish wWish urnArtNew tab ilkDust
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtDart)
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtDink)
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtU)
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtV)
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtW)
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtCan)
          hsrcDebt hloadU hloadV hloadW
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtUrnArtNew)
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtTab)
          (by
            rw [store_get_ne _ _ (by decide)]
            rw [store_get_ne _ _ (by decide)]
            exact hlocalsDebtIlkDust)
          (frobAuthUSourceCond_of_evm (I := I) hU')
          (frobAuthVSourceCond_of_evm (I := I) hV')
          (frobAuthWSourceCond_of_evm (I := I) hW')
          (frobDustSourceCond_of_evm hDustS)
      have h08 := execBlock_append
        (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
          localsDtab, tab, localsDebt, debtOld, dtabWord, debtNew, evmDebt,
          ceilingDebt, inkSpot, localsSafe] using hsourceSafe)
        hauthBlock
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
        tab, localsDebt, debtOld, dtabWord, debtNew, evmDebt, ceilingDebt, inkSpot,
        localsSafe, List.append_assoc] using h08
    have hthroughSafetyEvm :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        (UInt256.slt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (UInt256.sgt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (solcSlotWord σ_evm I (frobIlkRateSlot I)))
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.land
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)
                (solcSlotWord σ_evm I ⟨9⟩)))
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul
                  (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)))
                (solcSlotWord σ_evm I (frobIlkLineSlot I)))))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        (((sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) =
          UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot) →
        (solcSlotWord σ_evm I (frobIlkSpotSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
              (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.isZero
            (UInt256.gt
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ →
        ∃ k' C',
          RD vatBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3605⟩
            [UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)),
              UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)),
              ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
              frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
              frobIWord I, ⟨524⟩, vatSelWord I]
            (frobIlkArtUpdatedMem σ_evm I
              (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
              (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)))
            (UInt256.ofNat 18) ByteArray.empty
            (cA, sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)) k' C' := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk hDebtLoadStore hInkMul
        hSafetyOk
      obtain ⟨_, _, hDebt⟩ :=
        hthroughDebtEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hRateMax hDtabMul hTabMul hDebtNeg hDebtPos
      obtain ⟨_, _, hCeiling⟩ :=
        RD.vatFrobCeilingCheckSuccess
          (h := by simpa using hDebt)
          (by simpa using hCeilingMul)
          (by simpa using hCeilingOk)
          (by simpa [foldDebtSlot] using hDebtLoadStore)
      obtain ⟨_, _, hSafety⟩ :=
        RD.vatFrobSafetyCheckSuccess
          (h := by simpa using hCeiling)
          (by simpa using hInkMul)
          (by simpa using hSafetyOk)
      exact ⟨_, _, by simpa [foldDebtSlot] using hSafety⟩
    have hthroughDustEvm :
        (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
        (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
            (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
        UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
        (frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        ((frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
        (UInt256.slt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (UInt256.sgt
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I))) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩) →
        (solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (solcSlotWord σ_evm I (frobIlkRateSlot I)))
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.land
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)
                (solcSlotWord σ_evm I ⟨9⟩)))
            (UInt256.isZero
              (UInt256.gt
                (UInt256.mul
                  (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)))
                (solcSlotWord σ_evm I (frobIlkLineSlot I)))))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        (((sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) =
          UInt256.mul (frobDartWord I)
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot) →
        (solcSlotWord σ_evm I (frobIlkSpotSlot I) = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.div
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
              (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I)) ≠ ⟨0⟩) →
        UInt256.lor
          (UInt256.isZero
            (UInt256.gt
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (UInt256.mul
                (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                (solcSlotWord σ_evm I (frobIlkSpotSlot I)))))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobUWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobVWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
          (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobWWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I)
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
          (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ →
        UInt256.lor
          (UInt256.isZero
            (UInt256.lt
              (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (solcSlotWord σ_evm I (frobIlkDustSlot I))))
          (UInt256.eq ⟨0⟩
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))) ≠ ⟨0⟩ →
        ∃ k' C',
          RD vatBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3963⟩
            [UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)),
              UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)),
              ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
              frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
              frobIWord I, ⟨524⟩, vatSelWord I]
            (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
              (twoWordHashMem (frobWMaskedWord I) ⟨1⟩
                (twoWordHashMem (hopeSourceWord I)
                  (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
                  (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
                    (twoWordHashMem (hopeSourceWord I)
                      (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                      (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                        (frobIlkArtUpdatedMem σ_evm I
                          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
                          (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)))))))))
            (UInt256.ofNat 18) ByteArray.empty
            (cA, sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)) k' C' := by
      intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
        hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk hDebtLoadStore hInkMul
        hSafetyOk hU hV hW hDust
      obtain ⟨_, _, hSafety⟩ :=
        hthroughSafetyEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
          hRateMax hDtabMul hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk
          hDebtLoadStore hInkMul hSafetyOk
      obtain ⟨_, _, hDustDone⟩ :=
        RD.vatFrobAuthorizationDustChecksSuccess
          (h := by simpa using hSafety)
          (by simpa [foldDebtSlot] using hU)
          (by simpa [foldDebtSlot] using hV)
          (by simpa [foldDebtSlot] using hW)
          (by simpa [foldDebtSlot] using hDust)
      exact ⟨_, _, by simpa [foldDebtSlot] using hDustDone⟩
    classical
    have hsourceRevertFromUrnInkAdd
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromUrnArtAdd
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromIlkArtAdd
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromDtabMul
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromTabMul
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
              checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromDebtAdd
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
              checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
              checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromCeilingMul
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
              checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
              checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
              [ .assign .storage debtRef (.var "debtNew") ] ++
              checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromInkSpotMul
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
              checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
              checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
              [ .assign .storage debtRef (.var "debtNew") ] ++
              checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
              checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromCeilingRequire
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
              checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
              checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
              [ .assign .storage debtRef (.var "debtNew") ] ++
              checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
              checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
              [ .require
                  (eitherExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (bothExpr
                      (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                      (.binary .le (.var "debtNew") (.storage LineRef)))) ])
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromSafetyRequire
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
              checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
              checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
              [ .assign .storage debtRef (.var "debtNew") ] ++
              checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
              checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
              [ .require
                  (eitherExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (bothExpr
                      (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                      (.binary .le (.var "debtNew") (.storage LineRef)))),
                .require
                  (eitherExpr
                    (bothExpr
                      (.binary .le (.var "dart") (.intLit 0))
                      (.binary .ge (.var "dink") (.intLit 0)))
                    (.binary .le (.var "tab") (.var "inkSpot"))) ])
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    have hsourceRevertFromAuthorizationDust
        (hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
              checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
              checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
              checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
              checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
              checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
              [ .assign .storage debtRef (.var "debtNew") ] ++
              checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
              checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
              [ .require
                  (eitherExpr
                    (.binary .le (.var "dart") (.intLit 0))
                    (bothExpr
                      (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                      (.binary .le (.var "debtNew") (.storage LineRef)))),
                .require
                  (eitherExpr
                    (bothExpr
                      (.binary .le (.var "dart") (.intLit 0))
                      (.binary .ge (.var "dink") (.intLit 0)))
                    (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
              [ .require
                  (eitherExpr
                    (bothExpr
                      (.binary .le (.var "dart") (.intLit 0))
                      (.binary .ge (.var "dink") (.intLit 0)))
                    (wishExpr (.var "u") sender)),
                .require
                  (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                    (wishExpr (.var "v") sender)),
                .require
                  (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                    (wishExpr (.var "w") sender)),
                .require
                  (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                    (.binary .ge (.var "tab") (.var "ilkDust"))) ])
            .reverted) :
        ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
          .reverted := by
      have hblock := execBlock_append_term
        (s2 :=
          checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
            (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        hsrcPrefixRevert (by intro f e h; cases h)
      exact ExecFuncBody.execBlockRevert (by
        simpa [ExecTransitionBody, frobTransition, evm0, List.append_assoc]
          using hblock)
    rcases hSuccess with
      ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
        hDtabMul, hTabMul, hDebtNeg, hDebtPos, hCeilingMul, hCeilingOk,
        hDebtLoadStore, hInkMul, hSafetyOk, hU, hV, hW, hDust,
        hGemPos, hGemNeg, hDaiNeg, hDaiPos⟩
    obtain ⟨_, _, hDustDone⟩ :=
      hthroughDustEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
        hRateMax hDtabMul hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk
        hDebtLoadStore hInkMul hSafetyOk hU hV hW hDust
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtOld := vatSlotWord foldDebtSlot σ_solm I
    let dtabWord := UInt256.mul (frobDartWord I) ilkRate
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let evmDebt :=
      Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot
        debtNew
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    let gemOld := solcSlotWord (frobAfterDebt σ_solm I) I (frobGemVSlot I)
    let gemNew := frobGemNew σ_solm I
    let evmGem :=
      Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) gemNew
    let daiOld := solcSlotWord (frobAfterGem σ_solm I) I (frobDaiWSlot I)
    let daiNew := frobDaiNew σ_solm I
    let finalLocals :=
      (localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).insert
        "daiNew" (.int (Int.ofNat daiNew.toNat))
    have hret :
        RDret vatBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, frobAfterRuntimeFinal σ_evm I) ByteArray.empty := by
      exact RD.vatFrobStoreSuccess
        (h := by
          simpa [frobTabWord, frobDtabWord, frobUrnInkNew, frobUrnArtNew,
            frobIlkArtNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using
            hDustDone)
        hperm hGemPos hGemNeg hDaiNeg hDaiPos
    have hsourceDust :=
      hthroughDustSource hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
        hRateMax hDtabMul hTabMul hDebtNeg hDebtPos hCeilingMul hCeilingOk
        hDebtLoadStore hInkMul hSafetyOk hU hV hW hDust
    have hdtabRange := hDtabRangeOfGuards hRateMax hDtabMul
    have hDebtAccounts :
        accountMapEquiv (frobAfterDebt σ_evm I) (frobAfterDebt σ_solm I) :=
      accountMapEquiv_frobAfterDebt (I := I) hAccounts
    have hGemOldEq :
        solcSlotWord (frobAfterDebt σ_evm I) I (frobGemVSlot I) = gemOld :=
      accountMapEquiv_storage_findD hDebtAccounts I.codeOwner (frobGemVSlot I) ⟨0⟩
    have hGemNewEq : frobGemNew σ_evm I = gemNew := by
      simp [gemNew, frobGemNew, gemOld, hGemOldEq]
    have hGemPosS :
        UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt gemNew gemOld = ⟨0⟩ := by
      simpa [gemNew, gemOld, hGemNewEq, hGemOldEq] using hGemPos
    have hGemNegS :
        UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt gemNew gemOld = ⟨0⟩ := by
      simpa [gemNew, gemOld, hGemNewEq, hGemOldEq] using hGemNeg
    have hAfterGemAccounts :
        accountMapEquiv (frobAfterGem σ_evm I) (frobAfterGem σ_solm I) :=
      accountMapEquiv_frobAfterGem (I := I) hAccounts
    have hDaiOldEq :
        solcSlotWord (frobAfterGem σ_evm I) I (frobDaiWSlot I) = daiOld :=
      accountMapEquiv_storage_findD hAfterGemAccounts I.codeOwner (frobDaiWSlot I) ⟨0⟩
    have hDtabEq : frobDtabWord σ_evm I = dtabWord := by
      simp [frobDtabWord, dtabWord, ilkRate, vatSlotWord, hIlkRateEq]
    have hDaiNewEq : frobDaiNew σ_evm I = daiNew := by
      calc
        frobDaiNew σ_evm I =
            frobDtabWord σ_evm I +
              solcSlotWord (frobAfterGem σ_evm I) I (frobDaiWSlot I) := by
          rfl
        _ = dtabWord + daiOld := by
          rw [hDtabEq, hDaiOldEq]
        _ = daiNew := by
          simp [daiNew, frobDaiNew, daiOld, dtabWord, frobDtabWord, ilkRate,
            vatSlotWord, frobAfterGem]
    have hDaiNegS :
        UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt daiNew daiOld = ⟨0⟩ := by
      simpa [dtabWord, daiNew, daiOld, hDtabEq, hDaiNewEq, hDaiOldEq] using
        hDaiNeg
    have hDaiPosS :
        UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt daiNew daiOld = ⟨0⟩ := by
      simpa [dtabWord, daiNew, daiOld, hDtabEq, hDaiNewEq, hDaiOldEq] using
        hDaiPos
    exact vatFrobLiveSuccessFinish hcode hsel hdecode hAccounts hsz196 hret
      hsourceDust hdtabRange hGemPosS hGemNegS hDaiNegS hDaiPosS

end Benchmarks.Dss.Vat

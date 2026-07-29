import Benchmarks.Dss.Vow.CageTailRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` min/heal tail runtime helpers -/

theorem cageSourceVatSinSuccessTailRevertFromBlock
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {outDai outFlap outFlop outDai2 : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin))
    (htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts) .reverted) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin0, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts)
        (.ok { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
          evmFlap) := by
    exact cageFirstDaiFlapperCageSuccess (evm := evmAsh) (evmDai := evmDai)
      (evmFlap := evmFlap) (outDai := outDai) (outFlap := outFlap)
      (flapperDai := flapperDai)
      (by simpa [evm0, evmLive, evmSin0, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin0, evmAsh] using hcallDai)
      hdecDai hflapperCode hcallFlap
  have hflopper :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
        evmFlap cageFlopperCageStmts
        (.ok { contract := contract, locals := cageLocalsAfterFlopCage flapperDai }
          evmFlop) := by
    exact cageFlopperCageSuccess (evm := evmFlap) (evmFlop := evmFlop)
      (outFlop := outFlop) (flapperDai := flapperDai) hflopperCode hcallFlop
  have hsecond :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterFlopCage flapperDai }
        evmFlop cageVatDaiStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
          evmDai2) := by
    exact cageVatDaiSuccess (evm := evmFlop) (evmDai := evmDai2)
      (outDai := outDai2) (flapperDai := flapperDai) (vatDai := vatDai)
      hvatCode2 hcallDai2 hdecDai2
  have hprefix := execBlock_append
    (Reasoning.Theory.execBlock_append
      (Reasoning.Theory.execBlock_append
        (Reasoning.Theory.execBlock_append
          (Reasoning.Theory.execBlock_append hclear hfirst) hflopper) hsecond) hsin)
    htail
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (((((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++
          cageFlopperCageStmts) ++ cageVatDaiStmts) ++ cageVatSinStmts) ++
          cageMinStmts ++ cageVatHealStmts)
        .reverted :=
    by simpa [List.append_assoc] using hprefix
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceVatSinSuccessTailOkFromBlock
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin healRad : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {outDai outFlap outFlop outDai2 : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin))
    (htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts)
        (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin healRad } evmHeal)) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body
      (.returned
        { contract := contract,
          locals := cageLocalsAfterHealRet flapperDai vatDai vatSin healRad }
        evmHeal none) := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin0, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts)
        (.ok { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
          evmFlap) := by
    exact cageFirstDaiFlapperCageSuccess (evm := evmAsh) (evmDai := evmDai)
      (evmFlap := evmFlap) (outDai := outDai) (outFlap := outFlap)
      (flapperDai := flapperDai)
      (by simpa [evm0, evmLive, evmSin0, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin0, evmAsh] using hcallDai)
      hdecDai hflapperCode hcallFlap
  have hflopper :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
        evmFlap cageFlopperCageStmts
        (.ok { contract := contract, locals := cageLocalsAfterFlopCage flapperDai }
          evmFlop) := by
    exact cageFlopperCageSuccess (evm := evmFlap) (evmFlop := evmFlop)
      (outFlop := outFlop) (flapperDai := flapperDai) hflopperCode hcallFlop
  have hsecond :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterFlopCage flapperDai }
        evmFlop cageVatDaiStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
          evmDai2) := by
    exact cageVatDaiSuccess (evm := evmFlop) (evmDai := evmDai2)
      (outDai := outDai2) (flapperDai := flapperDai) (vatDai := vatDai)
      hvatCode2 hcallDai2 hdecDai2
  have hprefix := execBlock_append
    (Reasoning.Theory.execBlock_append
      (Reasoning.Theory.execBlock_append
        (Reasoning.Theory.execBlock_append
          (Reasoning.Theory.execBlock_append hclear hfirst) hflopper) hsecond) hsin)
    htail
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (((((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++
          cageFlopperCageStmts) ++ cageVatDaiStmts) ++ cageVatSinStmts) ++
          cageMinStmts ++ cageVatHealStmts)
        (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin healRad } evmHeal) :=
    by simpa [List.append_assoc] using hprefix
  have hbody := ExecFuncBody.execBlockOK hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceMinHealLeftNoCode
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {outDai outFlap outFlop outDai2 outSin : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatNoCode :
      (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin) :=
    cageVatSinSuccess (evm := evmDai2) (evmSin := evmSin) (outSin := outSin)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hvatCodeSin hcallSin hdecSin
  have htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts) .reverted :=
    cageMinHealLeftNoCode (evm := evmSin) (flapperDai := flapperDai)
      (vatDai := vatDai) (vatSin := vatSin) hle hvatNoCode
  exact cageSourceVatSinSuccessTailRevertFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (vatSin := vatSin) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (evmSin := evmSin)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) hwv hauth hlive hvatCode hcallDai
    hdecDai hflapperCode hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2
    hdecDai2 hsin htail

theorem cageSourceMinHealRightNoCode
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {outDai outFlap outFlop outDai2 outSin : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatNoCode :
      (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin) :=
    cageVatSinSuccess (evm := evmDai2) (evmSin := evmSin) (outSin := outSin)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hvatCodeSin hcallSin hdecSin
  have htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts) .reverted :=
    cageMinHealRightNoCode (evm := evmSin) (flapperDai := flapperDai)
      (vatDai := vatDai) (vatSin := vatSin) hlt hvatNoCode
  exact cageSourceVatSinSuccessTailRevertFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (vatSin := vatSin) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (evmSin := evmSin)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) hwv hauth hlive hvatCode hcallDai
    hdecDai hflapperCode hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2
    hdecDai2 hsin htail

theorem cageSourceMinHealLeftCallFailure
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {outDai outFlap outFlop outDai2 outSin outHeal : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatDai.toNat)] (false, evmHeal, outHeal) true) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin) :=
    cageVatSinSuccess (evm := evmDai2) (evmSin := evmSin) (outSin := outSin)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hvatCodeSin hcallSin hdecSin
  have htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts) .reverted :=
    cageMinHealLeftCallFailure (evm := evmSin) (evmHeal := evmHeal)
      (outHeal := outHeal) (flapperDai := flapperDai) (vatDai := vatDai)
      (vatSin := vatSin) hle hvatCodeHeal hcallHeal
  exact cageSourceVatSinSuccessTailRevertFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (vatSin := vatSin) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (evmSin := evmSin)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode
    hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hsin htail

theorem cageSourceMinHealRightCallFailure
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {outDai outFlap outFlop outDai2 outSin outHeal : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatSin.toNat)] (false, evmHeal, outHeal) true) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin) :=
    cageVatSinSuccess (evm := evmDai2) (evmSin := evmSin) (outSin := outSin)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hvatCodeSin hcallSin hdecSin
  have htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts) .reverted :=
    cageMinHealRightCallFailure (evm := evmSin) (evmHeal := evmHeal)
      (outHeal := outHeal) (flapperDai := flapperDai) (vatDai := vatDai)
      (vatSin := vatSin) hlt hvatCodeHeal hcallHeal
  exact cageSourceVatSinSuccessTailRevertFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (vatSin := vatSin) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (evmSin := evmSin)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode
    hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hsin htail

theorem cageSourceMinHealLeftSuccess
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {outDai outFlap outFlop outDai2 outSin outHeal : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatDai.toNat)] (true, evmHeal, outHeal) true) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body
      (.returned
        { contract := contract,
          locals := cageLocalsAfterHealRet flapperDai vatDai vatSin vatDai }
        evmHeal none) := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin) :=
    cageVatSinSuccess (evm := evmDai2) (evmSin := evmSin) (outSin := outSin)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hvatCodeSin hcallSin hdecSin
  have htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts)
        (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin vatDai } evmHeal) :=
    cageMinHealLeftSuccess (evm := evmSin) (evmHeal := evmHeal) (outHeal := outHeal)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hle hvatCodeHeal hcallHeal
  exact cageSourceVatSinSuccessTailOkFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (vatSin := vatSin) (healRad := vatDai) (evmDai := evmDai)
    (evmFlap := evmFlap) (evmFlop := evmFlop) (evmDai2 := evmDai2)
    (evmSin := evmSin) (evmHeal := evmHeal) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hsin htail

theorem cageSourceMinHealRightSuccess
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {outDai outFlap outFlop outDai2 outSin outHeal : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatSin.toNat)] (true, evmHeal, outHeal) true) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body
      (.returned
        { contract := contract,
          locals := cageLocalsAfterHealRet flapperDai vatDai vatSin vatSin }
        evmHeal none) := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin) :=
    cageVatSinSuccess (evm := evmDai2) (evmSin := evmSin) (outSin := outSin)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hvatCodeSin hcallSin hdecSin
  have htail :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin (cageMinStmts ++ cageVatHealStmts)
        (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin vatSin } evmHeal) :=
    cageMinHealRightSuccess (evm := evmSin) (evmHeal := evmHeal) (outHeal := outHeal)
      (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
      hlt hvatCodeHeal hcallHeal
  exact cageSourceVatSinSuccessTailOkFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (vatSin := vatSin) (healRad := vatSin) (evmDai := evmDai)
    (evmFlap := evmFlap) (evmFlop := evmFlop) (evmDai2 := evmDai2)
    (evmSin := evmSin) (evmHeal := evmHeal) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hsin htail

theorem vowCageMinHealLeftNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {mem outDai outFlap outFlop outDai2 outSin rdata : ByteArray}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3234 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3234⟩
      (vatSin :: vatDai :: ⟨3238⟩ :: kissHealSelector ::
        kissDaiTargetWord acc.2 I :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) =
        ⟨0⟩)
    (hov : R.length + 15 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatNoCode :
      (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd3238⟩ := RD.vowCageMinReturnLeft rd3234 hle (by simp; omega)
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageHealNoCode rd3238 hmem hread64 hcodeSize (by simp; omega)
  have hbody := cageSourceMinHealLeftNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
    (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
    (evmDai2 := evmDai2) (evmSin := evmSin) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    (outSin := outSin) hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode
    hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin
    hcallSin hdecSin hle hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageMinHealRightNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {mem outDai outFlap outFlop outDai2 outSin rdata : ByteArray}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3234 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3234⟩
      (vatSin :: vatDai :: ⟨3238⟩ :: kissHealSelector ::
        kissDaiTargetWord acc.2 I :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) =
        ⟨0⟩)
    (hov : R.length + 15 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatNoCode :
      (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd3238⟩ := RD.vowCageMinReturnRight rd3234 hlt (by simp; omega)
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageHealNoCode rd3238 hmem hread64 hcodeSize (by simp; omega)
  have hbody := cageSourceMinHealRightNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
    (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
    (evmDai2 := evmDai2) (evmSin := evmSin) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    (outSin := outSin) hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode
    hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin
    hcallSin hdecSin hlt hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageMinHealLeftCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {mem outDai outFlap outFlop outDai2 outSin outHeal : ByteArray} {aw target : UInt256}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3296 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3296⟩
      (⟨0⟩ :: kissHealEndPtr :: kissHealSelector :: target :: R)
      mem aw outHeal acc k C)
    (houtHealSize : outHeal.size < UInt256.size)
    (hov : R.length + 8 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatDai.toNat)] (false, evmHeal, outHeal) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageHealCallFailure rd3296 houtHealSize (by simp; omega)
  have hbody := cageSourceMinHealLeftCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
    (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
    (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHeal)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin hdecSin hle
    hvatCodeHeal hcallHeal
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageMinHealRightCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {mem outDai outFlap outFlop outDai2 outSin outHeal : ByteArray} {aw target : UInt256}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3296 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3296⟩
      (⟨0⟩ :: kissHealEndPtr :: kissHealSelector :: target :: R)
      mem aw outHeal acc k C)
    (houtHealSize : outHeal.size < UInt256.size)
    (hov : R.length + 8 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatSin.toNat)] (false, evmHeal, outHeal) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageHealCallFailure rd3296 houtHealSize (by simp; omega)
  have hbody := cageSourceMinHealRightCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
    (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
    (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHeal)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin hdecSin hlt
    hvatCodeHeal hcallHeal
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageMinHealLeftSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai vatSin sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {mem outDai outFlap outFlop outDai2 outSin outHeal : ByteArray} {aw : UInt256}
    {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3296 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3296⟩
      (⟨1⟩ :: kissHealEndPtr :: kissHealSelector :: target :: ⟨412⟩ :: sel :: [])
      mem aw outHeal acc k C)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatDai.toNat)] (true, evmHeal, outHeal) true)
    (hcreated : acc.1 = evmHeal.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmHeal.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hret : RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty :=
    RD.vowCageHealCallSuccess rd3296
  have hbody := cageSourceMinHealLeftSuccess (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
    (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
    (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHeal)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin hdecSin hle
    hvatCodeHeal hcallHeal
  have henc : returnEquiv ByteArray.empty none cageTransition.returnType := by
    rw [show cageTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated hAccountsFinal henc

theorem vowCageMinHealRightSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai vatSin sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin evmHeal : EVM.State}
    {mem outDai outFlap outFlop outDai2 outSin outHeal : ByteArray} {aw : UInt256}
    {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3296 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3296⟩
      (⟨1⟩ :: kissHealEndPtr :: kissHealSelector :: target :: ⟨412⟩ :: sel :: [])
      mem aw outHeal acc k C)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin0 := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin0 I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (true, evmFlop, outFlop) true)
    (hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai2 :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
        false)
    (hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
        "heal" 0 [.int (Int.ofNat vatSin.toNat)] (true, evmHeal, outHeal) true)
    (hcreated : acc.1 = evmHeal.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmHeal.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hret : RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty :=
    RD.vowCageHealCallSuccess rd3296
  have hbody := cageSourceMinHealRightSuccess (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
    (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
    (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHeal)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin hdecSin hlt
    hvatCodeHeal hcallHeal
  have henc : returnEquiv ByteArray.empty none cageTransition.returnType := by
    rw [show cageTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated hAccountsFinal henc

end Benchmarks.Dss.Vow

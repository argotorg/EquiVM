import Benchmarks.Dss.Vow.CageRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` tail runtime helpers -/

theorem cageSourceSecondDaiNoCode
    {cA gh bl σ σ₀ A I} {g flapperDai : UInt256}
    {evmDai evmFlap evmFlop : EVM.State} {outDai outFlap outFlop : ByteArray}
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
    (hvatNoCode :
      (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
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
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
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
        evmFlop cageVatDaiStmts .reverted :=
    cageVatDaiNoCode (evm := evmFlop) (flapperDai := flapperDai) hvatNoCode
  have hprefix :=.execBlock_append
    (Reasoning.Theory.execBlock_append
      (Reasoning.Theory.execBlock_append hclear hfirst) hflopper) hsecond
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++
          cageFlopperCageStmts) ++ cageVatDaiStmts) ++
          cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
        .reverted :=
   .execBlock_append_term
      (s2 := cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceSecondDaiCallFailure
    {cA gh bl σ σ₀ A I} {g flapperDai : UInt256}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
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
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (false, evmDai2, outDai2)
        false) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
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
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
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
        evmFlop cageVatDaiStmts .reverted :=
    cageVatDaiCallFailure (evm := evmFlop) (evmDai := evmDai2)
      (outDai := outDai2) (flapperDai := flapperDai) hvatCode2 hcallDai2
  have hprefix :=.execBlock_append
    (Reasoning.Theory.execBlock_append
      (Reasoning.Theory.execBlock_append hclear hfirst) hflopper) hsecond
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++
          cageFlopperCageStmts) ++ cageVatDaiStmts) ++
          cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
        .reverted :=
   .execBlock_append_term
      (s2 := cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceSecondDaiReturnDecodeFailure
    {cA gh bl σ σ₀ A I} {g flapperDai : UInt256}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
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
    (hdecDai2 : config.externalABI.decode? "dai" outDai2 = none) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
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
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
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
        evmFlop cageVatDaiStmts .reverted :=
    cageVatDaiReturnDecodeFailure (evm := evmFlop) (evmDai := evmDai2)
      (outDai := outDai2) (flapperDai := flapperDai) hvatCode2 hcallDai2 hdecDai2
  have hprefix :=.execBlock_append
    (Reasoning.Theory.execBlock_append
      (Reasoning.Theory.execBlock_append hclear hfirst) hflopper) hsecond
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++
          cageFlopperCageStmts) ++ cageVatDaiStmts) ++
          cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
        .reverted :=
   .execBlock_append_term
      (s2 := cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceVatSinNoCode
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai : UInt256}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
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
    (hvatNoCode :
      (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
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
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
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
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts .reverted :=
    cageVatSinNoCode (evm := evmDai2) (flapperDai := flapperDai)
      (vatDai := vatDai) hvatNoCode
  have hprefix :=.execBlock_append
    (Reasoning.Theory.execBlock_append
      (Reasoning.Theory.execBlock_append
        (Reasoning.Theory.execBlock_append hclear hfirst) hflopper) hsecond) hsin
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
   .execBlock_append_term
      (s2 := cageMinStmts ++ cageVatHealStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceVatSinRevertFromBlock
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai : UInt256}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
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
        evmDai2 cageVatSinStmts .reverted) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
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
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
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
  have hprefix :=.execBlock_append
    (Reasoning.Theory.execBlock_append
      (Reasoning.Theory.execBlock_append
        (Reasoning.Theory.execBlock_append hclear hfirst) hflopper) hsecond) hsin
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
   .execBlock_append_term
      (s2 := cageMinStmts ++ cageVatHealStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceVatSinCallFailure
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {outDai outFlap outFlop outDai2 outSin : ByteArray}
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
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (false, evmSin, outSin)
        false) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts .reverted :=
    cageVatSinCallFailure (evm := evmDai2) (evmSin := evmSin) (outSin := outSin)
      (flapperDai := flapperDai) (vatDai := vatDai) hvatCodeSin hcallSin
  exact cageSourceVatSinRevertFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hsin

theorem cageSourceVatSinReturnDecodeFailure
    {cA gh bl σ σ₀ A I} {g flapperDai vatDai : UInt256}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {outDai outFlap outFlop outDai2 outSin : ByteArray}
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
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin : config.externalABI.decode? "sin" outSin = none) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  have hsin :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai2 cageVatSinStmts .reverted :=
    cageVatSinReturnDecodeFailure (evm := evmDai2) (evmSin := evmSin)
      (outSin := outSin) (flapperDai := flapperDai) (vatDai := vatDai)
      hvatCodeSin hcallSin hdecSin
  exact cageSourceVatSinRevertFromBlock (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (flapperDai := flapperDai)
    (vatDai := vatDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hsin

theorem vowCageSecondDaiNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai d1 d2 : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop : EVM.State} {mem outDai outFlap outFlop rdata : ByteArray}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd2983 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2983⟩
      (d1 :: d2 :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) =
        ⟨0⟩)
    (hov : R.length + 16 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
    (hvatNoCode :
      (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageSecondDaiNoCode rd2983 hmem hread64 hcodeSize hov
  have hbody := cageSourceSecondDaiNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (outDai := outDai) (outFlap := outFlap)
    (outFlop := outFlop) hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode
    hcallFlap hflopperCode hcallFlop hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageSecondDaiCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
    {mem outDai outFlap outFlop outDai2 rdata : ByteArray} {aw : UInt256}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3074 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3074⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: ⟨3238⟩ ::
        ⟨4084909596⟩ :: target :: R)
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 11 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
        "dai" 0 [.address evmFlop.executionEnv.codeOwner] (false, evmDai2, outDai2)
        false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageSecondDaiCallFailure rd3074 hrdataSize (by simp; omega)
  have hbody := cageSourceSecondDaiCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageSecondDaiDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
    {base outDai outFlap outFlop outDai2 : ByteArray} {k C : ℕ}
    {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3074 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3074⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: ⟨3238⟩ ::
        ⟨4084909596⟩ :: target :: R)
      (outDai2.write 0 base 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai2.size)).toNat)
      (UInt256.ofNat 6) outDai2 acc k C)
    (hbase : base.size = 164)
    (hbaseRead64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hosz : outDai2.size < UInt256.size)
    (hshort : outDai2.size < 32)
    (hov : R.length + 12 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
        false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai2.size)).toNat = outDai2.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd3074Short := rd3074
  rw [hmin] at rd3074Short
  obtain ⟨_, _, rd3092⟩ :=
    RD.vowCageSecondDaiCallSuccessToDecode rd3074Short (by simp; omega)
  have hmemWrite :
      (outDai2.write 0 base 128 outDai2.size).size = 164 :=
    returnWrite_size_164 outDai2 outDai2.size hbase (by omega) (by omega)
  have hread64Write :
      (outDai2.write 0 base 128 outDai2.size).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    returnWrite_read64 outDai2 outDai2.size hbase hbaseRead64 (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (outDai2.write 0 base 128 outDai2.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai2.write 0 base 128 outDai2.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageSecondDaiReturnDecodeShortReverts rd3092 hshort hosz hmload64
      (by simp; omega)
  have hdecDai2 : config.externalABI.decode? "dai" outDai2 = none :=
    kissDaiDecode_none_short hshort
  have hbody := cageSourceSecondDaiReturnDecodeFailure (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (evmDai2 := evmDai2) (outDai := outDai)
    (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageVatSinNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
    {base outDai outFlap outFlop outDai2 : ByteArray} {k C : ℕ}
    {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3074 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3074⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord acc.2 I ::
        ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc.2 I :: R)
      (outDai2.write 0 base 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai2.size)).toNat)
      (UInt256.ofNat 6) outDai2 acc k C)
    (hbase : base.size = 164)
    (hbaseRead64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ outDai2.size)
    (hosz : outDai2.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) =
        ⟨0⟩)
    (hov : R.length + 18 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
    (hvatNoCode :
      (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let vatDai := UInt256.ofNat (fromByteArrayBigEndian (outDai2.extract 0 32))
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai2.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd3074Write := rd3074
  rw [hmin] at rd3074Write
  obtain ⟨_, _, rd3092⟩ :=
    RD.vowCageSecondDaiCallSuccessToDecode rd3074Write (by simp; omega)
  have hmemWrite :
      (outDai2.write 0 base 128 32).size = 164 :=
    returnWrite_size_164 outDai2 32 hbase (by omega) ho32
  have hread64Write :
      (outDai2.write 0 base 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    returnWrite_read64 outDai2 32 hbase hbaseRead64 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (outDai2.write 0 base 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai2.write 0 base 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (outDai2.write 0 base 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai2.write 0 base 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (outDai2.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥ (outDai2.write 0 base 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmemWrite]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      returnWrite_read128_32 outDai2 hbase ho32]
  obtain ⟨_, _, rd3115⟩ :=
    RD.vowCageSecondDaiReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (outDai2.extract 0 32)))
      rd3092 ho32 hosz hmload64 hmload128 (by simp; omega)
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageVatSinNoCode (by simpa [vatDai] using rd3115)
      hmemWrite hread64Write hcodeSize (by simp; omega)
  have hdecDai2 :
      config.externalABI.decode? "dai" outDai2 =
        some [.int (Int.ofNat vatDai.toNat)] := by
    simpa [vatDai] using kissDaiDecode_ok (o := outDai2) ho32
  have hbody := cageSourceVatSinNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (evmDai := evmDai)
    (evmFlap := evmFlap) (evmFlop := evmFlop) (evmDai2 := evmDai2)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode
    hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageVatSinCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {mem outDai outFlap outFlop outDai2 outSin : ByteArray} {aw : UInt256}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3193 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3193⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector :: kissDaiTargetWord acc.2 I ::
        vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc.2 I :: R)
      mem aw outSin acc k C)
    (houtSinSize : outSin.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (false, evmSin, outSin)
        false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageVatSinCallFailure rd3193 houtSinSize (by simp; omega)
  have hbody := cageSourceVatSinCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (evmDai := evmDai)
    (evmFlap := evmFlap) (evmFlop := evmFlop) (evmDai2 := evmDai2)
    (evmSin := evmSin) (outDai := outDai) (outFlap := outFlap)
    (outFlop := outFlop) (outDai2 := outDai2) (outSin := outSin)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageVatSinDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
    {base outDai outFlap outFlop outDai2 outSin : ByteArray}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3193 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3193⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: kissDaiTargetWord acc.2 I ::
        vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc.2 I :: R)
      (outSin.write 0 base 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
      (UInt256.ofNat 6) outSin acc k C)
    (hbase : base.size = 164)
    (hbaseRead64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hosz : outSin.size < UInt256.size)
    (hshort : outSin.size < 32)
    (hov : R.length + 13 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
        false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = outSin.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd3193Short := rd3193
  rw [hmin] at rd3193Short
  obtain ⟨_, _, rd3211⟩ :=
    RD.vowCageVatSinCallSuccessToDecode rd3193Short (by simp; omega)
  have hmemWrite :
      (outSin.write 0 base 128 outSin.size).size = 164 :=
    returnWrite_size_164 outSin outSin.size hbase (by omega) (by omega)
  have hread64Write :
      (outSin.write 0 base 128 outSin.size).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    returnWrite_read64 outSin outSin.size hbase hbaseRead64 (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (outSin.write 0 base 128 outSin.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin.write 0 base 128 outSin.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageVatSinReturnDecodeShortReverts rd3211 hshort hosz hmload64
      (by simp; omega)
  have hdecSin : config.externalABI.decode? "sin" outSin = none :=
    vatSinDecode_none_short hshort
  have hbody := cageSourceVatSinReturnDecodeFailure (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (evmDai := evmDai)
    (evmFlap := evmFlap) (evmFlop := evmFlop) (evmDai2 := evmDai2)
    (evmSin := evmSin) (outDai := outDai) (outFlap := outFlap)
    (outFlop := outFlop) (outDai2 := outDai2) (outSin := outSin)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode
    hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin hdecSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow

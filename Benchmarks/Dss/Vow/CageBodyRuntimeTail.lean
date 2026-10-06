import Benchmarks.Dss.Vow.CageBodyRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` final runtime wrapper tail -/

theorem vowCageVatSinNoCodeAt3115BodyCore
    {σ σ₀ A I} {g flapperDai vatDai : UInt256}
    {acc : AccountMap}
    {evmDai evmFlap evmFlop evmDai2 : EVM.State}
    {mem outDai outFlap outFlop outDai2 : ByteArray} {k C : ℕ}
    {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd3115 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3115⟩
      (vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc I :: R)
      mem (UInt256.ofNat 6) outDai2 acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc (kissDaiTargetWord acc I) =
        ⟨0⟩)
    (hov : R.length + 18 ≤ 1024)
    (hvatCode :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
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
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageVatSinNoCode rd3115 hmem hread64 hcodeSize hov
  have hbody := cageSourceVatSinNoCode
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (vatDai := vatDai) (evmDai := evmDai)
    (evmFlap := evmFlap) (evmFlop := evmFlop) (evmDai2 := evmDai2)
    (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
    (outDai2 := outDai2) hwv hauth hlive hvatCode hcallDai hdecDai
    hflapperCode hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2
    hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 0 in
theorem vowCageBodyToMinHeal
    {σ σ₀ A I} {g : UInt256}
    (cont :
      ∀ {σ_sin : AccountMap}
        {evmDai evmFlap evmFlop evmDai2 evmSin : EVM.State}
        {outDai outFlap outFlop outDai2 outSin memSin : ByteArray} {k3234 C3234 : ℕ}
        {flapperDai vatDai vatSin : UInt256},
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3234⟩
          (vatSin :: vatDai :: ⟨3238⟩ :: kissHealSelector ::
            kissDaiTargetWord σ_sin I :: ⟨412⟩ :: vowSelWord I :: [])
          memSin (UInt256.ofNat 6) outSin σ_sin k3234 C3234 →
        memSin.size = 164 →
        memSin.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat flapperDai.toNat)] →
        solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩ →
        solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ →
        0 < (UInt256.ofNat
          ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
          "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
          true →
        0 < (UInt256.ofNat
          ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
          "cage" 0 [] (true, evmFlop, outFlop) true →
        0 < (UInt256.ofNat
          ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
          "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
          false →
        config.externalABI.decode? "dai" outDai2 =
          some [.int (Int.ofNat vatDai.toNat)] →
        0 < (UInt256.ofNat
          ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
          "sin" 0 [.address evmDai2.executionEnv.codeOwner] (true, evmSin, outSin)
          false →
        config.externalABI.decode? "sin" outSin =
          some [.int (Int.ofNat vatSin.toNat)] →
        I.depth.val < 1024 →
        evmSin.σ₀ = σ₀ →
        evmSin.executionEnv = I →
        Eq σ_sin evmSin.accountMap →
        runtimeEquivalenceFor config contract σ σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToVatSin
      (fun {σ_dai2} {evmDai} {evmFlap} {evmFlop} {evmDai2}
          {outDai} {outFlap} {outFlop} {outDai2} {memDai2} {k3115} {C3115}
          {flapperDai} {vatDai} rd3115 hmemDai2 hread64Dai2 hvatCode hcallDai
          hdecDai hauthSolm hliveSolm hflapperCode hcallFlap hflopperCode hcallFlop
          hvatCode2 hcallDai2 hdecDai2 hdepthLt hσ0Dai2 henvDai2 hAccountsDai2 => ?_)
      hcode hsize hperm hwv hsel
  by_cases hcodeSizeVatSin :
      Reasoning.Theory.extCodeSizeWord σ_dai2 (kissDaiTargetWord σ_dai2 I) =
        ⟨0⟩
  · have hcodeSizeVatSinSolm :
        Reasoning.Theory.extCodeSizeWord evmDai2.accountMap
            (kissDaiTargetWord evmDai2.accountMap I) = ⟨0⟩ := by
      simpa only [← hAccountsDai2] using hcodeSizeVatSin
    have hownerDai2 : evmDai2.executionEnv.codeOwner = I.codeOwner := by
      simp [henvDai2]
    have hvatNoCode :
        (UInt256.ofNat
          ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      cageVatCode_zero_of_codeSize_zero evmDai2 I hownerDai2 hcodeSizeVatSinSolm
    exact vowCageVatSinNoCodeAt3115BodyCore (acc := σ_dai2)
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
      (evmDai2 := evmDai2) (outDai := outDai) (outFlap := outFlap)
      (outFlop := outFlop) (outDai2 := outDai2) (R := [⟨412⟩, vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa using rd3115) hmemDai2 hread64Dai2 hcodeSizeVatSin (by simp)
      hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
      hvatCode2 hcallDai2 hdecDai2 hvatNoCode
  have hcodeSizeVatSinNE :
      Reasoning.Theory.extCodeSizeWord σ_dai2 (kissDaiTargetWord σ_dai2 I) ≠
        ⟨0⟩ :=
    hcodeSizeVatSin
  have hcodeSizeVatSinSolmNE :
      Reasoning.Theory.extCodeSizeWord evmDai2.accountMap
          (kissDaiTargetWord evmDai2.accountMap I) ≠ ⟨0⟩ := by
    simpa only [← hAccountsDai2] using hcodeSizeVatSinNE
  have hownerDai2 : evmDai2.executionEnv.codeOwner = I.codeOwner := by
    simp [henvDai2]
  have hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai2.lookupAccount (cageVatAddressOf evmDai2)).option 0
          (fun acc => acc.code.size))).toNat :=
    cageVatCode_pos_of_codeSize_ne evmDai2 I hownerDai2 hcodeSizeVatSinSolmNE
  obtain ⟨σ_sin, zSin, outSin, A_sin, k3193, C3193, rd3193,
      hcallSinEvmRaw, houtSinSize⟩ :=
    RD.vowCageVatSinStaticcall
      (σCall := σ_dai2)
      (R := [⟨412⟩, vowSelWord I])
      rd3115 hmemDai2 hread64Dai2 hcodeSizeVatSinNE hdepthLt (by simp)
  let evmSinEvmIn :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_dai2
    }
  let evmSinEvmOut :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_sin
      substate := A_sin
    }
  have hcallSinEvm :
      typedCallViaEVM config evmSinEvmIn (EVM.address (kissVatAddress σ_dai2 I))
        "sin" 0 [.address I.codeOwner] (zSin, evmSinEvmOut, outSin) false := by
    simpa [evmSinEvmIn, evmSinEvmOut] using hcallSinEvmRaw
  have hSinTargetPostEvm : kissDaiTargetWord σ_sin I = kissDaiTargetWord σ_dai2 I := by
    have hslot :=
      typedCallViaEVM_static_storage_getD_of_accounts_eq
        (cfg := config) (σ := σ_dai2) (evm := evmSinEvmIn)
        (evm' := evmSinEvmOut) (target := EVM.address (kissVatAddress σ_dai2 I))
        (name := "sin") (args := [.address I.codeOwner]) (z := zSin)
        (out := outSin) (slot := ⟨1⟩) (default := ⟨0⟩)
        (by simp [evmSinEvmIn])
        hcallSinEvm
    simpa [kissDaiTargetWord, solcSlotWordAt, evmSinEvmIn, evmSinEvmOut, initState] using
      congrArg (fun word => UInt256.land word solcAddrMask) hslot
  have hVatAddrMap : kissVatAddress σ_dai2 I = kissVatAddress evmDai2.accountMap I :=
    congrArg (fun accounts => kissVatAddress accounts I) hAccountsDai2
  have hVatAddrSolm : cageVatAddressOf evmDai2 = kissVatAddress evmDai2.accountMap I :=
    cageVatAddressOf_eq_kissVatAddress evmDai2 I hownerDai2
  have hVatTargetAddr :
      EVM.address (kissVatAddress σ_dai2 I) =
        EVM.address (cageVatAddressOf evmDai2) := by
    rw [hVatAddrMap, ← hVatAddrSolm]
  have hVatTargetAddrDai2 :
      EVM.address (kissVatAddress σ_dai2 evmDai2.executionEnv) =
        EVM.address (cageVatAddressOf evmDai2) := by
    simpa [← henvDai2] using hVatTargetAddr
  obtain ⟨σ_sin_solm, A_sin_solm0, hcallSinSolmBase, hAccountsSin⟩ :=
    typedCallViaEVM_sameInputs (evm_solm := evmDai2)
      hcallSinEvm hAccountsDai2
      (by simpa [evmSinEvmIn, initState] using hσ0Dai2.symm)
      (by simpa [evmSinEvmIn, initState] using henvDai2.symm)
  let evmSinSolm :=
    { evmDai2 with
      accountMap := σ_sin_solm
      substate := A_sin_solm0
    }
  have hcallSinSolm :
      typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
        "sin" 0 [.address evmDai2.executionEnv.codeOwner]
        (zSin, evmSinSolm, outSin) false := by
    simpa [evmSinSolm, evmSinEvmOut, hVatTargetAddrDai2, ← henvDai2]
      using hcallSinSolmBase
  cases zSin
  · exact vowCageVatSinCallFailureBodyCore (acc := σ_sin)
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
      (evmDai2 := evmDai2) (evmSin := evmSinSolm) (R := [⟨412⟩, vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa [hSinTargetPostEvm] using rd3193) houtSinSize (by simp)
      hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
      hvatCode2 hcallDai2 hdecDai2 hvatCodeSin
      (by simpa using hcallSinSolm)
  · have rd3193True : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3193⟩
        (⟨1⟩ :: healSinEndPtr :: healSinSelector :: kissDaiTargetWord σ_sin I ::
          vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord σ_sin I ::
          ⟨412⟩ :: vowSelWord I :: [])
        (outSin.write 0 (healSinCalldataMem I memDai2) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
        (UInt256.ofNat 6) outSin σ_sin k3193 C3193 := by
      simpa [hSinTargetPostEvm] using rd3193
    have hcallSinSolmTrue :
        typedCallViaEVM config evmDai2 (EVM.address (cageVatAddressOf evmDai2))
          "sin" 0 [.address evmDai2.executionEnv.codeOwner]
          (true, evmSinSolm, outSin) false := by
      simpa using hcallSinSolm
    let baseSin := healSinCalldataMem I memDai2
    have hbaseSin : baseSin.size = 164 := by
      simpa [baseSin] using healSinCalldataMem_size I hmemDai2
    have hbaseSinRead64 :
        baseSin.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [baseSin] using healSinCalldataMem_read64 I hmemDai2 hread64Dai2
    by_cases ho32Sin : 32 ≤ outSin.size
    · let vatSin : UInt256 :=
        UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32))
      have hmin :
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = 32 :=
        ctorMin32_toNat_of_ge ho32Sin houtSinSize
      have rd3193Write := rd3193True
      rw [hmin] at rd3193Write
      obtain ⟨_, _, rd3211⟩ :=
        RD.vowCageVatSinCallSuccessToDecode rd3193Write (by simp)
      let memSin := outSin.write 0 baseSin 128 32
      have hmemSin : memSin.size = 164 := by
        simpa [memSin] using returnWrite_size_164 outSin 32 hbaseSin
          (by omega) ho32Sin
      have hread64Sin :
          memSin.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memSin] using returnWrite_read64 outSin 32 hbaseSin
          hbaseSinRead64 (by omega) ho32Sin
      have hmload64 :
          (if (⟨64⟩ : UInt256).toNat ≥ memSin.size then ⟨0⟩
           else UInt256.ofNat
             (fromByteArrayBigEndian
              (memSin.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
            ⟨128⟩ :=
        mloadFreePtrValue (by rw [hmemSin]; decide) hread64Sin
      have hmload128 :
          (if (⟨128⟩ : UInt256).toNat ≥ memSin.size then ⟨0⟩
           else UInt256.ofNat
             (fromByteArrayBigEndian
              (memSin.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
            UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)) := by
        have hnot :
            ¬ ((⟨128⟩ : UInt256).toNat ≥ memSin.size) := by
          rw [hmemSin]
          native_decide
        rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        simpa [memSin] using
          congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes))
            (returnWrite_read128_32 outSin hbaseSin ho32Sin)
      obtain ⟨k3234, C3234, rd3234⟩ :=
        RD.vowCageVatSinReturnDecodeOk
          (retWord := UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)))
          rd3211 ho32Sin houtSinSize hmload64 hmload128 (by simp)
      have hdecSin :
          config.externalABI.decode? "sin" outSin =
            some [.int (Int.ofNat vatSin.toNat)] := by
        simpa [vatSin] using vatSinDecode_ok (o := outSin) ho32Sin
      have hσ0Sin : evmSinSolm.σ₀ = σ₀ := by
        simpa [evmSinSolm] using hσ0Dai2
      have henvSin : evmSinSolm.executionEnv = I := by
        simpa [evmSinSolm] using henvDai2
      exact cont (σ_sin := σ_sin) (evmDai := evmDai) (evmFlap := evmFlap)
        (evmFlop := evmFlop) (evmDai2 := evmDai2) (evmSin := evmSinSolm)
        (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
        (outDai2 := outDai2) (outSin := outSin) (memSin := memSin)
        (flapperDai := flapperDai) (vatDai := vatDai) (vatSin := vatSin)
        (by simpa [vatSin, memSin, kissHealSelector] using rd3234)
        hmemSin hread64Sin hvatCode hcallDai hdecDai hauthSolm hliveSolm
        hflapperCode hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2
        hdecDai2 hvatCodeSin hcallSinSolmTrue hdecSin hdepthLt hσ0Sin henvSin
        (by simpa [evmSinEvmOut, evmSinSolm] using hAccountsSin)
    · have hshortSin : outSin.size < 32 := Nat.lt_of_not_ge ho32Sin
      exact vowCageVatSinDecodeShortBodyCore (acc := σ_sin)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2) (evmSin := evmSinSolm) (base := baseSin)
        (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
        (outDai2 := outDai2) (outSin := outSin) (R := [⟨412⟩, vowSelWord I])
        hcode hwv hauthSolm hliveSolm hdispatch hdecode rd3193True
        hbaseSin hbaseSinRead64 houtSinSize hshortSin (by simp)
        hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
        hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSinSolmTrue

set_option maxHeartbeats 0 in
theorem vowCageBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToMinHeal
      (fun {σ_sin} {evmDai} {evmFlap} {evmFlop} {evmDai2} {evmSin}
          {outDai} {outFlap} {outFlop} {outDai2} {outSin} {memSin}
          {k3234} {C3234} {flapperDai} {vatDai} {vatSin} rd3234 hmemSin
          hread64Sin hvatCode hcallDai hdecDai hauthSolm hliveSolm hflapperCode
          hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2
          hvatCodeSin hcallSin hdecSin hdepthLt hσ0Sin henvSin hAccountsSin => ?_)
      hcode hsize hperm hwv hsel
  have hownerSin : evmSin.executionEnv.codeOwner = I.codeOwner := by
    simp [henvSin]
  by_cases hle : vatDai.toNat ≤ vatSin.toNat
  · by_cases hcodeSizeHeal :
        Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) =
          ⟨0⟩
    · have hcodeSizeHealSolm :
          Reasoning.Theory.extCodeSizeWord evmSin.accountMap
              (kissDaiTargetWord evmSin.accountMap I) = ⟨0⟩ := by
        simpa only [← hAccountsSin] using hcodeSizeHeal
      have hvatNoCode :
          (UInt256.ofNat
            ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
              (fun acc => acc.code.size))).toNat = 0 :=
        cageVatCode_zero_of_codeSize_zero evmSin I hownerSin hcodeSizeHealSolm
      exact vowCageMinHealLeftNoCodeBodyCore (acc := σ_sin)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2) (evmSin := evmSin) (outDai := outDai)
        (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
        (outSin := outSin) (R := [⟨412⟩, vowSelWord I])
        hcode hwv hauthSolm hliveSolm hdispatch hdecode rd3234 hmemSin
        hread64Sin hcodeSizeHeal (by simp) hvatCode hcallDai hdecDai hflapperCode
        hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin
        hcallSin hdecSin hle hvatNoCode
    have hcodeSizeHealNE :
        Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) ≠
          ⟨0⟩ :=
      hcodeSizeHeal
    have hcodeSizeHealSolmNE :
        Reasoning.Theory.extCodeSizeWord evmSin.accountMap
            (kissDaiTargetWord evmSin.accountMap I) ≠ ⟨0⟩ := by
      simpa only [← hAccountsSin] using hcodeSizeHealNE
    have hvatCodeHeal :
        0 < (UInt256.ofNat
          ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
            (fun acc => acc.code.size))).toNat :=
      cageVatCode_pos_of_codeSize_ne evmSin I hownerSin hcodeSizeHealSolmNE
    obtain ⟨_, _, rd3238⟩ :=
      RD.vowCageMinReturnLeft rd3234 hle (by simp)
    obtain ⟨σ_heal, zHeal, outHeal, A_heal, k3296, C3296, rd3296,
        hcallHealEvmRaw, houtHealSize⟩ :=
      RD.vowCageHealPostCall
        (σCall := σ_sin)
        (healRad := vatDai) (R := [⟨412⟩, vowSelWord I])
        rd3238 hmemSin hread64Sin hcodeSizeHealNE hdepthLt hperm (by simp)
    let evmHealEvmIn :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_sin
      }
    let evmHealEvmOut :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_heal
        substate := A_heal
      }
    have hcallHealEvm :
        typedCallViaEVM config evmHealEvmIn (EVM.address (kissVatAddress σ_sin I))
          "heal" 0 [.int (Int.ofNat vatDai.toNat)]
          (zHeal, evmHealEvmOut, outHeal) true := by
      simpa [evmHealEvmIn, evmHealEvmOut] using hcallHealEvmRaw
    have hVatAddrMap : kissVatAddress σ_sin I = kissVatAddress evmSin.accountMap I :=
      congrArg (fun accounts => kissVatAddress accounts I) hAccountsSin
    have hVatAddrSolm : cageVatAddressOf evmSin = kissVatAddress evmSin.accountMap I :=
      cageVatAddressOf_eq_kissVatAddress evmSin I hownerSin
    have hVatTargetAddr :
        EVM.address (kissVatAddress σ_sin I) =
          EVM.address (cageVatAddressOf evmSin) := by
      rw [hVatAddrMap, ← hVatAddrSolm]
    have hVatTargetAddrSin :
        EVM.address (kissVatAddress σ_sin evmSin.executionEnv) =
          EVM.address (cageVatAddressOf evmSin) := by
      simpa [← henvSin] using hVatTargetAddr
    obtain ⟨σ_heal_solm, A_heal_solm0, hcallHealSolmBase, hAccountsHeal⟩ :=
      typedCallViaEVM_sameInputs (evm_solm := evmSin)
        hcallHealEvm hAccountsSin
        (by simpa [evmHealEvmIn, initState] using hσ0Sin.symm)
        (by simpa [evmHealEvmIn, initState] using henvSin.symm)
    let evmHealSolm :=
      { evmSin with
        accountMap := σ_heal_solm
        substate := A_heal_solm0
      }
    have hcallHealSolm :
        typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
          "heal" 0 [.int (Int.ofNat vatDai.toNat)]
          (zHeal, evmHealSolm, outHeal) true := by
      simpa [evmHealSolm, evmHealEvmOut, hVatTargetAddrSin,
        ← henvSin] using hcallHealSolmBase
    cases zHeal
    · exact vowCageMinHealLeftCallFailureBodyCore (acc := σ_heal)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHealSolm)
        (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
        (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
        (R := [⟨412⟩, vowSelWord I])
        hcode hwv hauthSolm hliveSolm hdispatch hdecode (by simpa using rd3296)
        houtHealSize (by simp) hvatCode hcallDai hdecDai hflapperCode hcallFlap
        hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin
        hdecSin hle hvatCodeHeal (by simpa using hcallHealSolm)
    · have hcallHealSolmTrue :
          typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
            "heal" 0 [.int (Int.ofNat vatDai.toNat)]
            (true, evmHealSolm, outHeal) true := by
        simpa using hcallHealSolm
      exact vowCageMinHealLeftSuccessBodyCore (acc := σ_heal)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHealSolm)
        (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
        (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
        (sel := vowSelWord I)
        hcode hwv hauthSolm hliveSolm hdispatch hdecode (by simpa using rd3296)
        hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
        hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin hdecSin hle
        hvatCodeHeal hcallHealSolmTrue
        (by simpa [evmHealEvmOut, evmHealSolm] using hAccountsHeal)
  · have hlt : vatSin.toNat < vatDai.toNat := by
      omega
    by_cases hcodeSizeHeal :
        Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) =
          ⟨0⟩
    · have hcodeSizeHealSolm :
          Reasoning.Theory.extCodeSizeWord evmSin.accountMap
              (kissDaiTargetWord evmSin.accountMap I) = ⟨0⟩ := by
        simpa only [← hAccountsSin] using hcodeSizeHeal
      have hvatNoCode :
          (UInt256.ofNat
            ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
              (fun acc => acc.code.size))).toNat = 0 :=
        cageVatCode_zero_of_codeSize_zero evmSin I hownerSin hcodeSizeHealSolm
      exact vowCageMinHealRightNoCodeBodyCore (acc := σ_sin)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2) (evmSin := evmSin) (outDai := outDai)
        (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
        (outSin := outSin) (R := [⟨412⟩, vowSelWord I])
        hcode hwv hauthSolm hliveSolm hdispatch hdecode rd3234 hmemSin
        hread64Sin hcodeSizeHeal (by simp) hvatCode hcallDai hdecDai hflapperCode
        hcallFlap hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin
        hcallSin hdecSin hlt hvatNoCode
    have hcodeSizeHealNE :
        Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) ≠
          ⟨0⟩ :=
      hcodeSizeHeal
    have hcodeSizeHealSolmNE :
        Reasoning.Theory.extCodeSizeWord evmSin.accountMap
            (kissDaiTargetWord evmSin.accountMap I) ≠ ⟨0⟩ := by
      simpa only [← hAccountsSin] using hcodeSizeHealNE
    have hvatCodeHeal :
        0 < (UInt256.ofNat
          ((evmSin.lookupAccount (cageVatAddressOf evmSin)).option 0
            (fun acc => acc.code.size))).toNat :=
      cageVatCode_pos_of_codeSize_ne evmSin I hownerSin hcodeSizeHealSolmNE
    obtain ⟨_, _, rd3238⟩ :=
      RD.vowCageMinReturnRight rd3234 hlt (by simp)
    obtain ⟨σ_heal, zHeal, outHeal, A_heal, k3296, C3296, rd3296,
        hcallHealEvmRaw, houtHealSize⟩ :=
      RD.vowCageHealPostCall
        (σCall := σ_sin)
        (healRad := vatSin) (R := [⟨412⟩, vowSelWord I])
        rd3238 hmemSin hread64Sin hcodeSizeHealNE hdepthLt hperm (by simp)
    let evmHealEvmIn :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_sin
      }
    let evmHealEvmOut :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_heal
        substate := A_heal
      }
    have hcallHealEvm :
        typedCallViaEVM config evmHealEvmIn (EVM.address (kissVatAddress σ_sin I))
          "heal" 0 [.int (Int.ofNat vatSin.toNat)]
          (zHeal, evmHealEvmOut, outHeal) true := by
      simpa [evmHealEvmIn, evmHealEvmOut] using hcallHealEvmRaw
    have hVatAddrMap : kissVatAddress σ_sin I = kissVatAddress evmSin.accountMap I :=
      congrArg (fun accounts => kissVatAddress accounts I) hAccountsSin
    have hVatAddrSolm : cageVatAddressOf evmSin = kissVatAddress evmSin.accountMap I :=
      cageVatAddressOf_eq_kissVatAddress evmSin I hownerSin
    have hVatTargetAddr :
        EVM.address (kissVatAddress σ_sin I) =
          EVM.address (cageVatAddressOf evmSin) := by
      rw [hVatAddrMap, ← hVatAddrSolm]
    have hVatTargetAddrSin :
        EVM.address (kissVatAddress σ_sin evmSin.executionEnv) =
          EVM.address (cageVatAddressOf evmSin) := by
      simpa [← henvSin] using hVatTargetAddr
    obtain ⟨σ_heal_solm, A_heal_solm0, hcallHealSolmBase, hAccountsHeal⟩ :=
      typedCallViaEVM_sameInputs (evm_solm := evmSin)
        hcallHealEvm hAccountsSin
        (by simpa [evmHealEvmIn, initState] using hσ0Sin.symm)
        (by simpa [evmHealEvmIn, initState] using henvSin.symm)
    let evmHealSolm :=
      { evmSin with
        accountMap := σ_heal_solm
        substate := A_heal_solm0
      }
    have hcallHealSolm :
        typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
          "heal" 0 [.int (Int.ofNat vatSin.toNat)]
          (zHeal, evmHealSolm, outHeal) true := by
      simpa [evmHealSolm, evmHealEvmOut, hVatTargetAddrSin,
        ← henvSin] using hcallHealSolmBase
    cases zHeal
    · exact vowCageMinHealRightCallFailureBodyCore (acc := σ_heal)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHealSolm)
        (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
        (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
        (R := [⟨412⟩, vowSelWord I])
        hcode hwv hauthSolm hliveSolm hdispatch hdecode (by simpa using rd3296)
        houtHealSize (by simp) hvatCode hcallDai hdecDai hflapperCode hcallFlap
        hflopperCode hcallFlop hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin
        hdecSin hlt hvatCodeHeal (by simpa using hcallHealSolm)
    · have hcallHealSolmTrue :
          typedCallViaEVM config evmSin (EVM.address (cageVatAddressOf evmSin))
            "heal" 0 [.int (Int.ofNat vatSin.toNat)]
            (true, evmHealSolm, outHeal) true := by
        simpa using hcallHealSolm
      exact vowCageMinHealRightSuccessBodyCore (acc := σ_heal)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2) (evmSin := evmSin) (evmHeal := evmHealSolm)
        (outDai := outDai) (outFlap := outFlap) (outFlop := outFlop)
        (outDai2 := outDai2) (outSin := outSin) (outHeal := outHeal)
        (sel := vowSelWord I)
        hcode hwv hauthSolm hliveSolm hdispatch hdecode (by simpa using rd3296)
        hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
        hvatCode2 hcallDai2 hdecDai2 hvatCodeSin hcallSin hdecSin hlt
        hvatCodeHeal hcallHealSolmTrue
        (by simpa [evmHealEvmOut, evmHealSolm] using hAccountsHeal)

end Benchmarks.Dss.Vow

import Reasoning.Storage
import Benchmarks.Dss.Vow.CageHealRuntime

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` top-level runtime wrapper helpers -/


theorem cageFlapperAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (solcAddressSlotWord ⟨2⟩ σ I).toNat) =
      AccountAddress.ofUInt256 (solcAddressSlotWord ⟨2⟩ σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simp [EVM.twoPow, AccountAddress.size])

theorem cageFlopperAddressOf_eq_vowAddressReturnWord (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    flopFlopperAddressOf evm =
      AccountAddress.ofUInt256 (solcAddressSlotWord ⟨3⟩ evm.accountMap I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [flopFlopperAddressOf, solcAddressSlotWord,
    storageLoad_codeOwner_eq_solcSlotWordAt evm I ⟨3⟩ howner]

theorem cageFlopperCode_pos_of_codeSize_ne (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (solcAddressSlotWord ⟨3⟩ evm.accountMap I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := solcAddressSlotWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (cageFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hne

theorem cageFlopperCode_zero_of_codeSize_zero (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (solcAddressSlotWord ⟨3⟩ evm.accountMap I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := solcAddressSlotWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (cageFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hzero

theorem cageVatAddressOf_eq_kissVatAddress (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    cageVatAddressOf evm = kissVatAddress evm.accountMap I := by
  have hload :
      Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ =
        solcSlotWordAt ⟨1⟩ evm.accountMap I := by
    simpa [howner] using storageLoad_codeOwner_eq_solcSlotWordAt evm I ⟨1⟩ howner
  simp only [cageVatAddressOf, kissVatAddress, solcAddressSlotWord]
  rw [hload]

theorem cageVatCode_pos_of_codeSize_ne (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hne : Reasoning.Theory.extCodeSizeWord evm.accountMap
        (kissDaiTargetWord evm.accountMap I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (cageVatAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat := by
  have haddr :
      cageVatAddressOf evm = AccountAddress.ofUInt256 (kissDaiTargetWord evm.accountMap I) :=
    (cageVatAddressOf_eq_kissVatAddress evm I howner).trans
      (kissVatAddress_eq_daiTarget_account evm.accountMap I)
  simpa [State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := kissDaiTargetWord evm.accountMap I)
      (addr := cageVatAddressOf evm) haddr hne

theorem cageVatCode_zero_of_codeSize_zero (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero : Reasoning.Theory.extCodeSizeWord evm.accountMap
        (kissDaiTargetWord evm.accountMap I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (cageVatAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  have haddr :
      cageVatAddressOf evm = AccountAddress.ofUInt256 (kissDaiTargetWord evm.accountMap I) :=
    (cageVatAddressOf_eq_kissVatAddress evm I howner).trans
      (kissVatAddress_eq_daiTarget_account evm.accountMap I)
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := kissDaiTargetWord evm.accountMap I)
      (addr := cageVatAddressOf evm) haddr hzero

theorem RD.vowCageFirstDaiCallDepthLimit
    {σ σCall σ₀ A I} {g ret : UInt256}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    (rd : RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2669⟩
      (solcSlotWord σCall I ⟨1⟩ :: solcSlotWord σCall I ⟨2⟩ :: ret :: R)
      mem (UInt256.ofNat 3) rdata σCall k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (kissDaiTargetWord σCall I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σCall I ::
        ⟨2734234354⟩ :: solcAddressSlotWord ⟨2⟩ σCall I :: ret :: R)
      (vatDaiCalldataMemFor (solcAddressSlotWord ⟨2⟩ σCall I) mem)
      (UInt256.ofNat 6) ByteArray.empty σCall k' C' := by
  have hcodeSizeRaw :
      Reasoning.Theory.extCodeSizeWord σCall
        (UInt256.land solcAddrMask (solcSlotWord σCall I ⟨1⟩)) ≠ ⟨0⟩ := by
    simpa [kissDaiTargetWord, solcSlotWordAt, solcSlotWord, u256_land_comm] using hcodeSize
  obtain ⟨_, _, _, rd2753⟩ :=
    RD.vowCageFirstDaiStaticcallSetup rd hmem hread64 hcodeSizeRaw hov
  obtain ⟨k2754, C2754, rd2754raw⟩ :=
    RD.solcStaticcallDepthLimit rd2753 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    native_decide
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd2754 : RD fork vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σCall I ⟨1⟩) :: ⟨2734234354⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σCall I ⟨2⟩) :: ret :: R)
      (ByteArray.empty.write 0
        (vatDaiCalldataMemFor
          (UInt256.land solcAddrMask (solcSlotWord σCall I ⟨2⟩)) mem)
        128 (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty σCall k2754 C2754 :=
    haw ▸ rd2754raw
  rw [hmin, byteArray_write_len_zero] at rd2754
  exact ⟨k2754, C2754, by
    simpa [kissDaiTargetWord, solcAddressSlotWord, solcSlotWordAt, solcSlotWord,
      u256_land_comm] using rd2754⟩

theorem vowCageFirstDaiCallDepthLimitBody
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hauthEvm : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hliveEvm : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord
        (vowCageClearedAccountMap I.codeOwner σ)
        (kissDaiTargetWord (vowCageClearedAccountMap I.codeOwner σ) I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let σClearedEvm := vowCageClearedAccountMap I.codeOwner σ
  let σClearedStele := vowCageClearedAccountMap I.codeOwner σ
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hdecode :
      config.externalABI.decodeCalldata? (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, rdClear⟩ :=
    vowCageReachAfterClear (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hauthEvm hliveEvm
  obtain ⟨_, _, rdLoads⟩ :=
    RD.vowCageFirstDaiLoadTargets (R := [vowSelWord I]) rdClear (by simp)
  obtain ⟨_, _, rd2754⟩ :=
    RD.vowCageFirstDaiCallDepthLimit
      (σCall := σClearedEvm) (ret := ⟨412⟩) (R := [vowSelWord I])
      rdLoads hmemAuth hread64 (by simpa [σClearedEvm] using hcodeSize) hdepth
      (by simp)
  have hauthStele : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩ := hauthEvm
  have hliveStele : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ := hliveEvm
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σClearedStele
        (kissDaiTargetWord σClearedStele I) ≠ ⟨0⟩ := by
    simpa [σClearedStele, σClearedEvm] using hcodeSize
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hownerAsh : evmAsh.executionEnv.codeOwner = I.codeOwner := by
    simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
  have haddrCage :
      cageVatAddressOf evmAsh = kissVatAddress σClearedStele I := by
    have hload :
        Stele.EVM.storageLoad evmAsh I.codeOwner ⟨1⟩ =
          solcSlotWordAt ⟨1⟩ evmAsh.accountMap I := by
      simpa [hownerAsh] using
        storageLoad_codeOwner_eq_solcSlotWordAt evmAsh I ⟨1⟩ hownerAsh
    simp only [cageVatAddressOf, kissVatAddress, solcAddressSlotWord]
    rw [hownerAsh, hload]
    simp [
      σClearedStele, evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
      vowCageClearedAccountMap]
  have haddr :
      cageVatAddressOf evmAsh = AccountAddress.ofUInt256 (kissDaiTargetWord σClearedStele I) :=
    haddrCage.trans (kissVatAddress_eq_daiTarget_account σClearedStele I)
  have hvatCode :
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat := by
    have hpos :=
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σClearedStele) (target := kissDaiTargetWord σClearedStele I)
        (addr := cageVatAddressOf evmAsh) haddr hcodeSizeStele
    simpa [evmAsh, evmSin, evmLive, evm0, initState, State.lookupAccount,
      storageStore_accountMap, σClearedStele, vowCageClearedAccountMap] using hpos
  have hflapperArg :
      flapFlapperAddressOf evmAsh =
        AccountAddress.ofNat (solcAddressSlotWord ⟨2⟩ σClearedStele I).toNat := by
    have hslot :
        solcAddressSlotWord ⟨2⟩ evmAsh.accountMap I =
          solcAddressSlotWord ⟨2⟩ σClearedStele I := by
      simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
        σClearedStele, vowCageClearedAccountMap]
    rw [flapFlapperAddressOf_eq_vowAddressReturnWord evmAsh I hownerAsh, hslot,
      accountAddress_ofUInt256_eq_ofNat_toNat]
  let A_dai := (Ethereum.EVM.callSubstate fork evmAsh.accountMap (EVM.address
    (cageVatAddressOf evmAsh)) evmAsh.substate)
  have hcallDai :
      typedCallViaEVM fork config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)]
        (false, { evmAsh with substate := A_dai }, ByteArray.empty) false := by
    have henc :
        config.externalABI.encode? "dai" [.address (flapFlapperAddressOf evmAsh)] =
          some ((vatDaiCalldataMemFor (solcAddressSlotWord ⟨2⟩ σClearedStele I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).readWithPadding 128 36) := by
      rw [hflapperArg]
      simpa [solcAddressSlotWord, solcSlotWordAt, solcSlotWord, u256_land_comm] using
        vatDaiEncodeMasked_eq_of_size96 (solcSlotWord σClearedStele I ⟨2⟩) hmemAuth
    simpa [A_dai, evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
      using
        (callNotMade_depthLimit (cfg := config) (evm := evmAsh)
          (tgt := EVM.address (cageVatAddressOf evmAsh)) (name := "dai")
          (args := [.address (flapFlapperAddressOf evmAsh)]) (callPerm := false)
          henc
          (by
            simpa [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
              using hdepth))
  exact vowCageFirstDaiCallFailureBodyCore (hperm := hperm) (acc := σClearedEvm)
    (evmDai := { evmAsh with substate := A_dai }) (outDai := ByteArray.empty)
    hcode hwv hauthStele hliveStele hdispatch hdecode
    (by simpa [σClearedEvm] using rd2754)
    (by native_decide) (by simp) hvatCode hcallDai

set_option maxHeartbeats 0 in
theorem vowCageBodyToFlapperCage
    {σ σ₀ A I} {g : UInt256}
    (cont : I.perm = true →
      ∀ {σ_dai : AccountMap}
        {evmDai : EVM.State} {outDai memDai : ByteArray} {k2795 C2795 : ℕ}
        {flapperDai : UInt256},
        RD fork vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2795⟩
          (flapperDai :: flapCageSelectorWord ::
            solcAddressSlotWord ⟨2⟩ (vowCageClearedAccountMap I.codeOwner σ) I ::
            ⟨412⟩ :: vowSelWord I :: [])
          memDai (UInt256.ofNat 6) outDai σ_dai k2795 C2795 →
        memDai.size = 164 →
        memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM fork config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
          config.externalABI.decode? "dai" outDai =
            some [.int (Int.ofNat flapperDai.toNat)] →
          solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩ →
          solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ →
          I.depth.val < 1024 →
        evmDai.σ₀ = σ₀ →
        evmDai.executionEnv = I →
        Eq σ_dai evmDai.accountMap →
        runtimeRefinementFor fork config contract σ σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  by_cases hauthEvm : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩
  · by_cases hliveEvm : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩
    · let σClearedEvm := vowCageClearedAccountMap I.codeOwner σ
      let σClearedStele := vowCageClearedAccountMap I.codeOwner σ
      have hsz : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
      have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
        vowDispatch_cage hsel
      have hdecode :
          config.externalABI.decodeCalldata? (cageTransition.params.map Param.name)
            (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
        vowDecode_cage hsz
      rcases vowCageReachAfterClearSplit (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hwv hsel hauthEvm hliveEvm with ⟨hperm, -⟩ | ⟨hpf, hstatic⟩
      swap
      · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode
          ((vowCageSourceClearPrefixSplit (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthEvm hliveEvm).2 hpf)
      by_cases hcodeSizeFirst :
          Reasoning.Theory.extCodeSizeWord σClearedEvm
              (kissDaiTargetWord σClearedEvm I) =
            ⟨0⟩
      · exact vowCageFirstDaiNoCodeBodyCore hcode hsize hperm hwv hsel
          hauthEvm hliveEvm (by simpa [σClearedEvm] using hcodeSizeFirst)
      have hcodeSizeFirstNE :
          Reasoning.Theory.extCodeSizeWord σClearedEvm
              (kissDaiTargetWord σClearedEvm I) ≠
            ⟨0⟩ :=
        hcodeSizeFirst
      by_cases hdepthLt : I.depth.val < 1024
      · have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        obtain ⟨_, _, rdClear⟩ :=
          vowCageReachAfterClear (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hauthEvm hliveEvm
        obtain ⟨_, _, rdLoads⟩ :=
          RD.vowCageFirstDaiLoadTargets (R := [vowSelWord I]) rdClear (by simp)
        obtain ⟨σ_dai, zDai, outDai, A_dai, k2754, C2754, rd2754,
            hcallDaiEvmRaw, houtDaiSize⟩ :=
          RD.vowCageFirstDaiStaticcall
            (σCall := σClearedEvm) (ret := ⟨412⟩) (R := [vowSelWord I])
            rdLoads hmemAuth hread64 (by simpa [σClearedEvm] using hcodeSizeFirstNE)
            hdepthLt (by simp)
        have hauthStele : solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩ := hauthEvm
        have hliveStele : solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ := hliveEvm
        have hClearedAccounts : Eq σClearedEvm σClearedStele := rfl
        have hTargetCleared :
            kissDaiTargetWord σClearedEvm I = kissDaiTargetWord σClearedStele I := by
          exact congrArg (fun accounts => kissDaiTargetWord accounts I) hClearedAccounts
        have hFlapperCleared :
            solcAddressSlotWord ⟨2⟩ σClearedEvm I =
              solcAddressSlotWord ⟨2⟩ σClearedStele I := by
          exact congrArg (fun accounts => solcAddressSlotWord ⟨2⟩ accounts I)
            hClearedAccounts
        have hcodeSizeStele :
            Reasoning.Theory.extCodeSizeWord σClearedStele
              (kissDaiTargetWord σClearedStele I) ≠ ⟨0⟩ := by
          simpa [hClearedAccounts] using hcodeSizeFirstNE
        let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
        let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
        let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
        have hownerAsh : evmAsh.executionEnv.codeOwner = I.codeOwner := by
          simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
        have haddrCage :
            cageVatAddressOf evmAsh = kissVatAddress σClearedStele I := by
          have hload :
              Stele.EVM.storageLoad evmAsh I.codeOwner ⟨1⟩ =
                solcSlotWordAt ⟨1⟩ evmAsh.accountMap I := by
            simpa [hownerAsh] using
              storageLoad_codeOwner_eq_solcSlotWordAt evmAsh I ⟨1⟩ hownerAsh
          simp only [cageVatAddressOf, kissVatAddress, solcAddressSlotWord]
          rw [hownerAsh, hload]
          simp [
            σClearedStele, evmAsh, evmSin, evmLive, evm0, initState,
            storageStore_accountMap, vowCageClearedAccountMap]
        have hVatAddrCleared :
            kissVatAddress σClearedEvm I = kissVatAddress σClearedStele I := by
          apply Fin.ext
          simp [kissVatAddress, solcAddressSlotWord, hTargetCleared]
        have hVatTarget :
            EVM.address (kissVatAddress σClearedEvm I) =
              EVM.address (cageVatAddressOf evmAsh) := by
          rw [hVatAddrCleared, haddrCage]
        have haddr :
            cageVatAddressOf evmAsh =
              AccountAddress.ofUInt256 (kissDaiTargetWord σClearedStele I) :=
          haddrCage.trans (kissVatAddress_eq_daiTarget_account σClearedStele I)
        have hvatCode :
            0 < (UInt256.ofNat
              ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
                (fun acc => acc.code.size))).toNat := by
          have hpos :=
            extCodeSizeWord_ne_zero_lookup_code_pos
              (σ := σClearedStele) (target := kissDaiTargetWord σClearedStele I)
              (addr := cageVatAddressOf evmAsh) haddr hcodeSizeStele
          simpa [evmAsh, evmSin, evmLive, evm0, initState, State.lookupAccount,
            storageStore_accountMap, σClearedStele, vowCageClearedAccountMap] using hpos
        have hflapperArg :
            flapFlapperAddressOf evmAsh =
              AccountAddress.ofNat (solcAddressSlotWord ⟨2⟩ σClearedStele I).toNat := by
          have hslot :
              solcAddressSlotWord ⟨2⟩ evmAsh.accountMap I =
                solcAddressSlotWord ⟨2⟩ σClearedStele I := by
            simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
              σClearedStele, vowCageClearedAccountMap]
          rw [flapFlapperAddressOf_eq_vowAddressReturnWord evmAsh I hownerAsh, hslot,
            accountAddress_ofUInt256_eq_ofNat_toNat]
        let evmDaiEvmIn :=
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σClearedEvm }
        let evmDaiEvmOut :=
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_dai
            substate := A_dai
          }
        have hcallDaiEvm :
            typedCallViaEVM fork config evmDaiEvmIn (EVM.address (kissVatAddress σClearedEvm I))
              "dai" 0 [.address (AccountAddress.ofNat
                (solcAddressSlotWord ⟨2⟩ σClearedEvm I).toNat)]
              (zDai, evmDaiEvmOut, outDai) false := by
          simpa [evmDaiEvmIn, evmDaiEvmOut] using hcallDaiEvmRaw
        have hDaiTargetPostEvm :
            kissDaiTargetWord σ_dai I = kissDaiTargetWord σClearedEvm I := by
          have hslot :=
            typedCallViaEVM_static_storage_getD_of_accounts_eq
              (cfg := config) (σ := σClearedEvm) (evm := evmDaiEvmIn)
              (evm' := evmDaiEvmOut) (target := EVM.address (kissVatAddress σClearedEvm I))
              (name := "dai")
              (args := [.address (AccountAddress.ofNat
                (solcAddressSlotWord ⟨2⟩ σClearedEvm I).toNat)])
              (z := zDai) (out := outDai) (slot := ⟨1⟩) (default := ⟨0⟩)
              (by simp [evmDaiEvmIn])
              hcallDaiEvm
          simpa [kissDaiTargetWord, solcSlotWordAt, solcSlotWord, evmDaiEvmIn,
            evmDaiEvmOut, initState] using
            congrArg (fun word => UInt256.land word solcAddrMask) hslot
        obtain ⟨σ_dai_stele, A_dai_stele, hcallDaiSteleRaw, hAccountsDai⟩ :=
          typedCallViaEVM_sameInputs (evm_stele := evmAsh)
            hcallDaiEvm (by
              simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_accountMap, σClearedEvm, σClearedStele,
                vowCageClearedAccountMap])
            (by simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState, storageStore_σ₀])
            (by simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv])
        let evmDaiStele :=
          { evmAsh with
            accountMap := σ_dai_stele
            substate := A_dai_stele
          }
        have hcallDaiStele :
            typedCallViaEVM fork config evmAsh (EVM.address (cageVatAddressOf evmAsh))
              "dai" 0 [.address (flapFlapperAddressOf evmAsh)]
              (zDai, evmDaiStele, outDai) false := by
          simpa [evmDaiStele, hVatTarget, hflapperArg, hFlapperCleared] using
            hcallDaiSteleRaw
        cases zDai
        · exact vowCageFirstDaiCallFailureBodyCore (hperm := hperm) (acc := σ_dai)
            (evmDai := evmDaiStele) (outDai := outDai)
            hcode hwv hauthStele hliveStele hdispatch hdecode
            (by simpa using rd2754) houtDaiSize (by simp) hvatCode
            (by simpa using hcallDaiStele)
        · have rd2754True : RD fork vowBytecode I (Sat256.ofUInt256 g)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
              (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σClearedEvm I ::
                flapCageSelectorWord :: solcAddressSlotWord ⟨2⟩ σClearedEvm I ::
                ⟨412⟩ :: vowSelWord I :: [])
              (outDai.write 0
                (vatDaiCalldataMemFor (solcAddressSlotWord ⟨2⟩ σClearedEvm I)
                  (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
                128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
              (UInt256.ofNat 6) outDai σ_dai k2754 C2754 := by
            simpa [σClearedEvm] using rd2754
          have hcallDaiSteleTrue :
              typedCallViaEVM fork config evmAsh (EVM.address (cageVatAddressOf evmAsh))
                "dai" 0 [.address (flapFlapperAddressOf evmAsh)]
                (true, evmDaiStele, outDai) false := by
            simpa using hcallDaiStele
          have rd2754TruePost : RD fork vowBytecode I (Sat256.ofUInt256 g)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
              (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σ_dai I ::
                flapCageSelectorWord :: solcAddressSlotWord ⟨2⟩ σClearedEvm I ::
                ⟨412⟩ :: vowSelWord I :: [])
              (outDai.write 0
                (vatDaiCalldataMemFor (solcAddressSlotWord ⟨2⟩ σClearedEvm I)
                  (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
                128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
              (UInt256.ofNat 6) outDai σ_dai k2754 C2754 := by
            simpa [hDaiTargetPostEvm] using rd2754True
          let baseDai :=
            vatDaiCalldataMemFor (solcAddressSlotWord ⟨2⟩ σClearedEvm I)
              (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
          have hbaseDai : baseDai.size = 164 := by
            simpa [baseDai] using
              vatDaiCalldataMemFor_size_of_size96
                (solcAddressSlotWord ⟨2⟩ σClearedEvm I) hmemAuth
          have hbaseDaiRead64 :
              baseDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
            simpa [baseDai] using
              vatDaiCalldataMemFor_read64_of_size96
                (solcAddressSlotWord ⟨2⟩ σClearedEvm I) hmemAuth hread64
          by_cases ho32Dai : 32 ≤ outDai.size
          · let flapperDai : UInt256 :=
              UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32))
            obtain ⟨_, _, rd2795⟩ :=
              RD.vowCageFirstDaiPostCallDecodeOk
                (acc := σ_dai)
                (mem := twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
                (target := solcAddressSlotWord ⟨2⟩ σClearedEvm I)
                (ret := ⟨412⟩) (R := [vowSelWord I])
                rd2754TruePost hmemAuth hread64 ho32Dai houtDaiSize (by simp)
            let memDai := outDai.write 0 baseDai 128 32
            have hmemDai : memDai.size = 164 := by
              simpa [memDai] using returnWrite_size_164 outDai 32 hbaseDai
                (by omega) ho32Dai
            have hread64Dai :
                memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
              simpa [memDai] using returnWrite_read64 outDai 32 hbaseDai
                hbaseDaiRead64 (by omega) ho32Dai
            have hdecDai :
                config.externalABI.decode? "dai" outDai =
                  some [.int (Int.ofNat flapperDai.toNat)] := by
              simpa [flapperDai] using kissDaiDecode_ok (o := outDai) ho32Dai
            have hσ0Dai : evmDaiStele.σ₀ = σ₀ := by
              simp [evmDaiStele, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_σ₀]
            have henvDai : evmDaiStele.executionEnv = I := by
              simp [evmDaiStele, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_executionEnv]
            exact cont hperm (evmDai := evmDaiStele) (outDai := outDai)
              (memDai := memDai) (flapperDai := flapperDai)
                (by simpa [memDai, baseDai, flapperDai, σClearedEvm] using rd2795)
                hmemDai hread64Dai hvatCode hcallDaiSteleTrue hdecDai hauthStele hliveStele hdepthLt hσ0Dai henvDai
                (by simpa [evmDaiEvmOut, evmDaiStele] using hAccountsDai)
          · have hshortDai : outDai.size < 32 := Nat.lt_of_not_ge ho32Dai
            exact vowCageFirstDaiDecodeShortBodyCore (hperm := hperm) (acc := σ_dai)
              (evmDai := evmDaiStele) (base := baseDai) (outDai := outDai)
              hcode hwv hauthStele hliveStele hdispatch hdecode rd2754True
              hbaseDai hbaseDaiRead64 houtDaiSize hshortDai (by simp)
              hvatCode hcallDaiSteleTrue
      · have hdepthEq : I.depth = 1024 := by
          apply Fin.ext
          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
          omega
        exact vowCageFirstDaiCallDepthLimitBody hcode hsize hperm hwv hsel
          hauthEvm hliveEvm (by simpa [σClearedEvm] using hcodeSizeFirstNE) hdepthEq
    · exact vowCageLiveRevert hcode hsize hwv hsel hauthEvm hliveEvm
  · exact vowCageAuthRevert hcode hsize hwv hsel hauthEvm

set_option maxHeartbeats 0 in
theorem vowCageBodyToFlopperCage
    {σ σ₀ A I} {g : UInt256}
    (cont : I.perm = true →
      ∀ {σ_flap : AccountMap}
        {evmDai evmFlap : EVM.State} {outDai outFlap memFlap : ByteArray}
        {k2881 C2881 : ℕ} {flapperDai : UInt256},
        RD fork vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2881⟩
          (⟨412⟩ :: vowSelWord I :: [])
          memFlap (UInt256.ofNat 6) outFlap σ_flap k2881 C2881 →
        memFlap.size = 164 →
        memFlap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM fork config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
          config.externalABI.decode? "dai" outDai =
            some [.int (Int.ofNat flapperDai.toNat)] →
          solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩ →
          solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ →
          0 < (UInt256.ofNat
          ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM fork config evmDai (EVM.address (flapFlapperAddressOf evmDai))
          "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
          true →
        I.depth.val < 1024 →
        evmFlap.σ₀ = σ₀ →
        evmFlap.executionEnv = I →
        Eq σ_flap evmFlap.accountMap →
        runtimeRefinementFor fork config contract σ σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let σClearedEvm := vowCageClearedAccountMap I.codeOwner σ
  let σClearedStele := vowCageClearedAccountMap I.codeOwner σ
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      config.externalABI.decodeCalldata? (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToFlapperCage
      (fun hperm {σ_dai} {evmDai} {outDai} {memDai} {k2795} {C2795}
          {flapperDai} rd2795 hmemDai hread64Dai hvatCode hcallDai hdecDai
          hauthStele hliveStele hdepthLt hσ0Dai henvDai hAccountsDai => ?_)
      hcode hsize hwv hsel
  have hClearedAccounts : Eq σClearedEvm σClearedStele := rfl
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hownerAsh : evmAsh.executionEnv.codeOwner = I.codeOwner := by
    simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
  have hslotFlapperStatic :
      solcAddressSlotWord ⟨2⟩ evmDai.accountMap I =
        solcAddressSlotWord ⟨2⟩ σClearedStele I := by
    have hslot :=
      typedCallViaEVM_static_storage_getD_of_accounts_eq
        (cfg := config) (σ := σClearedStele) (evm := evmAsh) (evm' := evmDai)
        (target := EVM.address (cageVatAddressOf evmAsh)) (name := "dai")
        (args := [.address (flapFlapperAddressOf evmAsh)]) (z := true)
        (out := outDai) (slot := ⟨2⟩) (default := ⟨0⟩)
        (by
          simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
            σClearedStele, vowCageClearedAccountMap])
        (by simpa [evmAsh, evmSin, evmLive, evm0] using hcallDai)
    simpa [solcAddressSlotWord, solcSlotWordAt, solcSlotWord, henvDai, hownerAsh] using
      congrArg (fun word => UInt256.land word solcAddrMask) hslot
  have hflapperTarget :
      solcAddressSlotWord ⟨2⟩ σ_dai I =
        solcAddressSlotWord ⟨2⟩ σClearedEvm I := by
    calc
      solcAddressSlotWord ⟨2⟩ σ_dai I =
          solcAddressSlotWord ⟨2⟩ evmDai.accountMap I :=
        congrArg (fun accounts => solcAddressSlotWord ⟨2⟩ accounts I) hAccountsDai
      _ = solcAddressSlotWord ⟨2⟩ σClearedStele I := hslotFlapperStatic
      _ = solcAddressSlotWord ⟨2⟩ σClearedEvm I :=
        (congrArg (fun accounts => solcAddressSlotWord ⟨2⟩ accounts I)
          hClearedAccounts).symm
  by_cases hcodeSizeFlapper :
      Reasoning.Theory.extCodeSizeWord σ_dai
        (solcAddressSlotWord ⟨2⟩ σClearedEvm I) = ⟨0⟩
  · have hcodeSizeFlapperDai :
        Reasoning.Theory.extCodeSizeWord σ_dai
            (solcAddressSlotWord ⟨2⟩ σ_dai I) = ⟨0⟩ := by
      simpa [hflapperTarget] using hcodeSizeFlapper
    have hcodeSizeFlapperStele :
        Reasoning.Theory.extCodeSizeWord evmDai.accountMap
            (solcAddressSlotWord ⟨2⟩ evmDai.accountMap I) = ⟨0⟩ := by
      simpa only [← hAccountsDai] using hcodeSizeFlapperDai
    have hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner := by
      simp [henvDai]
    have hflapperNoCode :
        (UInt256.ofNat
          ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      flapFlapperCode_zero_of_codeSize_zero evmDai I hownerDai hcodeSizeFlapperStele
    exact vowCageFlapperCageNoCodeBodyCore (hperm := hperm) (acc := σ_dai)
      (evmDai := evmDai) (target := solcAddressSlotWord ⟨2⟩ σClearedEvm I)
      (ret := ⟨412⟩) (R := [vowSelWord I])
      hcode hwv hauthStele hliveStele hdispatch hdecode
      (by simpa [hflapperTarget] using rd2795) hmemDai hread64Dai
      hcodeSizeFlapper (by simp) hvatCode hcallDai hdecDai hflapperNoCode
  have hcodeSizeFlapperNE :
      Reasoning.Theory.extCodeSizeWord σ_dai
        (solcAddressSlotWord ⟨2⟩ σClearedEvm I) ≠ ⟨0⟩ :=
    hcodeSizeFlapper
  have hcodeSizeFlapperDaiNE :
      Reasoning.Theory.extCodeSizeWord σ_dai
          (solcAddressSlotWord ⟨2⟩ σ_dai I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeFlapperNE
    simpa [hflapperTarget] using hzero
  have hcodeSizeFlapperSteleNE :
      Reasoning.Theory.extCodeSizeWord evmDai.accountMap
          (solcAddressSlotWord ⟨2⟩ evmDai.accountMap I) ≠ ⟨0⟩ := by
    simpa only [← hAccountsDai] using hcodeSizeFlapperDaiNE
  have hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner := by
    simp [henvDai]
  have hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat :=
    flapFlapperCode_pos_of_codeSize_ne evmDai I hownerDai hcodeSizeFlapperSteleNE
  obtain ⟨σ_flap, zFlap, outFlap, A_flap, k2860, C2860, rd2860,
      hcallFlapEvmRaw, houtFlapSize⟩ :=
    RD.vowCageFlapperCageCall
      (σCall := σ_dai)
      (target := solcAddressSlotWord ⟨2⟩ σClearedEvm I)
      (R := [⟨412⟩, vowSelWord I])
      rd2795 hmemDai hread64Dai hcodeSizeFlapperNE hdepthLt
      (cageFlapperAddress_eq_target σClearedEvm I)
      (by simp)
  let evmFlapEvmIn :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_dai
    }
  let evmFlapEvmOut :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flap
      substate := A_flap
    }
  have hFlapperAddr :
      flapFlapperAddressOf evmDai =
        AccountAddress.ofUInt256 (solcAddressSlotWord ⟨2⟩ evmDai.accountMap I) :=
    flapFlapperAddressOf_eq_vowAddressReturnWord evmDai I hownerDai
  have hFlapperTargetAddr :
      EVM.address (AccountAddress.ofNat (solcAddressSlotWord ⟨2⟩ σClearedEvm I).toNat) =
        EVM.address (flapFlapperAddressOf evmDai) := by
    calc
      EVM.address (AccountAddress.ofNat (solcAddressSlotWord ⟨2⟩ σClearedEvm I).toNat) =
          AccountAddress.ofUInt256 (solcAddressSlotWord ⟨2⟩ σClearedEvm I) :=
        cageFlapperAddress_eq_target σClearedEvm I
      _ = AccountAddress.ofUInt256 (solcAddressSlotWord ⟨2⟩ σ_dai I) := by
        rw [hflapperTarget]
      _ = AccountAddress.ofUInt256 (solcAddressSlotWord ⟨2⟩ evmDai.accountMap I) := by
        rw [congrArg (fun accounts => solcAddressSlotWord ⟨2⟩ accounts I)
          hAccountsDai]
      _ = EVM.address (flapFlapperAddressOf evmDai) := by
        rw [← hFlapperAddr]
        apply Eq.symm
        apply Fin.ext
        simp [EVM.address, EVM.uintN]
        exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
  have hcallFlapEvm :
      typedCallViaEVM fork config evmFlapEvmIn (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)]
        (zFlap, evmFlapEvmOut, outFlap) true := by
    simpa [evmFlapEvmIn, evmFlapEvmOut, hFlapperTargetAddr] using hcallFlapEvmRaw
  obtain ⟨σ_flap_stele, A_flap_stele0, hcallFlapSteleBase, hAccountsFlap⟩ :=
    typedCallViaEVM_sameInputs (evm_stele := evmDai)
      hcallFlapEvm hAccountsDai
      (by simpa [evmFlapEvmIn, initState] using hσ0Dai.symm)
      (by simpa [evmFlapEvmIn, initState] using henvDai.symm)
  let evmFlapStele :=
    { evmDai with
      accountMap := σ_flap_stele
      substate := A_flap_stele0
    }
  have hcallFlapStele :
      typedCallViaEVM fork config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)]
        (zFlap, evmFlapStele, outFlap) true := by
    simpa [evmFlapStele] using hcallFlapSteleBase
  cases zFlap
  · exact vowCageFlapperCageCallFailureBodyCore (hperm := hperm) (acc := σ_flap)
      (evmDai := evmDai) (evmFlap := evmFlapStele)
      (target := solcAddressSlotWord ⟨2⟩ σClearedEvm I) (ret := ⟨412⟩)
      (R := [vowSelWord I])
      hcode hwv hauthStele hliveStele hdispatch hdecode
      (by simpa using rd2860) houtFlapSize (by simp) hvatCode hcallDai hdecDai
      hflapperCode (by simpa using hcallFlapStele)
  · have rd2860True : RD fork vowBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2860⟩
        (⟨1⟩ :: flapCageEndPtr :: flapCageSelectorWord ::
          solcAddressSlotWord ⟨2⟩ σClearedEvm I :: ⟨412⟩ :: vowSelWord I :: [])
        (flapCageCalldataMem flapperDai memDai)
        (UInt256.ofNat 6) outFlap σ_flap k2860 C2860 := by
      simpa using rd2860
    obtain ⟨k2881, C2881, rd2881⟩ :=
      RD.vowCageFlapperCageCallSuccessCleanup rd2860True (by simp)
    let memFlap := flapCageCalldataMem flapperDai memDai
    have hmemFlap : memFlap.size = 164 := by
      simpa [memFlap] using flapCageCalldataMem_size flapperDai hmemDai
    have hread64Flap :
        memFlap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memFlap] using flapCageCalldataMem_read64 flapperDai hmemDai hread64Dai
    have hcallFlapSteleTrue :
        typedCallViaEVM fork config evmDai (EVM.address (flapFlapperAddressOf evmDai))
          "cage" 0 [.int (Int.ofNat flapperDai.toNat)]
          (true, evmFlapStele, outFlap) true := by
      simpa using hcallFlapStele
    have hσ0Flap : evmFlapStele.σ₀ = σ₀ := by
      simpa [evmFlapStele] using hσ0Dai
    have henvFlap : evmFlapStele.executionEnv = I := by
      simpa [evmFlapStele] using henvDai
    exact cont hperm (evmDai := evmDai) (evmFlap := evmFlapStele) (outDai := outDai)
      (outFlap := outFlap) (memFlap := memFlap) (flapperDai := flapperDai)
      (by simpa [memFlap] using rd2881) hmemFlap hread64Flap hvatCode hcallDai
      hdecDai hauthStele hliveStele hflapperCode hcallFlapSteleTrue hdepthLt hσ0Flap henvFlap (by simpa [evmFlapEvmOut, evmFlapStele] using hAccountsFlap)

set_option maxHeartbeats 0 in
theorem vowCageBodyToSecondDai
    {σ σ₀ A I} {g : UInt256}
    (cont : I.perm = true →
      ∀ {σ_flap σ_flop : AccountMap}
        {evmDai evmFlap evmFlop : EVM.State}
        {outDai outFlap outFlop memFlop : ByteArray} {k2983 C2983 : ℕ}
        {flapperDai : UInt256},
        RD fork vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2983⟩
          (flopCageSelectorWord :: solcAddressSlotWord ⟨3⟩ σ_flap I ::
            ⟨412⟩ :: vowSelWord I :: [])
          memFlop (UInt256.ofNat 6) outFlop σ_flop k2983 C2983 →
        memFlop.size = 164 →
        memFlop.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM fork config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat flapperDai.toNat)] →
        solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩ →
        solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ →
        0 < (UInt256.ofNat
          ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM fork config evmDai (EVM.address (flapFlapperAddressOf evmDai))
          "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
          true →
        0 < (UInt256.ofNat
          ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM fork config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
          "cage" 0 [] (true, evmFlop, outFlop) true →
        I.depth.val < 1024 →
        evmFlop.σ₀ = σ₀ →
        evmFlop.executionEnv = I →
        Eq σ_flop evmFlop.accountMap →
        runtimeRefinementFor fork config contract σ σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      config.externalABI.decodeCalldata? (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToFlopperCage
      (fun hperm {σ_flap} {evmDai} {evmFlap} {outDai} {outFlap}
          {memFlap} {k2881} {C2881} {flapperDai} rd2881 hmemFlap hread64Flap
          hvatCode hcallDai hdecDai hauthStele hliveStele hflapperCode hcallFlap
          hdepthLt hσ0Flap henvFlap
          hAccountsFlap => ?_)
      hcode hsize hwv hsel
  by_cases hcodeSizeFlopper :
      Reasoning.Theory.extCodeSizeWord σ_flap
        (solcAddressSlotWord ⟨3⟩ σ_flap I) = ⟨0⟩
  · have hcodeSizeFlopperStele :
        Reasoning.Theory.extCodeSizeWord evmFlap.accountMap
            (solcAddressSlotWord ⟨3⟩ evmFlap.accountMap I) = ⟨0⟩ := by
      simpa only [← hAccountsFlap] using hcodeSizeFlopper
    have hownerFlap : evmFlap.executionEnv.codeOwner = I.codeOwner := by
      simp [henvFlap]
    have hflopperNoCode :
        (UInt256.ofNat
          ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      cageFlopperCode_zero_of_codeSize_zero evmFlap I hownerFlap hcodeSizeFlopperStele
    exact vowCageFlopperCageNoCodeBodyCore (hperm := hperm) (acc := σ_flap)
      (evmDai := evmDai) (evmFlap := evmFlap) (flapperDai := flapperDai)
      (ret := ⟨412⟩) (R := [vowSelWord I])
      hcode hwv hauthStele hliveStele hdispatch hdecode
      (by simpa using rd2881) hmemFlap hread64Flap hcodeSizeFlopper (by simp)
      hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperNoCode
  have hcodeSizeFlopperNE :
      Reasoning.Theory.extCodeSizeWord σ_flap
        (solcAddressSlotWord ⟨3⟩ σ_flap I) ≠ ⟨0⟩ :=
    hcodeSizeFlopper
  have hcodeSizeFlopperSteleNE :
      Reasoning.Theory.extCodeSizeWord evmFlap.accountMap
          (solcAddressSlotWord ⟨3⟩ evmFlap.accountMap I) ≠ ⟨0⟩ := by
    simpa only [← hAccountsFlap] using hcodeSizeFlopperNE
  have hownerFlap : evmFlap.executionEnv.codeOwner = I.codeOwner := by
    simp [henvFlap]
  have hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat :=
    cageFlopperCode_pos_of_codeSize_ne evmFlap I hownerFlap hcodeSizeFlopperSteleNE
  obtain ⟨σ_flop, zFlop, outFlop, A_flop, k2964, C2964, rd2964,
      hcallFlopEvmRaw, houtFlopSize⟩ :=
    RD.vowCageFlopperCageCall
      (σCall := σ_flap) (R := [vowSelWord I])
      rd2881 hmemFlap hread64Flap hcodeSizeFlopperNE hdepthLt (by simp)
  let evmFlopEvmIn :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flap
    }
  let evmFlopEvmOut :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flop
      substate := A_flop
    }
  have hFlopperAddr :
      flopFlopperAddressOf evmFlap =
        AccountAddress.ofUInt256 (solcAddressSlotWord ⟨3⟩ evmFlap.accountMap I) :=
    cageFlopperAddressOf_eq_vowAddressReturnWord evmFlap I hownerFlap
  have hFlopperTargetAddr :
      EVM.address (AccountAddress.ofNat (solcAddressSlotWord ⟨3⟩ σ_flap I).toNat) =
        EVM.address (flopFlopperAddressOf evmFlap) := by
    calc
      EVM.address (AccountAddress.ofNat (solcAddressSlotWord ⟨3⟩ σ_flap I).toNat) =
          AccountAddress.ofUInt256 (solcAddressSlotWord ⟨3⟩ σ_flap I) :=
        cageFlopperAddress_eq_target σ_flap I
      _ = AccountAddress.ofUInt256 (solcAddressSlotWord ⟨3⟩ evmFlap.accountMap I) := by
        rw [congrArg (fun accounts => solcAddressSlotWord ⟨3⟩ accounts I)
          hAccountsFlap]
      _ = EVM.address (flopFlopperAddressOf evmFlap) := by
        rw [← hFlopperAddr]
        apply Eq.symm
        apply Fin.ext
        simp [EVM.address, EVM.uintN]
        exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
  have hcallFlopEvm :
      typedCallViaEVM fork config evmFlopEvmIn (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (zFlop, evmFlopEvmOut, outFlop) true := by
    simpa [evmFlopEvmIn, evmFlopEvmOut, hFlopperTargetAddr] using hcallFlopEvmRaw
  obtain ⟨σ_flop_stele, A_flop_stele0, hcallFlopSteleBase, hAccountsFlop⟩ :=
    typedCallViaEVM_sameInputs (evm_stele := evmFlap)
      hcallFlopEvm hAccountsFlap
      (by simpa [evmFlopEvmIn, initState] using hσ0Flap.symm)
      (by simpa [evmFlopEvmIn, initState] using henvFlap.symm)
  let evmFlopStele :=
    { evmFlap with
      accountMap := σ_flop_stele
      substate := A_flop_stele0
    }
  have hcallFlopStele :
      typedCallViaEVM fork config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (zFlop, evmFlopStele, outFlop) true := by
    simpa [evmFlopStele] using hcallFlopSteleBase
  cases zFlop
  · exact vowCageFlopperCageCallFailureBodyCore (hperm := hperm) (acc := σ_flop)
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlopStele)
      (target := solcAddressSlotWord ⟨3⟩ σ_flap I) (ret := ⟨412⟩)
      (R := [vowSelWord I])
      hcode hwv hauthStele hliveStele hdispatch hdecode
      (by simpa using rd2964) houtFlopSize (by simp) hvatCode hcallDai hdecDai
      hflapperCode hcallFlap hflopperCode (by simpa using hcallFlopStele)
  · have rd2964True : RD fork vowBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2964⟩
        (⟨1⟩ :: flopCageEndPtr :: flopCageSelectorWord ::
          solcAddressSlotWord ⟨3⟩ σ_flap I :: ⟨412⟩ :: vowSelWord I :: [])
        (flopCageCalldataMem memFlap)
        (UInt256.ofNat 6) outFlop σ_flop k2964 C2964 := by
      simpa using rd2964
    obtain ⟨k2983, C2983, rd2983⟩ :=
      RD.vowCageFlopperCageCallSuccessCleanup rd2964True (by simp)
    let memFlop := flopCageCalldataMem memFlap
    have hmemFlop : memFlop.size = 164 := by
      simpa [memFlop] using flopCageCalldataMem_size hmemFlap
    have hread64Flop :
        memFlop.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memFlop] using flopCageCalldataMem_read64 hmemFlap hread64Flap
    have hcallFlopSteleTrue :
        typedCallViaEVM fork config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
          "cage" 0 [] (true, evmFlopStele, outFlop) true := by
      simpa using hcallFlopStele
    have hσ0Flop : evmFlopStele.σ₀ = σ₀ := by
      simpa [evmFlopStele] using hσ0Flap
    have henvFlop : evmFlopStele.executionEnv = I := by
      simpa [evmFlopStele] using henvFlap
    exact cont hperm (σ_flap := σ_flap) (evmDai := evmDai) (evmFlap := evmFlap)
      (evmFlop := evmFlopStele) (outDai := outDai) (outFlap := outFlap)
      (outFlop := outFlop) (memFlop := memFlop) (flapperDai := flapperDai)
      (by simpa [memFlop] using rd2983) hmemFlop hread64Flop hvatCode hcallDai
      hdecDai hauthStele hliveStele hflapperCode hcallFlap hflopperCode hcallFlopSteleTrue
      hdepthLt hσ0Flop henvFlop
      (by simpa [evmFlopEvmOut, evmFlopStele] using hAccountsFlop)

set_option maxHeartbeats 0 in
theorem vowCageBodyToVatSin
    {σ σ₀ A I} {g : UInt256}
    (cont : I.perm = true →
      ∀ {σ_dai2 : AccountMap}
        {evmDai evmFlap evmFlop evmDai2 : EVM.State}
        {outDai outFlap outFlop outDai2 memDai2 : ByteArray} {k3115 C3115 : ℕ}
        {flapperDai vatDai : UInt256},
        RD fork vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3115⟩
          (vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord σ_dai2 I ::
            ⟨412⟩ :: vowSelWord I :: [])
          memDai2 (UInt256.ofNat 6) outDai2 σ_dai2 k3115 C3115 →
        memDai2.size = 164 →
        memDai2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Stele.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Stele.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Stele.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM fork config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat flapperDai.toNat)] →
        solcSlotWordAt (vowCallerWardsSlot I) σ I = ⟨1⟩ →
        solcSlotWordAt ⟨12⟩ σ I = ⟨1⟩ →
        0 < (UInt256.ofNat
          ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM fork config evmDai (EVM.address (flapFlapperAddressOf evmDai))
          "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
          true →
        0 < (UInt256.ofNat
          ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM fork config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
          "cage" 0 [] (true, evmFlop, outFlop) true →
        0 < (UInt256.ofNat
          ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM fork config evmFlop (EVM.address (cageVatAddressOf evmFlop))
          "dai" 0 [.address evmFlop.executionEnv.codeOwner] (true, evmDai2, outDai2)
          false →
        config.externalABI.decode? "dai" outDai2 =
          some [.int (Int.ofNat vatDai.toNat)] →
        I.depth.val < 1024 →
        evmDai2.σ₀ = σ₀ →
        evmDai2.executionEnv = I →
        Eq σ_dai2 evmDai2.accountMap →
        runtimeRefinementFor fork config contract σ σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      config.externalABI.decodeCalldata? (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToSecondDai
      (fun hperm {σ_flap} {σ_flop} {evmDai} {evmFlap} {evmFlop}
          {outDai} {outFlap} {outFlop} {memFlop} {k2983} {C2983}
          {flapperDai} rd2983 hmemFlop hread64Flop hvatCode hcallDai hdecDai
          hauthStele hliveStele hflapperCode hcallFlap hflopperCode hcallFlop
          hdepthLt hσ0Flop henvFlop
          hAccountsFlop => ?_)
      hcode hsize hwv hsel
  by_cases hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ_flop (kissDaiTargetWord σ_flop I) =
        ⟨0⟩
  · have hcodeSizeVatStele :
        Reasoning.Theory.extCodeSizeWord evmFlop.accountMap
            (kissDaiTargetWord evmFlop.accountMap I) = ⟨0⟩ := by
      simpa only [← hAccountsFlop] using hcodeSizeVat
    have hownerFlop : evmFlop.executionEnv.codeOwner = I.codeOwner := by
      simp [henvFlop]
    have hvatNoCode :
        (UInt256.ofNat
          ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      cageVatCode_zero_of_codeSize_zero evmFlop I hownerFlop hcodeSizeVatStele
    exact vowCageSecondDaiNoCodeBodyCore (hperm := hperm) (acc := σ_flop)
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
      (flapperDai := flapperDai) (d1 := flopCageSelectorWord)
      (d2 := solcAddressSlotWord ⟨3⟩ σ_flap I) (R := [⟨412⟩, vowSelWord I])
      hcode hwv hauthStele hliveStele hdispatch hdecode
      (by simpa using rd2983) hmemFlop hread64Flop hcodeSizeVat (by simp)
      hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
      hvatNoCode
  have hcodeSizeVatNE :
      Reasoning.Theory.extCodeSizeWord σ_flop (kissDaiTargetWord σ_flop I) ≠
        ⟨0⟩ :=
    hcodeSizeVat
  have hcodeSizeVatSteleNE :
      Reasoning.Theory.extCodeSizeWord evmFlop.accountMap
          (kissDaiTargetWord evmFlop.accountMap I) ≠ ⟨0⟩ := by
    simpa only [← hAccountsFlop] using hcodeSizeVatNE
  have hownerFlop : evmFlop.executionEnv.codeOwner = I.codeOwner := by
    simp [henvFlop]
  have hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat :=
    cageVatCode_pos_of_codeSize_ne evmFlop I hownerFlop hcodeSizeVatSteleNE
  obtain ⟨σ_dai2, zDai2, outDai2, A_dai2, k3074, C3074, rd3074,
      hcallDai2EvmRaw, houtDai2Size⟩ :=
    RD.vowCageSecondDaiStaticcall
      (σCall := σ_flop)
      (R := [⟨412⟩, vowSelWord I])
      rd2983 hmemFlop hread64Flop hcodeSizeVatNE hdepthLt (by simp)
  let evmDai2EvmIn :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flop
    }
  let evmDai2EvmOut :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_dai2
      substate := A_dai2
    }
  have hcallDai2Evm :
      typedCallViaEVM fork config evmDai2EvmIn (EVM.address (kissVatAddress σ_flop I))
        "dai" 0 [.address I.codeOwner] (zDai2, evmDai2EvmOut, outDai2) false := by
    simpa [evmDai2EvmIn, evmDai2EvmOut] using hcallDai2EvmRaw
  have hDai2TargetPostEvm : kissDaiTargetWord σ_dai2 I = kissDaiTargetWord σ_flop I := by
    have hslot :=
      typedCallViaEVM_static_storage_getD_of_accounts_eq
        (cfg := config) (σ := σ_flop) (evm := evmDai2EvmIn)
        (evm' := evmDai2EvmOut) (target := EVM.address (kissVatAddress σ_flop I))
        (name := "dai") (args := [.address I.codeOwner]) (z := zDai2)
        (out := outDai2) (slot := ⟨1⟩) (default := ⟨0⟩)
        (by simp [evmDai2EvmIn])
        hcallDai2Evm
    simpa [kissDaiTargetWord, solcSlotWordAt, evmDai2EvmIn, evmDai2EvmOut, initState] using
      congrArg (fun word => UInt256.land word solcAddrMask) hslot
  have hVatAddrMap : kissVatAddress σ_flop I = kissVatAddress evmFlop.accountMap I :=
    congrArg (fun accounts => kissVatAddress accounts I) hAccountsFlop
  have hVatAddrStele : cageVatAddressOf evmFlop = kissVatAddress evmFlop.accountMap I :=
    cageVatAddressOf_eq_kissVatAddress evmFlop I hownerFlop
  have hVatTargetAddr :
      EVM.address (kissVatAddress σ_flop I) =
        EVM.address (cageVatAddressOf evmFlop) := by
    rw [hVatAddrMap, ← hVatAddrStele]
  have hVatTargetAddrFlop :
      EVM.address (kissVatAddress σ_flop evmFlop.executionEnv) =
        EVM.address (cageVatAddressOf evmFlop) := by
    simpa [← henvFlop] using hVatTargetAddr
  obtain ⟨σ_dai2_stele, A_dai2_stele0, hcallDai2SteleBase, hAccountsDai2⟩ :=
    typedCallViaEVM_sameInputs (evm_stele := evmFlop)
      hcallDai2Evm hAccountsFlop
      (by simpa [evmDai2EvmIn, initState] using hσ0Flop.symm)
      (by simpa [evmDai2EvmIn, initState] using henvFlop.symm)
  let evmDai2Stele :=
    { evmFlop with
      accountMap := σ_dai2_stele
      substate := A_dai2_stele0
    }
  have hcallDai2Stele :
      typedCallViaEVM fork config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner]
        (zDai2, evmDai2Stele, outDai2) false := by
    simpa [evmDai2Stele, evmDai2EvmOut, hVatTargetAddrFlop, ← henvFlop]
      using hcallDai2SteleBase
  cases zDai2
  · exact vowCageSecondDaiCallFailureBodyCore (hperm := hperm) (acc := σ_dai2)
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
      (evmDai2 := evmDai2Stele) (target := kissDaiTargetWord σ_flop I)
      (R := [⟨412⟩, vowSelWord I])
      hcode hwv hauthStele hliveStele hdispatch hdecode
      (by simpa using rd3074) houtDai2Size (by simp) hvatCode hcallDai hdecDai
      hflapperCode hcallFlap hflopperCode hcallFlop hvatCode2
      (by simpa using hcallDai2Stele)
  · have rd3074True : RD fork vowBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3074⟩
        (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σ_flop I ::
          ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord σ_flop I ::
          ⟨412⟩ :: vowSelWord I :: [])
        (outDai2.write 0 (vatDaiCalldataMem I memFlop) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai2.size)).toNat)
        (UInt256.ofNat 6) outDai2 σ_dai2 k3074 C3074 := by
      simpa using rd3074
    have hcallDai2SteleTrue :
        typedCallViaEVM fork config evmFlop (EVM.address (cageVatAddressOf evmFlop))
          "dai" 0 [.address evmFlop.executionEnv.codeOwner]
          (true, evmDai2Stele, outDai2) false := by
      simpa using hcallDai2Stele
    let baseDai2 := vatDaiCalldataMem I memFlop
    have hbaseDai2 : baseDai2.size = 164 := by
      simpa [baseDai2] using vatDaiCalldataMem_size I hmemFlop
    have hbaseDai2Read64 :
        baseDai2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [baseDai2] using vatDaiCalldataMem_read64 I hmemFlop hread64Flop
    by_cases ho32Dai2 : 32 ≤ outDai2.size
    · let vatDai : UInt256 :=
        UInt256.ofNat (fromByteArrayBigEndian (outDai2.extract 0 32))
      have hmin :
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai2.size)).toNat = 32 :=
        ctorMin32_toNat_of_ge ho32Dai2 houtDai2Size
      have rd3074Write := rd3074True
      rw [hmin] at rd3074Write
      obtain ⟨_, _, rd3092⟩ :=
        RD.vowCageSecondDaiCallSuccessToDecode rd3074Write (by simp)
      let memDai2 := outDai2.write 0 baseDai2 128 32
      have hmemDai2 : memDai2.size = 164 := by
        simpa [memDai2] using returnWrite_size_164 outDai2 32 hbaseDai2
          (by omega) ho32Dai2
      have hread64Dai2 :
          memDai2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memDai2] using returnWrite_read64 outDai2 32 hbaseDai2
          hbaseDai2Read64 (by omega) ho32Dai2
      have hmload64 :
          (if (⟨64⟩ : UInt256).toNat ≥ memDai2.size then ⟨0⟩
           else UInt256.ofNat
             (fromByteArrayBigEndian
              (memDai2.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
            ⟨128⟩ :=
        mloadFreePtrValue (by rw [hmemDai2]; decide) hread64Dai2
      have hmload128 :
          (if (⟨128⟩ : UInt256).toNat ≥ memDai2.size then ⟨0⟩
           else UInt256.ofNat
             (fromByteArrayBigEndian
              (memDai2.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
            UInt256.ofNat (fromByteArrayBigEndian (outDai2.extract 0 32)) := by
        have hnot :
            ¬ ((⟨128⟩ : UInt256).toNat ≥ memDai2.size) := by
          rw [hmemDai2]
          native_decide
        rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        simpa [memDai2] using
          congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes))
            (returnWrite_read128_32 outDai2 hbaseDai2 ho32Dai2)
      obtain ⟨k3115, C3115, rd3115⟩ :=
        RD.vowCageSecondDaiReturnDecodeOk
          (retWord := UInt256.ofNat (fromByteArrayBigEndian (outDai2.extract 0 32)))
          rd3092 ho32Dai2 houtDai2Size hmload64 hmload128 (by simp)
      have hdecDai2 :
          config.externalABI.decode? "dai" outDai2 =
            some [.int (Int.ofNat vatDai.toNat)] := by
        simpa [vatDai] using kissDaiDecode_ok (o := outDai2) ho32Dai2
      have hσ0Dai2 : evmDai2Stele.σ₀ = σ₀ := by
        simpa [evmDai2Stele] using hσ0Flop
      have henvDai2 : evmDai2Stele.executionEnv = I := by
        simpa [evmDai2Stele] using henvFlop
      exact cont hperm (σ_dai2 := σ_dai2) (evmDai := evmDai) (evmFlap := evmFlap)
        (evmFlop := evmFlop)
        (evmDai2 := evmDai2Stele) (outDai := outDai) (outFlap := outFlap)
        (outFlop := outFlop) (outDai2 := outDai2) (memDai2 := memDai2)
        (flapperDai := flapperDai) (vatDai := vatDai)
        (by simpa [vatDai, memDai2, hDai2TargetPostEvm] using rd3115)
        hmemDai2 hread64Dai2 hvatCode
        hcallDai hdecDai hauthStele hliveStele hflapperCode hcallFlap hflopperCode
        hcallFlop hvatCode2 hcallDai2SteleTrue hdecDai2 hdepthLt hσ0Dai2 henvDai2
        (by simpa [evmDai2EvmOut, evmDai2Stele] using hAccountsDai2)
    · have hshortDai2 : outDai2.size < 32 := Nat.lt_of_not_ge ho32Dai2
      exact vowCageSecondDaiDecodeShortBodyCore (hperm := hperm) (acc := σ_dai2)
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2Stele) (base := baseDai2) (outDai := outDai)
        (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
        (target := kissDaiTargetWord σ_flop I) (R := [⟨412⟩, vowSelWord I])
        hcode hwv hauthStele hliveStele hdispatch hdecode rd3074True
        hbaseDai2 hbaseDai2Read64 houtDai2Size hshortDai2 (by simp)
        hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
        hvatCode2 hcallDai2SteleTrue

end Benchmarks.Dss.Vow

import Benchmarks.Dss.Vow.CageHealRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` top-level runtime wrapper helpers -/

-- LIBRARY CANDIDATE: field preservation facts for `Solm.EVM.storageStore`.
theorem storageStore_substate (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem cageFlapperTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    vowAddressReturnWord ⟨2⟩ σ I = vowAddressReturnWord ⟨2⟩ τ I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  simpa [vowAddressReturnWord, vowSlotWord, solcSlotWord] using
    congrArg (fun word => UInt256.land word solcAddrMask) hslot

theorem cageFlapperCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (vowAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (vowAddressReturnWord ⟨2⟩ τ I) ≠
      ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (vowAddressReturnWord ⟨2⟩ σ I)
  have htarget : vowAddressReturnWord ⟨2⟩ σ I = vowAddressReturnWord ⟨2⟩ τ I :=
    cageFlapperTargetWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem cageFlapperCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (vowAddressReturnWord ⟨2⟩ σ I) =
        ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (vowAddressReturnWord ⟨2⟩ τ I) =
      ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (vowAddressReturnWord ⟨2⟩ σ I)
  have htarget : vowAddressReturnWord ⟨2⟩ σ I = vowAddressReturnWord ⟨2⟩ τ I :=
    cageFlapperTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem cageFlopperTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    vowAddressReturnWord ⟨3⟩ σ I = vowAddressReturnWord ⟨3⟩ τ I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  simpa [vowAddressReturnWord, vowSlotWord, solcSlotWord] using
    congrArg (fun word => UInt256.land word solcAddrMask) hslot

theorem cageFlopperCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (vowAddressReturnWord ⟨3⟩ σ I) ≠
        ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (vowAddressReturnWord ⟨3⟩ τ I) ≠
      ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (vowAddressReturnWord ⟨3⟩ σ I)
  have htarget : vowAddressReturnWord ⟨3⟩ σ I = vowAddressReturnWord ⟨3⟩ τ I :=
    cageFlopperTargetWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem cageFlopperCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (vowAddressReturnWord ⟨3⟩ σ I) =
        ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (vowAddressReturnWord ⟨3⟩ τ I) =
      ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (vowAddressReturnWord ⟨3⟩ σ I)
  have htarget : vowAddressReturnWord ⟨3⟩ σ I = vowAddressReturnWord ⟨3⟩ τ I :=
    cageFlopperTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem cageVatTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    kissDaiTargetWord σ I = kissDaiTargetWord τ I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  simpa [kissDaiTargetWord, vowSlotWord] using
    congrArg (fun word => UInt256.land word solcAddrMask) hslot

theorem cageVatAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    kissVatAddress σ I = kissVatAddress τ I := by
  rw [kissVatAddress_eq_daiTarget_account σ I, kissVatAddress_eq_daiTarget_account τ I,
    cageVatTargetWord_accountMapEquiv hAccounts]

theorem cageVatCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (kissDaiTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (kissDaiTargetWord σ I)
  have htarget : kissDaiTargetWord σ I = kissDaiTargetWord τ I :=
    cageVatTargetWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem cageVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (kissDaiTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (kissDaiTargetWord σ I)
  have htarget : kissDaiTargetWord σ I = kissDaiTargetWord τ I :=
    cageVatTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem cageFlapperAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σ I).toNat) =
      AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simp [EVM.twoPow, AccountAddress.size])

theorem cageFlopperAddressOf_eq_vowAddressReturnWord (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    flopFlopperAddressOf evm =
      AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ evm.accountMap I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [flopFlopperAddressOf, vowAddressReturnWord,
    flapStorageLoad_codeOwner_eq_vowSlotWord evm I ⟨3⟩ howner]

theorem cageFlopperCode_pos_of_codeSize_ne (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (vowAddressReturnWord ⟨3⟩ evm.accountMap I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := vowAddressReturnWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (cageFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hne

theorem cageFlopperCode_zero_of_codeSize_zero (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (vowAddressReturnWord ⟨3⟩ evm.accountMap I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := vowAddressReturnWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (cageFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hzero

theorem cageVatAddressOf_eq_kissVatAddress (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    cageVatAddressOf evm = kissVatAddress evm.accountMap I := by
  have hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ evm.accountMap I := by
    simpa [howner] using flapStorageLoad_codeOwner_eq_vowSlotWord evm I ⟨1⟩ howner
  simp only [cageVatAddressOf, kissVatAddress, vowAddressReturnWord]
  rw [hload]

theorem cageVatCode_pos_of_codeSize_ne (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (kissDaiTargetWord evm.accountMap I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (cageVatAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat := by
  have haddr :
      cageVatAddressOf evm = AccountAddress.ofUInt256 (kissDaiTargetWord evm.accountMap I) :=
    (cageVatAddressOf_eq_kissVatAddress evm I howner).trans
      (kissVatAddress_eq_daiTarget_account evm.accountMap I)
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := kissDaiTargetWord evm.accountMap I)
      (addr := cageVatAddressOf evm) haddr hne

theorem cageVatCode_zero_of_codeSize_zero (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (kissDaiTargetWord evm.accountMap I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (cageVatAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  have haddr :
      cageVatAddressOf evm = AccountAddress.ofUInt256 (kissDaiTargetWord evm.accountMap I) :=
    (cageVatAddressOf_eq_kissVatAddress evm I howner).trans
      (kissVatAddress_eq_daiTarget_account evm.accountMap I)
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := kissDaiTargetWord evm.accountMap I)
      (addr := cageVatAddressOf evm) haddr hzero

theorem RD.vowCageFirstDaiCallDepthLimit
    {cA gh bl σ σCall σ₀ A I} {g ret : UInt256}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2669⟩
      (solcSlotWord σCall I ⟨1⟩ :: solcSlotWord σCall I ⟨2⟩ :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σCall) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σCall (kissDaiTargetWord σCall I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σCall I ::
        ⟨2734234354⟩ :: vowAddressReturnWord ⟨2⟩ σCall I :: ret :: R)
      (vatDaiCalldataMemFor (vowAddressReturnWord ⟨2⟩ σCall I) mem)
      (UInt256.ofNat 6) ByteArray.empty (cA, σCall) k' C' := by
  have hcodeSizeRaw :
      Reasoning.Theory.uniswapExtCodeSizeWord σCall
        (UInt256.land solcAddrMask (solcSlotWord σCall I ⟨1⟩)) ≠ ⟨0⟩ := by
    simpa [kissDaiTargetWord, vowSlotWord, solcSlotWord, u256_land_comm] using hcodeSize
  obtain ⟨_, _, _, rd2753⟩ :=
    RD.vowCageFirstDaiStaticcallSetup rd hmem hread64 hcodeSizeRaw hov
  obtain ⟨k2754, C2754, rd2754raw⟩ :=
    RD.uniswapStaticcallDepthLimit rd2753 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    native_decide
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd2754 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σCall I ⟨1⟩) :: ⟨2734234354⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σCall I ⟨2⟩) :: ret :: R)
      (ByteArray.empty.write 0
        (vatDaiCalldataMemFor
          (UInt256.land solcAddrMask (solcSlotWord σCall I ⟨2⟩)) mem)
        128 (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA, σCall) k2754 C2754 :=
    haw ▸ rd2754raw
  rw [hmin, byteArray_write_len_zero] at rd2754
  exact ⟨k2754, C2754, by
    simpa [kissDaiTargetWord, vowAddressReturnWord, vowSlotWord, solcSlotWord,
      u256_land_comm] using rd2754⟩

theorem vowCageFirstDaiCallDepthLimitBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hliveEvm : vowSlotWord ⟨12⟩ σ_evm I = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (vowCageClearedAccountMap I.codeOwner σ_evm)
        (kissDaiTargetWord (vowCageClearedAccountMap I.codeOwner σ_evm) I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σClearedEvm := vowCageClearedAccountMap I.codeOwner σ_evm
  let σClearedSolm := vowCageClearedAccountMap I.codeOwner σ_solm
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
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
    vowCageReachAfterClear (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hauthEvm hliveEvm
  obtain ⟨_, _, rdLoads⟩ :=
    RD.vowCageFirstDaiLoadTargets (R := [vowSelWord I]) rdClear (by simp)
  obtain ⟨_, _, rd2754⟩ :=
    RD.vowCageFirstDaiCallDepthLimit
      (σCall := σClearedEvm) (ret := ⟨412⟩) (R := [vowSelWord I])
      rdLoads hmemAuth hread64 (by simpa [σClearedEvm] using hcodeSize) hdepth
      (by simp)
  have hauthSolm : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hslot :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (vowCallerWardsSlot I) ⟨0⟩
    exact (by simpa [vowSlotWord] using hslot.symm.trans hauthEvm)
  have hliveSolm : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ := by
    have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
    exact (by simpa [vowSlotWord] using hslot.symm.trans hliveEvm)
  have hClearedAccounts : accountMapEquiv σClearedEvm σClearedSolm := by
    simpa [σClearedEvm, σClearedSolm] using
      accountMapEquiv_vowCageCleared I.codeOwner hAccounts
  have hTargetCleared :
      kissDaiTargetWord σClearedEvm I = kissDaiTargetWord σClearedSolm I := by
    have hslot := accountMapEquiv_storage_findD hClearedAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissDaiTargetWord, vowSlotWord, hslot]
  have hcodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σClearedSolm
        (kissDaiTargetWord σClearedSolm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSize
    have hsame :=
      Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hClearedAccounts
        (kissDaiTargetWord σClearedEvm I)
    rw [hsame, hTargetCleared]
    exact hzero
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hownerAsh : evmAsh.executionEnv.codeOwner = I.codeOwner := by
    simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
  have haddrCage :
      cageVatAddressOf evmAsh = kissVatAddress σClearedSolm I := by
    have hload :
        Solm.EVM.storageLoad evmAsh I.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ evmAsh.accountMap I := by
      simpa [hownerAsh] using
        flapStorageLoad_codeOwner_eq_vowSlotWord evmAsh I ⟨1⟩ hownerAsh
    simp only [cageVatAddressOf, kissVatAddress, vowAddressReturnWord]
    rw [hownerAsh, hload]
    simp [
      σClearedSolm, evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
      vowCageClearedAccountMap]
  have haddr :
      cageVatAddressOf evmAsh = AccountAddress.ofUInt256 (kissDaiTargetWord σClearedSolm I) :=
    haddrCage.trans (kissVatAddress_eq_daiTarget_account σClearedSolm I)
  have hvatCode :
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat := by
    have hpos :=
      uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σClearedSolm) (target := kissDaiTargetWord σClearedSolm I)
        (addr := cageVatAddressOf evmAsh) haddr hcodeSizeSolm
    simpa [evmAsh, evmSin, evmLive, evm0, initState, State.lookupAccount,
      storageStore_accountMap, σClearedSolm, vowCageClearedAccountMap] using hpos
  have hflapperArg :
      flapFlapperAddressOf evmAsh =
        AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σClearedSolm I).toNat := by
    have hslot :
        vowAddressReturnWord ⟨2⟩ evmAsh.accountMap I =
          vowAddressReturnWord ⟨2⟩ σClearedSolm I := by
      simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
        σClearedSolm, vowCageClearedAccountMap]
    rw [flapFlapperAddressOf_eq_vowAddressReturnWord evmAsh I hownerAsh, hslot,
      accountAddress_ofUInt256_eq_ofNat_toNat]
  let A_dai := (evmAsh.addAccessedAccount (EVM.address (cageVatAddressOf evmAsh))).substate
  have hcallDai :
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)]
        (false, { evmAsh with substate := A_dai }, ByteArray.empty) false := by
    have henc :
        config.externalABI.encode? "dai" [.address (flapFlapperAddressOf evmAsh)] =
          some ((vatDaiCalldataMemFor (vowAddressReturnWord ⟨2⟩ σClearedSolm I)
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).readWithPadding 128 36) := by
      rw [hflapperArg]
      simpa [vowAddressReturnWord, vowSlotWord, solcSlotWord, u256_land_comm] using
        vatDaiEncodeMasked_eq_of_size96 (solcSlotWord σClearedSolm I ⟨2⟩) hmemAuth
    simpa [A_dai, evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
      using
        (callNotMade_depthLimit (cfg := config) (evm := evmAsh)
          (tgt := EVM.address (cageVatAddressOf evmAsh)) (name := "dai")
          (args := [.address (flapFlapperAddressOf evmAsh)]) (callPerm := false)
          henc
          (by
            simpa [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
              using hdepth))
  exact vowCageFirstDaiCallFailureBodyCore (acc := (cA, σClearedEvm))
    (evmDai := { evmAsh with substate := A_dai }) (outDai := ByteArray.empty)
    hcode hwv hauthSolm hliveSolm hdispatch hdecode
    (by simpa [σClearedEvm] using rd2754)
    (by native_decide) (by simp) hvatCode hcallDai

set_option maxHeartbeats 0 in
theorem vowCageBodyToFlapperCage
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_dai : Batteries.RBSet AccountAddress compare} {σ_dai : AccountMap}
        {evmDai : EVM.State} {outDai memDai : ByteArray} {k2795 C2795 : ℕ}
        {flapperDai : UInt256},
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2795⟩
          (flapperDai :: flapCageSelectorWord ::
            vowAddressReturnWord ⟨2⟩ (vowCageClearedAccountMap I.codeOwner σ_evm) I ::
            ⟨412⟩ :: vowSelWord I :: [])
          memDai (UInt256.ofNat 6) outDai (cA_dai, σ_dai) k2795 C2795 →
        memDai.size = 164 →
        memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
          config.externalABI.decode? "dai" outDai =
            some [.int (Int.ofNat flapperDai.toNat)] →
          vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩ →
          vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ →
          I.depth.val < 1024 →
        evmDai.createdAccounts = cA_dai →
        evmDai.σ₀ = σ₀ →
        evmDai.blocks = bl →
        evmDai.genesisBlockHeader = gh →
        evmDai.executionEnv = I →
        accountMapEquiv σ_dai evmDai.accountMap →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩
  · by_cases hliveEvm : vowSlotWord ⟨12⟩ σ_evm I = ⟨1⟩
    · let σClearedEvm := vowCageClearedAccountMap I.codeOwner σ_evm
      let σClearedSolm := vowCageClearedAccountMap I.codeOwner σ_solm
      have hsz : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
      have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
        vowDispatch_cage hsel
      have hdecode :
          decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
            (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
        vowDecode_cage hsz
      by_cases hcodeSizeFirst :
          Reasoning.Theory.uniswapExtCodeSizeWord σClearedEvm
              (kissDaiTargetWord σClearedEvm I) =
            ⟨0⟩
      · exact vowCageFirstDaiNoCodeBodyCore hcode hsize hperm hwv hsel hAccounts
          hauthEvm hliveEvm (by simpa [σClearedEvm] using hcodeSizeFirst)
      have hcodeSizeFirstNE :
          Reasoning.Theory.uniswapExtCodeSizeWord σClearedEvm
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
          vowCageReachAfterClear (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hauthEvm hliveEvm
        obtain ⟨_, _, rdLoads⟩ :=
          RD.vowCageFirstDaiLoadTargets (R := [vowSelWord I]) rdClear (by simp)
        obtain ⟨cA_dai, σ_dai, zDai, outDai, A_dai, k2754, C2754, rd2754,
            hcallDaiEvmRaw, houtDaiSize⟩ :=
          RD.vowCageFirstDaiStaticcall
            (σCall := σClearedEvm) (ret := ⟨412⟩) (R := [vowSelWord I])
            rdLoads hmemAuth hread64 (by simpa [σClearedEvm] using hcodeSizeFirstNE)
            hdepthLt (by simp)
        have hauthSolm : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
          have hslot :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (vowCallerWardsSlot I) ⟨0⟩
          exact (by simpa [vowSlotWord] using hslot.symm.trans hauthEvm)
        have hliveSolm : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ := by
          have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
          exact (by simpa [vowSlotWord] using hslot.symm.trans hliveEvm)
        have hClearedAccounts : accountMapEquiv σClearedEvm σClearedSolm := by
          simpa [σClearedEvm, σClearedSolm] using
            accountMapEquiv_vowCageCleared I.codeOwner hAccounts
        have hTargetCleared :
            kissDaiTargetWord σClearedEvm I = kissDaiTargetWord σClearedSolm I := by
          have hslot :=
            accountMapEquiv_storage_findD hClearedAccounts I.codeOwner ⟨1⟩ ⟨0⟩
          simp [kissDaiTargetWord, vowSlotWord, hslot]
        have hFlapperCleared :
            vowAddressReturnWord ⟨2⟩ σClearedEvm I =
              vowAddressReturnWord ⟨2⟩ σClearedSolm I := by
          have hslot :=
            accountMapEquiv_storage_findD hClearedAccounts I.codeOwner ⟨2⟩ ⟨0⟩
          simp [vowAddressReturnWord, vowSlotWord, hslot]
        have hcodeSizeSolm :
            Reasoning.Theory.uniswapExtCodeSizeWord σClearedSolm
              (kissDaiTargetWord σClearedSolm I) ≠ ⟨0⟩ := by
          intro hzero
          apply hcodeSizeFirstNE
          have hsame :=
            Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hClearedAccounts
              (kissDaiTargetWord σClearedEvm I)
          rw [hsame, hTargetCleared]
          exact hzero
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
        let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
        let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
        have hownerAsh : evmAsh.executionEnv.codeOwner = I.codeOwner := by
          simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
        have haddrCage :
            cageVatAddressOf evmAsh = kissVatAddress σClearedSolm I := by
          have hload :
              Solm.EVM.storageLoad evmAsh I.codeOwner ⟨1⟩ =
                vowSlotWord ⟨1⟩ evmAsh.accountMap I := by
            simpa [hownerAsh] using
              flapStorageLoad_codeOwner_eq_vowSlotWord evmAsh I ⟨1⟩ hownerAsh
          simp only [cageVatAddressOf, kissVatAddress, vowAddressReturnWord]
          rw [hownerAsh, hload]
          simp [
            σClearedSolm, evmAsh, evmSin, evmLive, evm0, initState,
            storageStore_accountMap, vowCageClearedAccountMap]
        have hVatAddrCleared :
            kissVatAddress σClearedEvm I = kissVatAddress σClearedSolm I := by
          apply Fin.ext
          simp [kissVatAddress, vowAddressReturnWord, hTargetCleared]
        have hVatTarget :
            EVM.address (kissVatAddress σClearedEvm I) =
              EVM.address (cageVatAddressOf evmAsh) := by
          rw [hVatAddrCleared, haddrCage]
        have haddr :
            cageVatAddressOf evmAsh =
              AccountAddress.ofUInt256 (kissDaiTargetWord σClearedSolm I) :=
          haddrCage.trans (kissVatAddress_eq_daiTarget_account σClearedSolm I)
        have hvatCode :
            0 < (UInt256.ofNat
              ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
                (fun acc => acc.code.size))).toNat := by
          have hpos :=
            uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
              (σ := σClearedSolm) (target := kissDaiTargetWord σClearedSolm I)
              (addr := cageVatAddressOf evmAsh) haddr hcodeSizeSolm
          simpa [evmAsh, evmSin, evmLive, evm0, initState, State.lookupAccount,
            storageStore_accountMap, σClearedSolm, vowCageClearedAccountMap] using hpos
        have hflapperArg :
            flapFlapperAddressOf evmAsh =
              AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σClearedSolm I).toNat := by
          have hslot :
              vowAddressReturnWord ⟨2⟩ evmAsh.accountMap I =
                vowAddressReturnWord ⟨2⟩ σClearedSolm I := by
            simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
              σClearedSolm, vowCageClearedAccountMap]
          rw [flapFlapperAddressOf_eq_vowAddressReturnWord evmAsh I hownerAsh, hslot,
            accountAddress_ofUInt256_eq_ofNat_toNat]
        let evmDaiEvmIn :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σClearedEvm }
        let evmDaiEvmOut :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_dai
            substate := A_dai
            createdAccounts := cA_dai }
        have hcallDaiEvm :
            typedCallViaEVM config evmDaiEvmIn (EVM.address (kissVatAddress σClearedEvm I))
              "dai" 0 [.address (AccountAddress.ofNat
                (vowAddressReturnWord ⟨2⟩ σClearedEvm I).toNat)]
              (zDai, evmDaiEvmOut, outDai) false := by
          simpa [evmDaiEvmIn, evmDaiEvmOut] using hcallDaiEvmRaw
        have hDaiTargetPostEvm :
            kissDaiTargetWord σ_dai I = kissDaiTargetWord σClearedEvm I := by
          have hslot :=
            typedCallViaEVM_static_storage_findD_of_accountMapEquiv
              (cfg := config) (σ := σClearedEvm) (evm := evmDaiEvmIn)
              (evm' := evmDaiEvmOut) (target := EVM.address (kissVatAddress σClearedEvm I))
              (name := "dai")
              (args := [.address (AccountAddress.ofNat
                (vowAddressReturnWord ⟨2⟩ σClearedEvm I).toNat)])
              (z := zDai) (out := outDai) (slot := ⟨1⟩) (default := ⟨0⟩)
              (by simpa [evmDaiEvmIn] using accountMapEquiv_refl σClearedEvm)
              hcallDaiEvm
          simpa [kissDaiTargetWord, vowSlotWord, solcSlotWord, evmDaiEvmIn,
            evmDaiEvmOut, initState] using
            congrArg (fun word => UInt256.land word solcAddrMask) hslot
        obtain ⟨σ_dai_solm, A_dai_solm, hcallDaiSolmRaw, hAccountsDai⟩ :=
          typedCallViaEVM_accountMapEquiv (evm_solm := evmAsh)
            hcallDaiEvm
            (by
              simpa [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_accountMap, σClearedEvm, σClearedSolm, vowCageClearedAccountMap]
                using hClearedAccounts)
            (by
              simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_σ₀])
            (by
              simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_createdAccounts])
            (by
              simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_genesisBlockHeader])
            (by
              simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_blocks])
            (by
              simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_substate])
            (by simp [evmDaiEvmIn, evmAsh, evmSin, evmLive, evm0, initState,
              storageStore_executionEnv])
        let evmDaiSolm :=
          { evmAsh with
            accountMap := σ_dai_solm
            substate := A_dai_solm
            createdAccounts := cA_dai }
        have hcallDaiSolm :
            typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
              "dai" 0 [.address (flapFlapperAddressOf evmAsh)]
              (zDai, evmDaiSolm, outDai) false := by
          simpa [evmDaiSolm, hVatTarget, hflapperArg, hFlapperCleared] using
            hcallDaiSolmRaw
        cases zDai
        · exact vowCageFirstDaiCallFailureBodyCore (acc := (cA_dai, σ_dai))
            (evmDai := evmDaiSolm) (outDai := outDai)
            hcode hwv hauthSolm hliveSolm hdispatch hdecode
            (by simpa using rd2754) houtDaiSize (by simp) hvatCode
            (by simpa using hcallDaiSolm)
        · have rd2754True : RD vowBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
              (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σClearedEvm I ::
                flapCageSelectorWord :: vowAddressReturnWord ⟨2⟩ σClearedEvm I ::
                ⟨412⟩ :: vowSelWord I :: [])
              (outDai.write 0
                (vatDaiCalldataMemFor (vowAddressReturnWord ⟨2⟩ σClearedEvm I)
                  (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
                128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
              (UInt256.ofNat 6) outDai (cA_dai, σ_dai) k2754 C2754 := by
            simpa [σClearedEvm] using rd2754
          have hcallDaiSolmTrue :
              typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
                "dai" 0 [.address (flapFlapperAddressOf evmAsh)]
                (true, evmDaiSolm, outDai) false := by
            simpa using hcallDaiSolm
          have rd2754TruePost : RD vowBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
              (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σ_dai I ::
                flapCageSelectorWord :: vowAddressReturnWord ⟨2⟩ σClearedEvm I ::
                ⟨412⟩ :: vowSelWord I :: [])
              (outDai.write 0
                (vatDaiCalldataMemFor (vowAddressReturnWord ⟨2⟩ σClearedEvm I)
                  (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
                128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
              (UInt256.ofNat 6) outDai (cA_dai, σ_dai) k2754 C2754 := by
            simpa [hDaiTargetPostEvm] using rd2754True
          let baseDai :=
            vatDaiCalldataMemFor (vowAddressReturnWord ⟨2⟩ σClearedEvm I)
              (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
          have hbaseDai : baseDai.size = 164 := by
            simpa [baseDai] using
              vatDaiCalldataMemFor_size_of_size96
                (vowAddressReturnWord ⟨2⟩ σClearedEvm I) hmemAuth
          have hbaseDaiRead64 :
              baseDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
            simpa [baseDai] using
              vatDaiCalldataMemFor_read64_of_size96
                (vowAddressReturnWord ⟨2⟩ σClearedEvm I) hmemAuth hread64
          by_cases ho32Dai : 32 ≤ outDai.size
          · let flapperDai : UInt256 :=
              UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32))
            obtain ⟨_, _, rd2795⟩ :=
              RD.vowCageFirstDaiPostCallDecodeOk
                (acc := (cA_dai, σ_dai))
                (mem := twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
                (target := vowAddressReturnWord ⟨2⟩ σClearedEvm I)
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
            have hcreatedDai : evmDaiSolm.createdAccounts = cA_dai := by
              simp [evmDaiSolm]
            have hσ0Dai : evmDaiSolm.σ₀ = σ₀ := by
              simp [evmDaiSolm, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_σ₀]
            have hblocksDai : evmDaiSolm.blocks = bl := by
              simp [evmDaiSolm, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_blocks]
            have hgenesisDai : evmDaiSolm.genesisBlockHeader = gh := by
              simp [evmDaiSolm, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_genesisBlockHeader]
            have henvDai : evmDaiSolm.executionEnv = I := by
              simp [evmDaiSolm, evmAsh, evmSin, evmLive, evm0, initState,
                storageStore_executionEnv]
            exact cont (evmDai := evmDaiSolm) (outDai := outDai)
              (memDai := memDai) (flapperDai := flapperDai)
                (by simpa [memDai, baseDai, flapperDai, σClearedEvm] using rd2795)
                hmemDai hread64Dai hvatCode hcallDaiSolmTrue hdecDai hauthSolm hliveSolm hdepthLt
                hcreatedDai hσ0Dai hblocksDai hgenesisDai henvDai
                (by simpa [evmDaiEvmOut, evmDaiSolm] using hAccountsDai)
          · have hshortDai : outDai.size < 32 := Nat.lt_of_not_ge ho32Dai
            exact vowCageFirstDaiDecodeShortBodyCore (acc := (cA_dai, σ_dai))
              (evmDai := evmDaiSolm) (base := baseDai) (outDai := outDai)
              hcode hwv hauthSolm hliveSolm hdispatch hdecode rd2754True
              hbaseDai hbaseDaiRead64 houtDaiSize hshortDai (by simp)
              hvatCode hcallDaiSolmTrue
      · have hdepthEq : I.depth = 1024 := by
          apply Fin.ext
          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
          omega
        exact vowCageFirstDaiCallDepthLimitBody hcode hsize hperm hwv hsel hAccounts
          hauthEvm hliveEvm (by simpa [σClearedEvm] using hcodeSizeFirstNE) hdepthEq
    · exact vowCageLiveRevert hcode hsize hperm hwv hsel hAccounts hauthEvm hliveEvm
  · exact vowCageAuthRevert hcode hsize hperm hwv hsel hAccounts hauthEvm

set_option maxHeartbeats 0 in
theorem vowCageBodyToFlopperCage
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_flap : Batteries.RBSet AccountAddress compare} {σ_flap : AccountMap}
        {evmDai evmFlap : EVM.State} {outDai outFlap memFlap : ByteArray}
        {k2881 C2881 : ℕ} {flapperDai : UInt256},
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2881⟩
          (⟨412⟩ :: vowSelWord I :: [])
          memFlap (UInt256.ofNat 6) outFlap (cA_flap, σ_flap) k2881 C2881 →
        memFlap.size = 164 →
        memFlap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
          config.externalABI.decode? "dai" outDai =
            some [.int (Int.ofNat flapperDai.toNat)] →
          vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩ →
          vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ →
          0 < (UInt256.ofNat
          ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
          "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
          true →
        I.depth.val < 1024 →
        evmFlap.createdAccounts = cA_flap →
        evmFlap.σ₀ = σ₀ →
        evmFlap.blocks = bl →
        evmFlap.genesisBlockHeader = gh →
        evmFlap.executionEnv = I →
        accountMapEquiv σ_flap evmFlap.accountMap →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σClearedEvm := vowCageClearedAccountMap I.codeOwner σ_evm
  let σClearedSolm := vowCageClearedAccountMap I.codeOwner σ_solm
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToFlapperCage
      (fun {cA_dai} {σ_dai} {evmDai} {outDai} {memDai} {k2795} {C2795}
          {flapperDai} rd2795 hmemDai hread64Dai hvatCode hcallDai hdecDai
          hauthSolm hliveSolm hdepthLt hcreatedDai hσ0Dai hblocksDai hgenesisDai
          henvDai hAccountsDai => ?_)
      hcode hsize hperm hwv hsel hAccounts
  have hClearedAccounts : accountMapEquiv σClearedEvm σClearedSolm := by
    simpa [σClearedEvm, σClearedSolm] using
      accountMapEquiv_vowCageCleared I.codeOwner hAccounts
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hownerAsh : evmAsh.executionEnv.codeOwner = I.codeOwner := by
    simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
  have hslotFlapperStatic :
      vowAddressReturnWord ⟨2⟩ evmDai.accountMap I =
        vowAddressReturnWord ⟨2⟩ σClearedSolm I := by
    have hslot :=
      typedCallViaEVM_static_storage_findD_of_accountMapEquiv
        (cfg := config) (σ := σClearedSolm) (evm := evmAsh) (evm' := evmDai)
        (target := EVM.address (cageVatAddressOf evmAsh)) (name := "dai")
        (args := [.address (flapFlapperAddressOf evmAsh)]) (z := true)
        (out := outDai) (slot := ⟨2⟩) (default := ⟨0⟩)
        (by
          simpa [evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
            σClearedSolm, vowCageClearedAccountMap] using
            accountMapEquiv_refl σClearedSolm)
        (by simpa [evmAsh, evmSin, evmLive, evm0] using hcallDai)
    simpa [vowAddressReturnWord, vowSlotWord, solcSlotWord, henvDai, hownerAsh] using
      congrArg (fun word => UInt256.land word solcAddrMask) hslot
  have hflapperTarget :
      vowAddressReturnWord ⟨2⟩ σ_dai I =
        vowAddressReturnWord ⟨2⟩ σClearedEvm I := by
    calc
      vowAddressReturnWord ⟨2⟩ σ_dai I =
          vowAddressReturnWord ⟨2⟩ evmDai.accountMap I :=
        cageFlapperTargetWord_accountMapEquiv hAccountsDai
      _ = vowAddressReturnWord ⟨2⟩ σClearedSolm I := hslotFlapperStatic
      _ = vowAddressReturnWord ⟨2⟩ σClearedEvm I :=
        (cageFlapperTargetWord_accountMapEquiv hClearedAccounts).symm
  by_cases hcodeSizeFlapper :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_dai
        (vowAddressReturnWord ⟨2⟩ σClearedEvm I) = ⟨0⟩
  · have hcodeSizeFlapperDai :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_dai
            (vowAddressReturnWord ⟨2⟩ σ_dai I) = ⟨0⟩ := by
      simpa [hflapperTarget] using hcodeSizeFlapper
    have hcodeSizeFlapperSolm :
        Reasoning.Theory.uniswapExtCodeSizeWord evmDai.accountMap
            (vowAddressReturnWord ⟨2⟩ evmDai.accountMap I) = ⟨0⟩ :=
      cageFlapperCodeSize_zero_accountMapEquiv hAccountsDai hcodeSizeFlapperDai
    have hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner := by
      simp [henvDai]
    have hflapperNoCode :
        (UInt256.ofNat
          ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      flapFlapperCode_zero_of_codeSize_zero evmDai I hownerDai hcodeSizeFlapperSolm
    exact vowCageFlapperCageNoCodeBodyCore (acc := (cA_dai, σ_dai))
      (evmDai := evmDai) (target := vowAddressReturnWord ⟨2⟩ σClearedEvm I)
      (ret := ⟨412⟩) (R := [vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa [hflapperTarget] using rd2795) hmemDai hread64Dai
      hcodeSizeFlapper (by simp) hvatCode hcallDai hdecDai hflapperNoCode
  have hcodeSizeFlapperNE :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_dai
        (vowAddressReturnWord ⟨2⟩ σClearedEvm I) ≠ ⟨0⟩ :=
    hcodeSizeFlapper
  have hcodeSizeFlapperDaiNE :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_dai
          (vowAddressReturnWord ⟨2⟩ σ_dai I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeFlapperNE
    simpa [hflapperTarget] using hzero
  have hcodeSizeFlapperSolmNE :
      Reasoning.Theory.uniswapExtCodeSizeWord evmDai.accountMap
          (vowAddressReturnWord ⟨2⟩ evmDai.accountMap I) ≠ ⟨0⟩ :=
    cageFlapperCodeSize_ne_accountMapEquiv hAccountsDai hcodeSizeFlapperDaiNE
  have hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner := by
    simp [henvDai]
  have hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat :=
    flapFlapperCode_pos_of_codeSize_ne evmDai I hownerDai hcodeSizeFlapperSolmNE
  obtain ⟨cA_flap, σ_flap, zFlap, outFlap, A_flap, k2860, C2860, rd2860,
      hcallFlapEvmRaw, houtFlapSize⟩ :=
    RD.vowCageFlapperCageCall
      (cA_call := cA_dai) (σCall := σ_dai)
      (target := vowAddressReturnWord ⟨2⟩ σClearedEvm I)
      (R := [⟨412⟩, vowSelWord I])
      rd2795 hmemDai hread64Dai hcodeSizeFlapperNE hdepthLt hperm
      (cageFlapperAddress_eq_target σClearedEvm I)
      (by simp)
  let evmFlapEvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_dai
      createdAccounts := cA_dai }
  let evmFlapEvmOut :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flap
      substate := A_flap
      createdAccounts := cA_flap }
  have hFlapperAddr :
      flapFlapperAddressOf evmDai =
        AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ evmDai.accountMap I) :=
    flapFlapperAddressOf_eq_vowAddressReturnWord evmDai I hownerDai
  have hFlapperTargetAddr :
      EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σClearedEvm I).toNat) =
        EVM.address (flapFlapperAddressOf evmDai) := by
    calc
      EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σClearedEvm I).toNat) =
          AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ σClearedEvm I) :=
        cageFlapperAddress_eq_target σClearedEvm I
      _ = AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ σ_dai I) := by
        rw [hflapperTarget]
      _ = AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ evmDai.accountMap I) := by
        rw [cageFlapperTargetWord_accountMapEquiv hAccountsDai]
      _ = EVM.address (flapFlapperAddressOf evmDai) := by
        rw [← hFlapperAddr]
        apply Eq.symm
        apply Fin.ext
        simp [EVM.address, EVM.uintN]
        exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
  have hcallFlapEvm :
      typedCallViaEVM config evmFlapEvmIn (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)]
        (zFlap, evmFlapEvmOut, outFlap) true := by
    simpa [evmFlapEvmIn, evmFlapEvmOut, hFlapperTargetAddr] using hcallFlapEvmRaw
  let evmFlapSolmBase := { evmDai with substate := evmFlapEvmIn.substate }
  have hcallCreatedFlap :
      evmFlapSolmBase.createdAccounts = evmFlapEvmIn.createdAccounts := by
    simpa [evmFlapSolmBase, evmFlapEvmIn] using hcreatedDai
  have hcallEnvFlap :
      evmFlapSolmBase.executionEnv = evmFlapEvmIn.executionEnv := by
    simpa [evmFlapSolmBase, evmFlapEvmIn, initState] using henvDai
  obtain ⟨σ_flap_solm, A_flap_solm0, hcallFlapSolmBase, hAccountsFlap⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmFlapSolmBase)
      hcallFlapEvm hAccountsDai
      (by simpa [evmFlapEvmIn, evmFlapSolmBase, initState] using hσ0Dai.symm)
      hcallCreatedFlap
      (by simpa [evmFlapEvmIn, evmFlapSolmBase, initState] using hgenesisDai)
      (by simpa [evmFlapEvmIn, evmFlapSolmBase, initState] using hblocksDai)
      (by simp [evmFlapSolmBase])
      hcallEnvFlap
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepthLt
    norm_num at hdepthLt
  have hdepthNeBaseFlap : evmFlapSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmFlapSolmBase, henvDai] using hdepthNeI
  obtain ⟨A_flap_solm, hcallFlapSolmRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallFlapSolmBase hdepthNeBaseFlap evmDai.substate
  let evmFlapSolm :=
    { evmDai with
      accountMap := σ_flap_solm
      substate := A_flap_solm
      createdAccounts := cA_flap }
  have hcallFlapSolm :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)]
        (zFlap, evmFlapSolm, outFlap) true := by
    simpa [evmFlapSolm, evmFlapSolmBase] using hcallFlapSolmRaw
  cases zFlap
  · exact vowCageFlapperCageCallFailureBodyCore (acc := (cA_flap, σ_flap))
      (evmDai := evmDai) (evmFlap := evmFlapSolm)
      (target := vowAddressReturnWord ⟨2⟩ σClearedEvm I) (ret := ⟨412⟩)
      (R := [vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa using rd2860) houtFlapSize (by simp) hvatCode hcallDai hdecDai
      hflapperCode (by simpa using hcallFlapSolm)
  · have rd2860True : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2860⟩
        (⟨1⟩ :: flapCageEndPtr :: flapCageSelectorWord ::
          vowAddressReturnWord ⟨2⟩ σClearedEvm I :: ⟨412⟩ :: vowSelWord I :: [])
        (flapCageCalldataMem flapperDai memDai)
        (UInt256.ofNat 6) outFlap (cA_flap, σ_flap) k2860 C2860 := by
      simpa using rd2860
    obtain ⟨k2881, C2881, rd2881⟩ :=
      RD.vowCageFlapperCageCallSuccessCleanup rd2860True (by simp)
    let memFlap := flapCageCalldataMem flapperDai memDai
    have hmemFlap : memFlap.size = 164 := by
      simpa [memFlap] using flapCageCalldataMem_size flapperDai hmemDai
    have hread64Flap :
        memFlap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memFlap] using flapCageCalldataMem_read64 flapperDai hmemDai hread64Dai
    have hcallFlapSolmTrue :
        typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
          "cage" 0 [.int (Int.ofNat flapperDai.toNat)]
          (true, evmFlapSolm, outFlap) true := by
      simpa using hcallFlapSolm
    have hcreatedFlap : evmFlapSolm.createdAccounts = cA_flap := by
      simp [evmFlapSolm]
    have hσ0Flap : evmFlapSolm.σ₀ = σ₀ := by
      simpa [evmFlapSolm] using hσ0Dai
    have hblocksFlap : evmFlapSolm.blocks = bl := by
      simpa [evmFlapSolm] using hblocksDai
    have hgenesisFlap : evmFlapSolm.genesisBlockHeader = gh := by
      simpa [evmFlapSolm] using hgenesisDai
    have henvFlap : evmFlapSolm.executionEnv = I := by
      simpa [evmFlapSolm] using henvDai
    exact cont (evmDai := evmDai) (evmFlap := evmFlapSolm) (outDai := outDai)
      (outFlap := outFlap) (memFlap := memFlap) (flapperDai := flapperDai)
      (by simpa [memFlap] using rd2881) hmemFlap hread64Flap hvatCode hcallDai
      hdecDai hauthSolm hliveSolm hflapperCode hcallFlapSolmTrue hdepthLt hcreatedFlap
      hσ0Flap hblocksFlap
      hgenesisFlap henvFlap (by simpa [evmFlapEvmOut, evmFlapSolm] using hAccountsFlap)

set_option maxHeartbeats 0 in
theorem vowCageBodyToSecondDai
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_flop : Batteries.RBSet AccountAddress compare} {σ_flap σ_flop : AccountMap}
        {evmDai evmFlap evmFlop : EVM.State}
        {outDai outFlap outFlop memFlop : ByteArray} {k2983 C2983 : ℕ}
        {flapperDai : UInt256},
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2983⟩
          (flopCageSelectorWord :: vowAddressReturnWord ⟨3⟩ σ_flap I ::
            ⟨412⟩ :: vowSelWord I :: [])
          memFlop (UInt256.ofNat 6) outFlop (cA_flop, σ_flop) k2983 C2983 →
        memFlop.size = 164 →
        memFlop.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat flapperDai.toNat)] →
        vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩ →
        vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ →
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
        I.depth.val < 1024 →
        evmFlop.createdAccounts = cA_flop →
        evmFlop.σ₀ = σ₀ →
        evmFlop.blocks = bl →
        evmFlop.genesisBlockHeader = gh →
        evmFlop.executionEnv = I →
        accountMapEquiv σ_flop evmFlop.accountMap →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToFlopperCage
      (fun {cA_flap} {σ_flap} {evmDai} {evmFlap} {outDai} {outFlap}
          {memFlap} {k2881} {C2881} {flapperDai} rd2881 hmemFlap hread64Flap
          hvatCode hcallDai hdecDai hauthSolm hliveSolm hflapperCode hcallFlap
          hdepthLt hcreatedFlap hσ0Flap hblocksFlap hgenesisFlap henvFlap
          hAccountsFlap => ?_)
      hcode hsize hperm hwv hsel hAccounts
  by_cases hcodeSizeFlopper :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_flap
        (vowAddressReturnWord ⟨3⟩ σ_flap I) = ⟨0⟩
  · have hcodeSizeFlopperSolm :
        Reasoning.Theory.uniswapExtCodeSizeWord evmFlap.accountMap
            (vowAddressReturnWord ⟨3⟩ evmFlap.accountMap I) = ⟨0⟩ :=
      cageFlopperCodeSize_zero_accountMapEquiv hAccountsFlap hcodeSizeFlopper
    have hownerFlap : evmFlap.executionEnv.codeOwner = I.codeOwner := by
      simp [henvFlap]
    have hflopperNoCode :
        (UInt256.ofNat
          ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      cageFlopperCode_zero_of_codeSize_zero evmFlap I hownerFlap hcodeSizeFlopperSolm
    exact vowCageFlopperCageNoCodeBodyCore (acc := (cA_flap, σ_flap))
      (evmDai := evmDai) (evmFlap := evmFlap) (flapperDai := flapperDai)
      (ret := ⟨412⟩) (R := [vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa using rd2881) hmemFlap hread64Flap hcodeSizeFlopper (by simp)
      hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperNoCode
  have hcodeSizeFlopperNE :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_flap
        (vowAddressReturnWord ⟨3⟩ σ_flap I) ≠ ⟨0⟩ :=
    hcodeSizeFlopper
  have hcodeSizeFlopperSolmNE :
      Reasoning.Theory.uniswapExtCodeSizeWord evmFlap.accountMap
          (vowAddressReturnWord ⟨3⟩ evmFlap.accountMap I) ≠ ⟨0⟩ :=
    cageFlopperCodeSize_ne_accountMapEquiv hAccountsFlap hcodeSizeFlopperNE
  have hownerFlap : evmFlap.executionEnv.codeOwner = I.codeOwner := by
    simp [henvFlap]
  have hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat :=
    cageFlopperCode_pos_of_codeSize_ne evmFlap I hownerFlap hcodeSizeFlopperSolmNE
  obtain ⟨cA_flop, σ_flop, zFlop, outFlop, A_flop, k2964, C2964, rd2964,
      hcallFlopEvmRaw, houtFlopSize⟩ :=
    RD.vowCageFlopperCageCall
      (cA_call := cA_flap) (σCall := σ_flap) (R := [vowSelWord I])
      rd2881 hmemFlap hread64Flap hcodeSizeFlopperNE hdepthLt hperm (by simp)
  let evmFlopEvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flap
      createdAccounts := cA_flap }
  let evmFlopEvmOut :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flop
      substate := A_flop
      createdAccounts := cA_flop }
  have hFlopperAddr :
      flopFlopperAddressOf evmFlap =
        AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ evmFlap.accountMap I) :=
    cageFlopperAddressOf_eq_vowAddressReturnWord evmFlap I hownerFlap
  have hFlopperTargetAddr :
      EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨3⟩ σ_flap I).toNat) =
        EVM.address (flopFlopperAddressOf evmFlap) := by
    calc
      EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨3⟩ σ_flap I).toNat) =
          AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ σ_flap I) :=
        cageFlopperAddress_eq_target σ_flap I
      _ = AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ evmFlap.accountMap I) := by
        rw [cageFlopperTargetWord_accountMapEquiv hAccountsFlap]
      _ = EVM.address (flopFlopperAddressOf evmFlap) := by
        rw [← hFlopperAddr]
        apply Eq.symm
        apply Fin.ext
        simp [EVM.address, EVM.uintN]
        exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
  have hcallFlopEvm :
      typedCallViaEVM config evmFlopEvmIn (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (zFlop, evmFlopEvmOut, outFlop) true := by
    simpa [evmFlopEvmIn, evmFlopEvmOut, hFlopperTargetAddr] using hcallFlopEvmRaw
  let evmFlopSolmBase := { evmFlap with substate := evmFlopEvmIn.substate }
  have hcallCreatedFlop :
      evmFlopSolmBase.createdAccounts = evmFlopEvmIn.createdAccounts := by
    simpa [evmFlopSolmBase, evmFlopEvmIn] using hcreatedFlap
  have hcallEnvFlop :
      evmFlopSolmBase.executionEnv = evmFlopEvmIn.executionEnv := by
    simpa [evmFlopSolmBase, evmFlopEvmIn, initState] using henvFlap
  obtain ⟨σ_flop_solm, A_flop_solm0, hcallFlopSolmBase, hAccountsFlop⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmFlopSolmBase)
      hcallFlopEvm hAccountsFlap
      (by simpa [evmFlopEvmIn, evmFlopSolmBase, initState] using hσ0Flap.symm)
      hcallCreatedFlop
      (by simpa [evmFlopEvmIn, evmFlopSolmBase, initState] using hgenesisFlap)
      (by simpa [evmFlopEvmIn, evmFlopSolmBase, initState] using hblocksFlap)
      (by simp [evmFlopSolmBase])
      hcallEnvFlop
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepthLt
    norm_num at hdepthLt
  have hdepthNeBaseFlop : evmFlopSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmFlopSolmBase, henvFlap] using hdepthNeI
  obtain ⟨A_flop_solm, hcallFlopSolmRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallFlopSolmBase hdepthNeBaseFlop
      evmFlap.substate
  let evmFlopSolm :=
    { evmFlap with
      accountMap := σ_flop_solm
      substate := A_flop_solm
      createdAccounts := cA_flop }
  have hcallFlopSolm :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (zFlop, evmFlopSolm, outFlop) true := by
    simpa [evmFlopSolm, evmFlopSolmBase] using hcallFlopSolmRaw
  cases zFlop
  · exact vowCageFlopperCageCallFailureBodyCore (acc := (cA_flop, σ_flop))
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlopSolm)
      (target := vowAddressReturnWord ⟨3⟩ σ_flap I) (ret := ⟨412⟩)
      (R := [vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa using rd2964) houtFlopSize (by simp) hvatCode hcallDai hdecDai
      hflapperCode hcallFlap hflopperCode (by simpa using hcallFlopSolm)
  · have rd2964True : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2964⟩
        (⟨1⟩ :: flopCageEndPtr :: flopCageSelectorWord ::
          vowAddressReturnWord ⟨3⟩ σ_flap I :: ⟨412⟩ :: vowSelWord I :: [])
        (flopCageCalldataMem memFlap)
        (UInt256.ofNat 6) outFlop (cA_flop, σ_flop) k2964 C2964 := by
      simpa using rd2964
    obtain ⟨k2983, C2983, rd2983⟩ :=
      RD.vowCageFlopperCageCallSuccessCleanup rd2964True (by simp)
    let memFlop := flopCageCalldataMem memFlap
    have hmemFlop : memFlop.size = 164 := by
      simpa [memFlop] using flopCageCalldataMem_size hmemFlap
    have hread64Flop :
        memFlop.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memFlop] using flopCageCalldataMem_read64 hmemFlap hread64Flap
    have hcallFlopSolmTrue :
        typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
          "cage" 0 [] (true, evmFlopSolm, outFlop) true := by
      simpa using hcallFlopSolm
    have hcreatedFlop : evmFlopSolm.createdAccounts = cA_flop := by
      simp [evmFlopSolm]
    have hσ0Flop : evmFlopSolm.σ₀ = σ₀ := by
      simpa [evmFlopSolm] using hσ0Flap
    have hblocksFlop : evmFlopSolm.blocks = bl := by
      simpa [evmFlopSolm] using hblocksFlap
    have hgenesisFlop : evmFlopSolm.genesisBlockHeader = gh := by
      simpa [evmFlopSolm] using hgenesisFlap
    have henvFlop : evmFlopSolm.executionEnv = I := by
      simpa [evmFlopSolm] using henvFlap
    exact cont (σ_flap := σ_flap) (evmDai := evmDai) (evmFlap := evmFlap)
      (evmFlop := evmFlopSolm) (outDai := outDai) (outFlap := outFlap)
      (outFlop := outFlop) (memFlop := memFlop) (flapperDai := flapperDai)
      (by simpa [memFlop] using rd2983) hmemFlop hread64Flop hvatCode hcallDai
      hdecDai hauthSolm hliveSolm hflapperCode hcallFlap hflopperCode hcallFlopSolmTrue
      hdepthLt hcreatedFlop hσ0Flop hblocksFlop hgenesisFlop henvFlop
      (by simpa [evmFlopEvmOut, evmFlopSolm] using hAccountsFlop)

set_option maxHeartbeats 0 in
theorem vowCageBodyToVatSin
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_dai2 : Batteries.RBSet AccountAddress compare} {σ_dai2 : AccountMap}
        {evmDai evmFlap evmFlop evmDai2 : EVM.State}
        {outDai outFlap outFlop outDai2 memDai2 : ByteArray} {k3115 C3115 : ℕ}
        {flapperDai vatDai : UInt256},
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3115⟩
          (vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord σ_dai2 I ::
            ⟨412⟩ :: vowSelWord I :: [])
          memDai2 (UInt256.ofNat 6) outDai2 (cA_dai2, σ_dai2) k3115 C3115 →
        memDai2.size = 164 →
        memDai2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         0 < (UInt256.ofNat
           ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
             (fun acc => acc.code.size))).toNat) →
        (let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
         let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
         let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
         let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
         typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
           "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
           false) →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat flapperDai.toNat)] →
        vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩ →
        vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ →
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
        I.depth.val < 1024 →
        evmDai2.createdAccounts = cA_dai2 →
        evmDai2.σ₀ = σ₀ →
        evmDai2.blocks = bl →
        evmDai2.genesisBlockHeader = gh →
        evmDai2.executionEnv = I →
        accountMapEquiv σ_dai2 evmDai2.accountMap →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  refine vowCageBodyToSecondDai
      (fun {cA_flop} {σ_flap} {σ_flop} {evmDai} {evmFlap} {evmFlop}
          {outDai} {outFlap} {outFlop} {memFlop} {k2983} {C2983}
          {flapperDai} rd2983 hmemFlop hread64Flop hvatCode hcallDai hdecDai
          hauthSolm hliveSolm hflapperCode hcallFlap hflopperCode hcallFlop
          hdepthLt hcreatedFlop hσ0Flop hblocksFlop hgenesisFlop henvFlop
          hAccountsFlop => ?_)
      hcode hsize hperm hwv hsel hAccounts
  by_cases hcodeSizeVat :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_flop (kissDaiTargetWord σ_flop I) =
        ⟨0⟩
  · have hcodeSizeVatSolm :
        Reasoning.Theory.uniswapExtCodeSizeWord evmFlop.accountMap
            (kissDaiTargetWord evmFlop.accountMap I) = ⟨0⟩ :=
      cageVatCodeSize_zero_accountMapEquiv hAccountsFlop hcodeSizeVat
    have hownerFlop : evmFlop.executionEnv.codeOwner = I.codeOwner := by
      simp [henvFlop]
    have hvatNoCode :
        (UInt256.ofNat
          ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      cageVatCode_zero_of_codeSize_zero evmFlop I hownerFlop hcodeSizeVatSolm
    exact vowCageSecondDaiNoCodeBodyCore (acc := (cA_flop, σ_flop))
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
      (flapperDai := flapperDai) (d1 := flopCageSelectorWord)
      (d2 := vowAddressReturnWord ⟨3⟩ σ_flap I) (R := [⟨412⟩, vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa using rd2983) hmemFlop hread64Flop hcodeSizeVat (by simp)
      hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
      hvatNoCode
  have hcodeSizeVatNE :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_flop (kissDaiTargetWord σ_flop I) ≠
        ⟨0⟩ :=
    hcodeSizeVat
  have hcodeSizeVatSolmNE :
      Reasoning.Theory.uniswapExtCodeSizeWord evmFlop.accountMap
          (kissDaiTargetWord evmFlop.accountMap I) ≠ ⟨0⟩ :=
    cageVatCodeSize_ne_accountMapEquiv hAccountsFlop hcodeSizeVatNE
  have hownerFlop : evmFlop.executionEnv.codeOwner = I.codeOwner := by
    simp [henvFlop]
  have hvatCode2 :
      0 < (UInt256.ofNat
        ((evmFlop.lookupAccount (cageVatAddressOf evmFlop)).option 0
          (fun acc => acc.code.size))).toNat :=
    cageVatCode_pos_of_codeSize_ne evmFlop I hownerFlop hcodeSizeVatSolmNE
  obtain ⟨cA_dai2, σ_dai2, zDai2, outDai2, A_dai2, k3074, C3074, rd3074,
      hcallDai2EvmRaw, houtDai2Size⟩ :=
    RD.vowCageSecondDaiStaticcall
      (cA_call := cA_flop) (σCall := σ_flop)
      (R := [⟨412⟩, vowSelWord I])
      rd2983 hmemFlop hread64Flop hcodeSizeVatNE hdepthLt (by simp)
  let evmDai2EvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_flop
      createdAccounts := cA_flop }
  let evmDai2EvmOut :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_dai2
      substate := A_dai2
      createdAccounts := cA_dai2 }
  have hcallDai2Evm :
      typedCallViaEVM config evmDai2EvmIn (EVM.address (kissVatAddress σ_flop I))
        "dai" 0 [.address I.codeOwner] (zDai2, evmDai2EvmOut, outDai2) false := by
    simpa [evmDai2EvmIn, evmDai2EvmOut] using hcallDai2EvmRaw
  have hDai2TargetPostEvm : kissDaiTargetWord σ_dai2 I = kissDaiTargetWord σ_flop I := by
    have hslot :=
      typedCallViaEVM_static_storage_findD_of_accountMapEquiv
        (cfg := config) (σ := σ_flop) (evm := evmDai2EvmIn)
        (evm' := evmDai2EvmOut) (target := EVM.address (kissVatAddress σ_flop I))
        (name := "dai") (args := [.address I.codeOwner]) (z := zDai2)
        (out := outDai2) (slot := ⟨1⟩) (default := ⟨0⟩)
        (by simpa [evmDai2EvmIn] using accountMapEquiv_refl σ_flop)
        hcallDai2Evm
    simpa [kissDaiTargetWord, vowSlotWord, evmDai2EvmIn, evmDai2EvmOut, initState] using
      congrArg (fun word => UInt256.land word solcAddrMask) hslot
  have hVatAddrMap : kissVatAddress σ_flop I = kissVatAddress evmFlop.accountMap I :=
    cageVatAddress_accountMapEquiv hAccountsFlop
  have hVatAddrSolm : cageVatAddressOf evmFlop = kissVatAddress evmFlop.accountMap I :=
    cageVatAddressOf_eq_kissVatAddress evmFlop I hownerFlop
  have hVatTargetAddr :
      EVM.address (kissVatAddress σ_flop I) =
        EVM.address (cageVatAddressOf evmFlop) := by
    rw [hVatAddrMap, ← hVatAddrSolm]
  have hVatTargetAddrFlop :
      EVM.address (kissVatAddress σ_flop evmFlop.executionEnv) =
        EVM.address (cageVatAddressOf evmFlop) := by
    simpa [← henvFlop] using hVatTargetAddr
  let evmDai2SolmBase := { evmFlop with substate := evmDai2EvmIn.substate }
  have hcallCreatedDai2 :
      evmDai2SolmBase.createdAccounts = evmDai2EvmIn.createdAccounts := by
    simpa [evmDai2SolmBase, evmDai2EvmIn] using hcreatedFlop
  have hcallEnvDai2 :
      evmDai2SolmBase.executionEnv = evmDai2EvmIn.executionEnv := by
    simpa [evmDai2SolmBase, evmDai2EvmIn, initState] using henvFlop
  obtain ⟨σ_dai2_solm, A_dai2_solm0, hcallDai2SolmBase, hAccountsDai2⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmDai2SolmBase)
      hcallDai2Evm hAccountsFlop
      (by simpa [evmDai2EvmIn, evmDai2SolmBase, initState] using hσ0Flop.symm)
      hcallCreatedDai2
      (by simpa [evmDai2EvmIn, evmDai2SolmBase, initState] using hgenesisFlop)
      (by simpa [evmDai2EvmIn, evmDai2SolmBase, initState] using hblocksFlop)
      (by simp [evmDai2SolmBase])
      hcallEnvDai2
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepthLt
    norm_num at hdepthLt
  have hdepthNeBaseDai2 : evmDai2SolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmDai2SolmBase, henvFlop] using hdepthNeI
  obtain ⟨A_dai2_solm, hcallDai2SolmRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallDai2SolmBase hdepthNeBaseDai2
      evmFlop.substate
  let evmDai2Solm :=
    { evmFlop with
      accountMap := σ_dai2_solm
      substate := A_dai2_solm
      createdAccounts := cA_dai2 }
  have hcallDai2Solm :
      typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
        "dai" 0 [.address evmFlop.executionEnv.codeOwner]
        (zDai2, evmDai2Solm, outDai2) false := by
    simpa [evmDai2Solm, evmDai2SolmBase, evmDai2EvmOut, hVatTargetAddrFlop, ← henvFlop]
      using hcallDai2SolmRaw
  cases zDai2
  · exact vowCageSecondDaiCallFailureBodyCore (acc := (cA_dai2, σ_dai2))
      (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
      (evmDai2 := evmDai2Solm) (target := kissDaiTargetWord σ_flop I)
      (R := [⟨412⟩, vowSelWord I])
      hcode hwv hauthSolm hliveSolm hdispatch hdecode
      (by simpa using rd3074) houtDai2Size (by simp) hvatCode hcallDai hdecDai
      hflapperCode hcallFlap hflopperCode hcallFlop hvatCode2
      (by simpa using hcallDai2Solm)
  · have rd3074True : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3074⟩
        (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord σ_flop I ::
          ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord σ_flop I ::
          ⟨412⟩ :: vowSelWord I :: [])
        (outDai2.write 0 (vatDaiCalldataMem I memFlop) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai2.size)).toNat)
        (UInt256.ofNat 6) outDai2 (cA_dai2, σ_dai2) k3074 C3074 := by
      simpa using rd3074
    have hcallDai2SolmTrue :
        typedCallViaEVM config evmFlop (EVM.address (cageVatAddressOf evmFlop))
          "dai" 0 [.address evmFlop.executionEnv.codeOwner]
          (true, evmDai2Solm, outDai2) false := by
      simpa using hcallDai2Solm
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
        kissDaiMin32_toNat_of_ge ho32Dai2 houtDai2Size
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
          (if (⟨64⟩ : UInt256).toNat ≥ memDai2.size
              ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat
             (fromByteArrayBigEndian
              (memDai2.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
            ⟨128⟩ :=
        mloadFreePtrValue (by rw [hmemDai2]; decide) (by decide) hread64Dai2
      have hmload128 :
          (if (⟨128⟩ : UInt256).toNat ≥ memDai2.size
              ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat
             (fromByteArrayBigEndian
              (memDai2.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
            UInt256.ofNat (fromByteArrayBigEndian (outDai2.extract 0 32)) := by
        have hnot :
            ¬ ((⟨128⟩ : UInt256).toNat ≥ memDai2.size
                ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
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
      have hcreatedDai2 : evmDai2Solm.createdAccounts = cA_dai2 := by
        simp [evmDai2Solm]
      have hσ0Dai2 : evmDai2Solm.σ₀ = σ₀ := by
        simpa [evmDai2Solm] using hσ0Flop
      have hblocksDai2 : evmDai2Solm.blocks = bl := by
        simpa [evmDai2Solm] using hblocksFlop
      have hgenesisDai2 : evmDai2Solm.genesisBlockHeader = gh := by
        simpa [evmDai2Solm] using hgenesisFlop
      have henvDai2 : evmDai2Solm.executionEnv = I := by
        simpa [evmDai2Solm] using henvFlop
      exact cont (σ_dai2 := σ_dai2) (evmDai := evmDai) (evmFlap := evmFlap)
        (evmFlop := evmFlop)
        (evmDai2 := evmDai2Solm) (outDai := outDai) (outFlap := outFlap)
        (outFlop := outFlop) (outDai2 := outDai2) (memDai2 := memDai2)
        (flapperDai := flapperDai) (vatDai := vatDai)
        (by simpa [vatDai, memDai2, hDai2TargetPostEvm] using rd3115)
        hmemDai2 hread64Dai2 hvatCode
        hcallDai hdecDai hauthSolm hliveSolm hflapperCode hcallFlap hflopperCode
        hcallFlop hvatCode2 hcallDai2SolmTrue hdecDai2 hdepthLt hcreatedDai2 hσ0Dai2
        hblocksDai2 hgenesisDai2 henvDai2
        (by simpa [evmDai2EvmOut, evmDai2Solm] using hAccountsDai2)
    · have hshortDai2 : outDai2.size < 32 := Nat.lt_of_not_ge ho32Dai2
      exact vowCageSecondDaiDecodeShortBodyCore (acc := (cA_dai2, σ_dai2))
        (evmDai := evmDai) (evmFlap := evmFlap) (evmFlop := evmFlop)
        (evmDai2 := evmDai2Solm) (base := baseDai2) (outDai := outDai)
        (outFlap := outFlap) (outFlop := outFlop) (outDai2 := outDai2)
        (target := kissDaiTargetWord σ_flop I) (R := [⟨412⟩, vowSelWord I])
        hcode hwv hauthSolm hliveSolm hdispatch hdecode rd3074True
        hbaseDai2 hbaseDai2Read64 houtDai2Size hshortDai2 (by simp)
        hvatCode hcallDai hdecDai hflapperCode hcallFlap hflopperCode hcallFlop
        hvatCode2 hcallDai2SolmTrue

end Benchmarks.Dss.Vow

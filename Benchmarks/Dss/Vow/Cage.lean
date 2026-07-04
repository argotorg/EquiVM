import Benchmarks.Dss.Vow.Rely
import Benchmarks.Dss.Vow.VatDaiCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` -/

abbrev cageAfterLive : List Stmt :=
  [ .assign .storage liveRef (.intLit 0),
    .assign .storage SinRef (.intLit 0),
    .assign .storage AshRef (.intLit 0) ] ++
  checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [.storage flapperRef]
    "flapperDai" (perm := false) ++
  checkedExternalCallStmts (.storage flapperRef) "cage" (.intLit 0)
    [.var "flapperDai"] "_flapCageRet" ++
  checkedExternalCallStmts (.storage flopperRef) "cage" (.intLit 0) [] "_flopCageRet" ++
  checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
    (perm := false) ++
  checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
    (perm := false) ++
  [ .internalCall "min" [.var "vatDai", .var "vatSin"] "healRad" ] ++
  checkedExternalCallStmts (.storage vatRef) "heal" (.intLit 0) [.var "healRad"] "_healRet"

abbrev cageAfterAuth : List Stmt :=
  .require (.binary .eq (.storage liveRef) (.intLit 1)) :: cageAfterLive

abbrev vowCageClearedAccountMap (owner : AccountAddress) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap owner
    (sstoreAccountMap owner (sstoreAccountMap owner σ ⟨12⟩ ⟨0⟩) ⟨5⟩ ⟨0⟩)
    ⟨6⟩ ⟨0⟩

theorem accountMapEquiv_vowCageCleared {σ τ : AccountMap} (owner : AccountAddress)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (vowCageClearedAccountMap owner σ) (vowCageClearedAccountMap owner τ) := by
  exact accountMapEquiv_sstoreAccountMap_three owner owner owner
    ⟨12⟩ ⟨0⟩ ⟨5⟩ ⟨0⟩ ⟨6⟩ ⟨0⟩ hστ

abbrev flapCageSelectorWord : UInt256 :=
  ⟨2734234354⟩

abbrev flapCageSelectorShifted : UInt256 :=
  UInt256.land (UInt256.shiftLeft flapCageSelectorWord ⟨224⟩)
    (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))

abbrev flapCageOutPtr : UInt256 := ⟨128⟩

abbrev flapCageInSize : UInt256 := ⟨36⟩

abbrev flapCageOutSize : UInt256 := ⟨0⟩

abbrev flapCageEndPtr : UInt256 := ⟨164⟩

noncomputable def flapCageSelectorMem (mem : ByteArray) : ByteArray :=
  flapCageSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def flapCageCalldataMem (rad : UInt256) (mem : ByteArray) : ByteArray :=
  rad.toByteArray.write 0 (flapCageSelectorMem mem) 132 32

theorem flapCageSelectorMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (flapCageSelectorMem mem).size = 164 := by
  unfold flapCageSelectorMem
  exact toByteArray_write32_size_of_le mem flapCageSelectorShifted 128 164 164 hmem
    (by rw [hmem]; omega) (by omega)

theorem flapCageCalldataMem_size (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (flapCageCalldataMem rad mem).size = 164 := by
  unfold flapCageCalldataMem
  exact toByteArray_write32_size_of_le (flapCageSelectorMem mem) rad 132 164 164
    (flapCageSelectorMem_size hmem)
    (by rw [flapCageSelectorMem_size hmem]; omega)
    (by omega)

theorem flapCageSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flapCageSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flapCageSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega), hread64]

theorem flapCageCalldataMem_read64 (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flapCageCalldataMem rad mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold flapCageCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [flapCageSelectorMem_size hmem]; omega) (by omega),
    flapCageSelectorMem_read64 hmem hread64]

theorem flapCageSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 164) :
    (flapCageSelectorMem mem).extract 128 132 = flapCageSelector := by
  unfold flapCageSelectorMem
  rw [write32_eq _ mem 128 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  have hAsz : (mem.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, hmem]
    omega
  have hBsz : (flapCageSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  rw [show
      (mem.extract 0 128 ++ flapCageSelectorShifted.toByteArray.extract 0 32 ++
          mem.extract (128 + 32) mem.size) =
        (mem.extract 0 128 ++
          (flapCageSelectorShifted.toByteArray.extract 0 32 ++
            mem.extract (128 + 32) mem.size)) by
    apply ByteArray.ext
    simp [ByteArray.data_append, Array.append_assoc]]
  rw [extract_append_right_window _ _ 128 132 (by rw [hAsz]), hAsz,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    extract_append_left _ _ 0 4 (by rw [hBsz]; omega), extract_extract_BA,
    show (0 : ℕ) + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega]
  native_decide

theorem flapCageCalldataMem_read128_36 (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (flapCageCalldataMem rad mem).readWithPadding 128 36 =
      flapCageSelector ++ rad.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [flapCageCalldataMem_size rad hmem]), flapCageCalldataMem,
    write32_eq _ (flapCageSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [flapCageSelectorMem_size hmem]; omega)]
  have hAsz : ((flapCageSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, flapCageSelectorMem_size hmem]
    omega
  have hBsz : (rad.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((flapCageSelectorMem mem).extract 0 132 ++ rad.toByteArray.extract 0 32).size =
        164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : rad.toByteArray.extract 0 32 = rad.toByteArray := by
    have h := @ByteArray.extract_zero_size rad.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), flapCageSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem flapCageEncode_eq (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    config.externalABI.encode? "cage" [.int (Int.ofNat rad.toNat)] =
      some ((flapCageCalldataMem rad mem).readWithPadding
        flapCageOutPtr.toNat flapCageInSize.toNat) := by
  change config.externalABI.encode? "cage" [.int (Int.ofNat rad.toNat)] =
    some ((flapCageCalldataMem rad mem).readWithPadding 128 36)
  rw [flapCageCalldataMem_read128_36 rad hmem]
  have hradLt : rad.toNat < EVM.twoPow 256 := rad.val.isLt
  have hradWord : EVM.word rad.toNat = rad := by
    show UInt256.ofNat rad.toNat = rad
    exact u256_ofNat_toNat _
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    uint256, uint256Int, flapCageSelector, selectorBytes, hradLt, hradWord]
  apply ByteArray.ext
  simp [word_toBytesBE_toByteArray_eq_toByteArray]

abbrev flopCageSelectorWord : UInt256 :=
  ⟨1763987465⟩

abbrev flopCageSelectorShifted : UInt256 :=
  UInt256.shiftLeft (UInt256.land flopCageSelectorWord ⟨4294967295⟩) ⟨224⟩

abbrev flopCageOutPtr : UInt256 := ⟨128⟩

abbrev flopCageInSize : UInt256 := ⟨4⟩

abbrev flopCageOutSize : UInt256 := ⟨0⟩

abbrev flopCageEndPtr : UInt256 := ⟨132⟩

noncomputable def flopCageCalldataMem (mem : ByteArray) : ByteArray :=
  flopCageSelectorShifted.toByteArray.write 0 mem 128 32

theorem flopCageCalldataMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (flopCageCalldataMem mem).size = 164 := by
  unfold flopCageCalldataMem
  exact toByteArray_write32_size_of_le mem flopCageSelectorShifted 128 164 164 hmem
    (by rw [hmem]; omega) (by omega)

theorem flopCageCalldataMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flopCageCalldataMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold flopCageCalldataMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega), hread64]

theorem flopCageCalldataMem_selector {mem : ByteArray} (hmem : mem.size = 164) :
    (flopCageCalldataMem mem).extract 128 132 = flopCageSelector := by
  unfold flopCageCalldataMem
  rw [write32_eq _ mem 128 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  have hAsz : (mem.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, hmem]
    omega
  have hBsz : (flopCageSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  rw [show
      (mem.extract 0 128 ++ flopCageSelectorShifted.toByteArray.extract 0 32 ++
          mem.extract (128 + 32) mem.size) =
        (mem.extract 0 128 ++
          (flopCageSelectorShifted.toByteArray.extract 0 32 ++
            mem.extract (128 + 32) mem.size)) by
    apply ByteArray.ext
    simp [ByteArray.data_append, Array.append_assoc]]
  rw [extract_append_right_window _ _ 128 132 (by rw [hAsz]), hAsz,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    extract_append_left _ _ 0 4 (by rw [hBsz]; omega), extract_extract_BA,
    show (0 : ℕ) + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega]
  native_decide

theorem flopCageCalldataMem_read128_4 {mem : ByteArray} (hmem : mem.size = 164) :
    (flopCageCalldataMem mem).readWithPadding 128 4 = flopCageSelector := by
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [flopCageCalldataMem_size hmem]; norm_num),
    flopCageCalldataMem_selector hmem]

theorem flopCageEncode_eq {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "cage" [] =
      some ((flopCageCalldataMem mem).readWithPadding
        flopCageOutPtr.toNat flopCageInSize.toNat) := by
  change config.externalABI.encode? "cage" [] =
    some ((flopCageCalldataMem mem).readWithPadding 128 4)
  rw [flopCageCalldataMem_read128_4 hmem]
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, flopCageSelector]

theorem cageFlopperAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨3⟩ σ I).toNat) =
      AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simp [EVM.twoPow, AccountAddress.size])

theorem u256_div_one (w : UInt256) :
    UInt256.div w ⟨1⟩ = w := by
  apply u256_inj
  rw [udiv_toNat]
  exact Nat.div_one w.toNat

theorem solcAddrMask_idem_left (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land w solcAddrMask) =
      UInt256.land w solcAddrMask := by
  exact solcAddrMask_clean_left (solcAddrMask_result_canonical w)

theorem solcAddrMask_idem_right (w : UInt256) :
    UInt256.land (UInt256.land w solcAddrMask) solcAddrMask =
      UInt256.land w solcAddrMask := by
  exact solcAddrMask_clean (solcAddrMask_result_canonical w)

theorem solcAddrMask_idem_left_left (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land solcAddrMask w := by
  rw [u256_land_comm solcAddrMask w]
  rw [solcAddrMask_idem_left w]

abbrev cageSinEvaledRef : EvaledStorageRef :=
  { base := "Sin", steps := [] }

abbrev cageAshEvaledRef : EvaledStorageRef :=
  { base := "Ash", steps := [] }

theorem assign_cageLiveStorage (evm : EVM.State) {locals : Store} (value : UInt256)
    (hbase : locals.get? "live" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨12⟩ value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm liveRef =
        .ok liveEvaledRef := by
    simp [liveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨12⟩) (.int (Int.ofNat value.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨12⟩ value
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨12⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, liveEvaledRef])
    (hstore := hstore)

theorem assign_cageSinStorage (evm : EVM.State) {locals : Store} (value : UInt256)
    (hbase : locals.get? "Sin" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage SinRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm SinRef =
        .ok cageSinEvaledRef := by
    simp [cageSinEvaledRef, SinRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨5⟩) (.int (Int.ofNat value.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨5⟩ value
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, cageSinEvaledRef])
    (hstore := hstore)

theorem assign_cageAshStorage (evm : EVM.State) {locals : Store} (value : UInt256)
    (hbase : locals.get? "Ash" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage AshRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm AshRef =
        .ok cageAshEvaledRef := by
    simp [cageAshEvaledRef, AshRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨6⟩) (.int (Int.ofNat value.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨6⟩ value
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, cageAshEvaledRef])
    (hstore := hstore)

theorem vowCageSourceClearPrefix {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩) :
    let locals : Store := ∅
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
    let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
    let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
    ExecBlock config { contract := contract, locals := locals } evm0
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
        [ .assign .storage liveRef (.intLit 0),
          .assign .storage SinRef (.intLit 0),
          .assign .storage AshRef (.intLit 0) ])
      (.ok { contract := contract, locals := locals } evmAsh) := by
  intro locals evm0 evmLive evmSin evmAsh
  have hguardAuth := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simp [locals]) hauth
  have hguardLive := vowLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simp [locals]) hlive
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage liveRef (.int 0) =
          .ok ({ contract := contract, locals := locals }, evmLive) := by
    simpa [evmLive] using
      assign_cageLiveStorage evm0 (locals := locals) (⟨0⟩ : UInt256) (by simp [locals])
  have hassignSin :
      assignStorageRef? config { contract := contract, locals := locals } evmLive
        .storage SinRef (.int 0) =
          .ok ({ contract := contract, locals := locals }, evmSin) := by
    simpa [evmSin, evmLive, storageStore_executionEnv] using
      assign_cageSinStorage evmLive (locals := locals) (⟨0⟩ : UInt256) (by simp [locals])
  have hassignAsh :
      assignStorageRef? config { contract := contract, locals := locals } evmSin
        .storage AshRef (.int 0) =
          .ok ({ contract := contract, locals := locals }, evmAsh) := by
    simpa [evmAsh, evmSin, evmLive, storageStore_executionEnv] using
      assign_cageAshStorage evmSin (locals := locals) (⟨0⟩ : UInt256) (by simp [locals])
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignSin) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignAsh)
    ExecBlock.nil

@[reducible] def solcNoArgsExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p7 := p4 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p7 = some (.JUMP, .none)

-- LIBRARY CANDIDATE: solc no-argument external entry thunk
theorem RD.solcNoArgsExternalEntry {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret routine sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc [sel] mem aw rdata acc k C)
    (hwf : solcNoArgsExternalEntryWf code pc ret routine)
    (hroutine : (D_J code 0).contains routine = true) :
    ∃ k' C', RD code ee g s0 routine [ret, sel] mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd4, hd7⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd7 := rd4.push2 routine hd4 (by evm_ov)
  exact ⟨_, _, rd7.jump hd7 hroutine (by evm_ov)⟩

@[reducible] def vowCageClearStoresWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.SSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨5⟩, 1))
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.SWAP1, .none)
  ∧ decode code p12 = some (.SSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨6⟩, 1))
  ∧ decode code p15 = some (.SSTORE, .none)

@[reducible] def vowCageClearStoresOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  p15 + ⟨1⟩

set_option maxHeartbeats 0 in
theorem RD.vowCageClearStores {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowCageClearStoresWf code pc)
    (hperm : ee.perm = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (vowCageClearStoresOutPc pc) (ret :: R) mem
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ⟨12⟩ ⟨0⟩)
          ⟨5⟩ ⟨0⟩)
        ⟨6⟩ ⟨0⟩)
      k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15⟩
  let σ1 := sstoreAccountMap ee.codeOwner σ ⟨12⟩ ⟨0⟩
  let σ2 := sstoreAccountMap ee.codeOwner σ1 ⟨5⟩ ⟨0⟩
  have rdLivePrefix := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push1 ⟨12⟩ hd3 (by evm_ov),
    raw dup2 hd5 (by evm_ov),
    raw swap1 hd6 (by evm_ov)]
  obtain ⟨_, _, rdLive⟩ := rdLivePrefix.sstore hperm hd7 (by evm_ov)
  have rdSinPrefix := evm_run rdLive with [
    raw push1 ⟨5⟩ hd8 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov)]
  obtain ⟨_, _, rdSin⟩ := rdSinPrefix.sstore hperm hd12 (by evm_ov)
  have rdAshPrefix := rdSin.push1 ⟨6⟩ hd13 (by evm_ov)
  obtain ⟨_, _, rdAsh⟩ := rdAshPrefix.sstore hperm hd15 (by evm_ov)
  exact ⟨_, _, by simpa [vowCageClearStoresOutPc, σ1, σ2] using rdAsh⟩

theorem vowDispatch_cage {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    dispatchMsg contract I.calldata = some cageTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition])
    (post := [denyTransition, dumpTransition, fessTransition, fileUintTransition,
      fileAddressTransition, flapTransition, flapperTransition, flogTransition, flopTransition,
      flopperTransition, healTransition, humpTransition, kissTransition, liveTransition,
      relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition])
    (ti := cageTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x69, 0x24, 0x50, 0x09]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, cageSelectorBytes]
    exact hsel

theorem vowDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨563⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨1763987465⟩ :=
    vowSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨1763987465⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc 5))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowHighBody 5 (by omega) ⟨563⟩ hcode hwv hsz hsize hroot hlow heq0
    htake (by jump_dest) (by native_decide)

theorem vowCageReachAfterClear {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2663⟩
      [⟨412⟩, vowSelWord I]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, vowCageClearedAccountMap I.codeOwner σ) k C := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  obtain ⟨_, _, hbodyEntry⟩ :=
    vowReachCageBody (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hsize hsel
  obtain ⟨_, _, hentry⟩ := RD.solcNoArgsExternalEntry
    (code := vowBytecode) (pc := ⟨563⟩) (ret := ⟨412⟩) (routine := ⟨2488⟩)
    hbodyEntry
    (by
      unfold solcNoArgsExternalEntryWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [vowCallerWardsSlot, vowSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
    (code := vowBytecode) (pc := ⟨2488⟩) (okPc := ⟨2577⟩)
    (key := ⟨412⟩) (ret := vowSelWord I) (R := [])
    (by simpa using hentry)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ I ⟨12⟩ = ⟨1⟩ := by
    simpa [vowSlotWord] using hlive
  obtain ⟨_, _, hafterLive⟩ := RD.vowLiveGuardOk
    (code := vowBytecode) (pc := ⟨2577⟩) (okPc := ⟨2647⟩)
    (key := ⟨412⟩) (ret := vowSelWord I) (R := [])
    hafterAuth
    (by
      unfold vowLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)
  obtain ⟨_, _, hafterClear⟩ := RD.vowCageClearStores
    (code := vowBytecode) (pc := ⟨2647⟩) (ret := ⟨412⟩) (R := [vowSelWord I])
    hafterLive
    (by
      unfold vowCageClearStoresWf
      repeat' first | apply And.intro | native_decide)
    hperm (by simp)
  exact ⟨_, _, by simpa [vowCageClearStoresOutPc, vowCageClearedAccountMap] using hafterClear⟩

theorem RD.vowCageFirstDaiLoadTargets {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨2663⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2669⟩
      (solcSlotWord σ ee ⟨1⟩ :: solcSlotWord σ ee ⟨2⟩ :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd2665 := rd.push1 ⟨2⟩ (by native_decide) (by simp; omega)
  obtain ⟨k2666, C2666, rd2666Raw⟩ := rd2665.sload (by native_decide) (by evm_ov)
  have rd2666 : RD vowBytecode ee g s0 ⟨2666⟩
      (solcSlotWord σ ee ⟨2⟩ :: ret :: R) mem aw rdata (cA, σ) k2666 C2666 := by
    simpa [solcSlotWord] using rd2666Raw
  have rd2668 := rd2666.push1 ⟨1⟩ (by native_decide) (by simp; omega)
  obtain ⟨k2669, C2669, rd2669Raw⟩ := rd2668.sload (by native_decide) (by evm_ov)
  exact ⟨k2669, C2669, by simpa [solcSlotWord] using rd2669Raw⟩

set_option maxHeartbeats 0 in
theorem RD.vowCageFirstDaiExtcodesizeGuard {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨2669⟩
      (solcSlotWord σ ee ⟨1⟩ :: solcSlotWord σ ee ⟨2⟩ :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (_hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2738⟩
      (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩) ::
        UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩) ::
        ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩) :: ⟨2734234354⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σ ee ⟨2⟩) :: ret :: R)
      (vatDaiCalldataMemFor (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨2⟩)) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  let vatTarget := UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩)
  let flapperArg := UInt256.land solcAddrMask (solcSlotWord σ ee ⟨2⟩)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hDaiMem : (vatDaiCalldataMemFor flapperArg mem).size = 164 :=
    vatDaiCalldataMemFor_size_of_size96 flapperArg hmem
  have hDaiRead64 :
      (vatDaiCalldataMemFor flapperArg mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    vatDaiCalldataMemFor_read64_of_size96 flapperArg hmem hread64
  have hmload64Dai :
      (if (⟨64⟩ : UInt256).toNat ≥ (vatDaiCalldataMemFor flapperArg mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((vatDaiCalldataMemFor flapperArg mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hDaiMem]; decide) (by decide) hDaiRead64
  have rd2738 := evm_run rd with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨907205027⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (vatDaiSelectorMem mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap4,
    dup5,
    and,
    push1 ⟨4⟩,
    dup3,
    add,
    dup2,
    swap1,
    raw mstore 3 (vatDaiCalldataMemFor flapperArg mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    swap2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Dai (by decide) (by evm_ov),
    swap2,
    swap4,
    push4 ⟨2734234354⟩,
    swap4,
    and,
    swap2,
    push4 ⟨1814410054⟩,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 ⟨32⟩,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup7,
    dup1]
  have hpc2738 :
      (⟨2669⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2738⟩ := by
    native_decide
  rw [hpc2738] at rd2738
  exact ⟨_, _, by
    simpa [vatTarget, flapperArg, vatDaiSelectorMem, vatDaiCalldataMemFor,
      kissDaiSelectorShifted, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩ = ⟨36⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide]
      using rd2738⟩

theorem vowCageReachFirstDaiExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2738⟩
      (UInt256.land solcAddrMask
          (solcSlotWord (vowCageClearedAccountMap I.codeOwner σ) I ⟨1⟩) ::
        UInt256.land solcAddrMask
          (solcSlotWord (vowCageClearedAccountMap I.codeOwner σ) I ⟨1⟩) ::
        ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        UInt256.land solcAddrMask
          (solcSlotWord (vowCageClearedAccountMap I.codeOwner σ) I ⟨1⟩) ::
        ⟨2734234354⟩ ::
        UInt256.land solcAddrMask
          (solcSlotWord (vowCageClearedAccountMap I.codeOwner σ) I ⟨2⟩) ::
        ⟨412⟩ :: vowSelWord I :: [])
      (vatDaiCalldataMemFor
        (UInt256.land solcAddrMask
          (solcSlotWord (vowCageClearedAccountMap I.codeOwner σ) I ⟨2⟩))
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem))
      (UInt256.ofNat 6) ByteArray.empty
      (cA, vowCageClearedAccountMap I.codeOwner σ) k C := by
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, hclear⟩ :=
    vowCageReachAfterClear (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hauth hlive
  obtain ⟨_, _, hloads⟩ := RD.vowCageFirstDaiLoadTargets
    (R := [vowSelWord I]) hclear (by simp)
  obtain ⟨_, _, hguard⟩ := RD.vowCageFirstDaiExtcodesizeGuard
    (R := [vowSelWord I]) hloads hmemAuth hread64 (by simp)
  exact ⟨_, _, by simpa using hguard⟩

theorem RD.vowCageFirstDaiNoCode {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨2669⟩
      (solcSlotWord σ ee ⟨1⟩ :: solcSlotWord σ ee ⟨2⟩ :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ
        (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩)) = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd2738⟩ := RD.vowCageFirstDaiExtcodesizeGuard
    rd hmem hread64 (by omega)
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨2738⟩) (okPc := ⟨2750⟩) rd2738
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp; omega)

theorem RD.vowCageFirstDaiStaticcallSetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨2669⟩
      (solcSlotWord σ ee ⟨1⟩ :: solcSlotWord σ ee ⟨2⟩ :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ
        (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩)) ≠ ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨2753⟩
      (gasWord :: UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩) ::
        ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩) :: ⟨2734234354⟩ ::
        UInt256.land solcAddrMask (solcSlotWord σ ee ⟨2⟩) :: ret :: R)
      (vatDaiCalldataMemFor (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨2⟩)) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd2738⟩ := RD.vowCageFirstDaiExtcodesizeGuard
    rd hmem hread64 (by omega)
  obtain ⟨gasWord, k2753, C2753, rd2753⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2738⟩) (okPc := ⟨2750⟩) rd2738
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp; omega)
  exact ⟨gasWord, k2753, C2753, rd2753⟩

theorem RD.vowCageFirstDaiStaticcall
    {cA gh bl σ σCall σ₀ A I} {g : UInt256} {ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2669⟩
      (solcSlotWord σCall I ⟨1⟩ :: solcSlotWord σCall I ⟨2⟩ :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σCall) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σCall (kissDaiTargetWord σCall I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 14 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outDai : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨1814410054⟩ ::
          kissDaiTargetWord σCall I :: ⟨2734234354⟩ ::
          vowAddressReturnWord ⟨2⟩ σCall I :: ret :: R)
        (outDai.write 0 (vatDaiCalldataMemFor (vowAddressReturnWord ⟨2⟩ σCall I) mem)
          128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
        (UInt256.ofNat 6) outDai (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σCall }
        (EVM.address (kissVatAddress σCall I)) "dai" 0
        [.address (AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σCall I).toNat)]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ'
            substate := A'
            createdAccounts := cA' },
          outDai) false
    ∧ outDai.size < UInt256.size := by
  have hcodeSize' :
      Reasoning.Theory.uniswapExtCodeSizeWord σCall
        (UInt256.land solcAddrMask (solcSlotWord σCall I ⟨1⟩)) ≠ ⟨0⟩ := by
    simpa [kissDaiTargetWord, vowSlotWord, solcSlotWord, u256_land_comm] using hcodeSize
  obtain ⟨gasWord, _, _, rd2753⟩ := RD.vowCageFirstDaiStaticcallSetup
    rd hmem hread64 hcodeSize' hov
  obtain ⟨cA', σ', z, outDai, A_in, callGas, k2754, C2754, hΘpack, rd2754raw,
      houtsz⟩ :=
    RD.uniswapStaticcall rd2753 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmDaiIn := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σCall }
  refine ⟨cA', σ', z, outDai, A', k2754, C2754, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      native_decide
    have rd2754 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨1814410054⟩ ::
          UInt256.land solcAddrMask (solcSlotWord σCall I ⟨1⟩) :: ⟨2734234354⟩ ::
          UInt256.land solcAddrMask (solcSlotWord σCall I ⟨2⟩) :: ret :: R)
        (outDai.write 0
          (vatDaiCalldataMemFor (UInt256.land solcAddrMask (solcSlotWord σCall I ⟨2⟩)) mem)
          128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
        (UInt256.ofNat 6) outDai (cA', σ') k2754 C2754 :=
      haw ▸ rd2754raw
    simpa [kissDaiTargetWord, vowAddressReturnWord, vowSlotWord, solcSlotWord,
      u256_land_comm] using rd2754
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σCall I)
      (mem := vatDaiCalldataMemFor (vowAddressReturnWord ⟨2⟩ σCall I) mem)
      (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmDaiIn, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      (kissVatAddress_eq_daiTarget σCall I) ?_ ?_
    · simpa [vowAddressReturnWord, vowSlotWord, solcSlotWord, u256_land_comm] using
        vatDaiEncodeMasked_eq_of_size96 (solcSlotWord σCall I ⟨2⟩) hmem
    · simpa [evmDaiIn, initState, kissDaiTargetWord, vowAddressReturnWord, vowSlotWord,
        solcSlotWord, u256_land_comm] using hΘ

theorem RD.vowCageFirstDaiCallFailure {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2754⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨2754⟩) (okPc := ⟨2770⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowCageFirstDaiCallSuccessToDecode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2754⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2772⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨2754⟩) (okPc := ⟨2770⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowCageFirstDaiReturnDecodeShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2772⟩
      (d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨2772⟩) (okPc := ⟨2792⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp; omega)

theorem RD.vowCageFirstDaiReturnDecodeOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {retWord d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2772⟩
      (d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 6) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2795⟩
      (retWord :: R) mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨2772⟩) (okPc := ⟨2792⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by simp; omega)

set_option maxHeartbeats 0 in
theorem RD.vowCageFlapperCageExtcodesizeGuard {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {rad target : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2795⟩
      (rad :: flapCageSelectorWord :: target :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (_hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2844⟩
      (target :: target :: flapCageOutSize :: flapCageOutPtr :: flapCageInSize ::
        flapCageOutPtr :: flapCageOutSize :: flapCageEndPtr :: flapCageSelectorWord ::
        target :: R)
      (flapCageCalldataMem rad mem) (UInt256.ofNat 6) rdata acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hCageMem : (flapCageCalldataMem rad mem).size = 164 :=
    flapCageCalldataMem_size rad hmem
  have hCageRead64 :
      (flapCageCalldataMem rad mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    flapCageCalldataMem_read64 rad hmem hread64
  have hmload64Cage :
      (if (⟨64⟩ : UInt256).toNat ≥ (flapCageCalldataMem rad mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((flapCageCalldataMem rad mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hCageMem]; decide) (by decide) hCageRead64
  have rd2844 := evm_run rd with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨224⟩,
    shl,
    sub,
    not,
    push1 ⟨224⟩,
    dup6,
    swap1,
    shl,
    and,
    dup2,
    raw mstore 0 (flapCageSelectorMem mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    swap3,
    swap1,
    swap3,
    raw mstore 0 (flapCageCalldataMem rad mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Cage (by decide) (by evm_ov),
    push1 ⟨36⟩,
    dup1,
    dup4,
    add,
    swap3,
    push1 ⟨0⟩,
    swap3,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  have hpc2844 :
      (⟨2795⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ =
        ⟨2844⟩ := by
    native_decide
  rw [hpc2844] at rd2844
  exact ⟨_, _, by
    simpa [flapCageSelectorWord, flapCageSelectorShifted, flapCageSelectorMem,
      flapCageCalldataMem, flapCageOutPtr, flapCageInSize, flapCageOutSize,
      flapCageEndPtr,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩ = ⟨36⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide]
      using rd2844⟩

theorem RD.vowCageFlapperCageNoCode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {rad target : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2795⟩
      (rad :: flapCageSelectorWord :: target :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord acc.2 target = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd2844⟩ := RD.vowCageFlapperCageExtcodesizeGuard
    rd hmem hread64 hov
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨2844⟩) (okPc := ⟨2856⟩) rd2844
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp; omega)

theorem RD.vowCageFlapperCageCallSetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {rad target : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2795⟩
      (rad :: flapCageSelectorWord :: target :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord acc.2 target ≠ ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨2859⟩
      (gasWord :: target :: flapCageOutSize :: flapCageOutPtr :: flapCageInSize ::
        flapCageOutPtr :: flapCageOutSize :: flapCageEndPtr :: flapCageSelectorWord ::
        target :: R)
      (flapCageCalldataMem rad mem) (UInt256.ofNat 6) rdata acc k' C' := by
  obtain ⟨_, _, rd2844⟩ := RD.vowCageFlapperCageExtcodesizeGuard
    rd hmem hread64 hov
  obtain ⟨gasWord, k', C', rd2859⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2844⟩) (okPc := ⟨2856⟩) rd2844
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp; omega)
  exact ⟨gasWord, k', C', by simpa using rd2859⟩

theorem RD.vowCageFlapperCageCall
    {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {cA_call : Batteries.RBSet AccountAddress compare}
    {mem rdata : ByteArray} {k C : ℕ} {rad target : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2795⟩
      (rad :: flapCageSelectorWord :: target :: R)
      mem (UInt256.ofNat 6) rdata (cA_call, σCall) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σCall target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true)
    (htgt : EVM.address (AccountAddress.ofNat target.toNat) =
      AccountAddress.ofUInt256 target)
    (hov : R.length + 12 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2860⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flapCageEndPtr :: flapCageSelectorWord ::
          target :: R)
        (flapCageCalldataMem rad mem) (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σCall
          createdAccounts := cA_call }
        (EVM.address (AccountAddress.ofNat target.toNat)) "cage" 0
        [.int (Int.ofNat rad.toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'
              substate := A'
              createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd2859⟩ := RD.vowCageFlapperCageCallSetup
    rd hmem hread64 hcodeSize hov
  obtain ⟨cA', σ', z, out, A_in, callGas, k2860, C2860, hΘpack, rd2860raw,
      houtsz⟩ :=
    RD.call (by simpa [flapCageOutSize] using rd2859)
      (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmCall := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σCall
    createdAccounts := cA_call }
  refine ⟨cA', σ', z, out, A', k2860, C2860, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          flapCageOutPtr.toNat flapCageInSize.toNat)
          flapCageOutPtr.toNat flapCageOutSize.toNat) = UInt256.ofNat 6 := by
      unfold flapCageOutPtr flapCageInSize flapCageOutSize
      native_decide
    have hmin : (min flapCageOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold flapCageOutSize
      rfl
    have rd2860 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2860⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flapCageEndPtr :: flapCageSelectorWord ::
          target :: R)
        (out.write 0 (flapCageCalldataMem rad mem) flapCageOutPtr.toNat
          (min flapCageOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k2860 C2860 :=
      haw ▸ rd2860raw
    rw [hmin, byteArray_write_len_zero] at rd2860
    exact rd2860
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target)
      (mem := flapCageCalldataMem rad mem)
      (inOff := flapCageOutPtr) (inSize := flapCageInSize)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmCall, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      htgt (flapCageEncode_eq rad hmem) ?_
    simpa [evmCall, initState, hperm] using hΘ

theorem RD.vowCageFlapperCageCallFailure {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2860⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨2860⟩) (okPc := ⟨2876⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowCageFlapperCageCallSuccessCleanup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2860⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2881⟩ R mem aw o acc k' C' := by
  obtain ⟨_, _, rd2878⟩ := RD.uniswapCallSuccessGuardOk
    (pc := ⟨2860⟩) (okPc := ⟨2876⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)
  have rd2879 := RD.pop rd2878 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd2880 := RD.pop rd2879 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd2881 := RD.pop rd2880 (by native_decide) (by omega)
  exact ⟨_, _, rd2881⟩

set_option maxHeartbeats 0 in
theorem RD.vowCageFlopperCageExtcodesizeGuard {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2881⟩
      (ret :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (_hov : R.length + 15 ≤ 1024) :
    let target := vowAddressReturnWord ⟨3⟩ acc.2 ee
    ∃ k' C', RD vowBytecode ee g s0 ⟨2948⟩
      (target :: target :: flopCageOutSize :: flopCageOutPtr :: flopCageInSize ::
        flopCageOutPtr :: flopCageOutSize :: flopCageEndPtr :: flopCageSelectorWord ::
        target :: ret :: R)
      (flopCageCalldataMem mem) (UInt256.ofNat 6) rdata acc k' C' := by
  intro target
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hCageMem : (flopCageCalldataMem mem).size = 164 :=
    flopCageCalldataMem_size hmem
  have hCageRead64 :
      (flopCageCalldataMem mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    flopCageCalldataMem_read64 hmem hread64
  have hmload64Cage :
      (if (⟨64⟩ : UInt256).toNat ≥ (flopCageCalldataMem mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((flopCageCalldataMem mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hCageMem]; decide) (by decide) hCageRead64
  have rd2883 := rd.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd2885 := rd2883.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2886 := rd2885.swap1 (by native_decide) (by evm_ov)
  obtain ⟨k2887, C2887, rd2887raw⟩ := rd2886.sload (by native_decide) (by evm_ov)
  have rd2887 : RD vowBytecode ee g s0 ⟨2887⟩
      (vowSlotWord ⟨3⟩ acc.2 ee :: ⟨0⟩ :: ret :: R)
      mem (UInt256.ofNat 6) rdata acc k2887 C2887 := by
    simpa [vowSlotWord, solcSlotWord] using rd2887raw
  have rd2948 := evm_run rd2887 with [
    swap1,
    push2 ⟨256⟩,
    exp,
    swap1,
    div,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    and,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    and,
    push4 flopCageSelectorWord,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    dup2,
    push4 ⟨4294967295⟩,
    and,
    push1 ⟨224⟩,
    shl,
    dup2,
    raw mstore 0 (flopCageCalldataMem mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    add,
    push1 ⟨0⟩,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Cage (by decide) (by evm_ov),
    dup1,
    dup4,
    sub,
    dup2,
    push1 ⟨0⟩,
    dup8,
    dup1]
  have hpc2948 :
      (⟨2887⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ =
        ⟨2948⟩ := by
    native_decide
  rw [hpc2948] at rd2948
  have htargetDouble :
      UInt256.land solcAddrMask
          (UInt256.land solcAddrMask (vowSlotWord ⟨3⟩ acc.2 ee)) =
        target := by
    simp [target, u256_land_comm, solcAddrMask_idem_left_left]
  exact ⟨_, _, by
    rw [← htargetDouble]
    simpa [flopCageSelectorWord, flopCageSelectorShifted, flopCageCalldataMem,
      flopCageOutPtr, flopCageInSize, flopCageOutSize, flopCageEndPtr,
      vowSlotWord, solcSlotWord, solcAddrMask, u256_land_comm, u256_div_one,
      show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ from by native_decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show UInt256.sub (⟨132⟩ : UInt256) ⟨128⟩ = ⟨4⟩ from by native_decide,
      show UInt256.sub ((⟨4⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨4⟩
        from by native_decide,
      show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by native_decide] using rd2948⟩

theorem RD.vowCageFlopperCageNoCode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2881⟩
      (ret :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord acc.2
        (vowAddressReturnWord ⟨3⟩ acc.2 ee) = ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  let target := vowAddressReturnWord ⟨3⟩ acc.2 ee
  obtain ⟨_, _, rd2948⟩ := RD.vowCageFlopperCageExtcodesizeGuard
    rd hmem hread64 hov
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨2948⟩) (okPc := ⟨2960⟩)
    (by simpa [target] using rd2948)
    (by simpa [target] using hcodeSize)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp; omega)

theorem RD.vowCageFlopperCageCallSetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2881⟩
      (ret :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord acc.2
        (vowAddressReturnWord ⟨3⟩ acc.2 ee) ≠ ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    let target := vowAddressReturnWord ⟨3⟩ acc.2 ee
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨2963⟩
      (gasWord :: target :: flopCageOutSize :: flopCageOutPtr :: flopCageInSize ::
        flopCageOutPtr :: flopCageOutSize :: flopCageEndPtr :: flopCageSelectorWord ::
        target :: ret :: R)
      (flopCageCalldataMem mem) (UInt256.ofNat 6) rdata acc k' C' := by
  intro target
  obtain ⟨_, _, rd2948⟩ := RD.vowCageFlopperCageExtcodesizeGuard
    rd hmem hread64 hov
  obtain ⟨gasWord, k', C', rd2963⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2948⟩) (okPc := ⟨2960⟩)
      (by simpa [target] using rd2948)
      (by simpa [target] using hcodeSize)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp; omega)
  exact ⟨gasWord, k', C', by simpa [target] using rd2963⟩

theorem RD.vowCageFlopperCageCall
    {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {cA_call : Batteries.RBSet AccountAddress compare}
    {mem rdata : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2881⟩
      (ret :: R) mem (UInt256.ofNat 6) rdata (cA_call, σCall) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σCall
        (vowAddressReturnWord ⟨3⟩ σCall I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true)
    (hov : R.length + 15 ≤ 1024) :
    let target := vowAddressReturnWord ⟨3⟩ σCall I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2964⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flopCageEndPtr :: flopCageSelectorWord ::
          target :: ret :: R)
        (flopCageCalldataMem mem) (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σCall
          createdAccounts := cA_call }
        (EVM.address (AccountAddress.ofNat target.toNat)) "cage" 0 []
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'
              substate := A'
              createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  intro target
  obtain ⟨gasWord, _, _, rd2963⟩ := RD.vowCageFlopperCageCallSetup
    rd hmem hread64 hcodeSize hov
  obtain ⟨cA', σ', z, out, A_in, callGas, k2964, C2964, hΘpack, rd2964raw,
      houtsz⟩ :=
    RD.call (by simpa [flopCageOutSize] using rd2963)
      (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmCall := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σCall
    createdAccounts := cA_call }
  refine ⟨cA', σ', z, out, A', k2964, C2964, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          flopCageOutPtr.toNat flopCageInSize.toNat)
          flopCageOutPtr.toNat flopCageOutSize.toNat) = UInt256.ofNat 6 := by
      unfold flopCageOutPtr flopCageInSize flopCageOutSize
      native_decide
    have hmin : (min flopCageOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold flopCageOutSize
      rfl
    have rd2964 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2964⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flopCageEndPtr :: flopCageSelectorWord ::
          target :: ret :: R)
        (out.write 0 (flopCageCalldataMem mem) flopCageOutPtr.toNat
          (min flopCageOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k2964 C2964 :=
      haw ▸ by simpa [target] using rd2964raw
    rw [hmin, byteArray_write_len_zero] at rd2964
    exact rd2964
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target)
      (mem := flopCageCalldataMem mem)
      (inOff := flopCageOutPtr) (inSize := flopCageInSize)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmCall, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      (by simpa [target] using cageFlopperAddress_eq_target σCall I)
      (flopCageEncode_eq hmem) ?_
    simpa [evmCall, initState, hperm] using hΘ

theorem RD.vowCageFlopperCageCallFailure {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2964⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨2964⟩) (okPc := ⟨2980⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowCageFlopperCageCallSuccessCleanup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2964⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2983⟩ (d1 :: d2 :: R) mem aw o acc k' C' := by
  obtain ⟨_, _, rd2982⟩ := RD.uniswapCallSuccessGuardOk
    (pc := ⟨2964⟩) (okPc := ⟨2980⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)
  have rd2983 := RD.pop rd2982 (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd2983⟩

theorem vowCageAuthRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I ≠ ⟨1⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  let locals : Store := ∅
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
    intro hsolm
    exact hauthEvm (by rw [hcallerWord, hsolm])
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody : ExecTransitionBody config contract evm0 locals cageTransition.body .reverted := by
    have hguard := vowAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (locals := locals)
      (by simp [locals]) hauthSolm
    have hblock := nonpayableSecondRequireReverts
      (cfg := config) (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := cageAfterAuth)
      (by simp [evm0, initState]; exact hwv)
      hguard
    simpa [ExecTransitionBody, cageTransition, cageAfterAuth, nonpayable, auth, evm0] using
      ExecFuncBody.execBlockRevert hblock
  have hreach :=
    vowReachCageBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hsize hsel
  obtain ⟨_, _, hbodyEntry⟩ := hreach
  obtain ⟨_, _, hentry⟩ := RD.solcNoArgsExternalEntry
    (code := vowBytecode) (pc := ⟨563⟩) (ret := ⟨412⟩) (routine := ⟨2488⟩)
    hbodyEntry
    (by
      unfold solcNoArgsExternalEntryWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  have hrev := RD.vowAuthCheckRevert
    (code := vowBytecode) (pc := ⟨2488⟩) (okPc := ⟨2577⟩)
    (key := ⟨412⟩) (ret := vowSelWord I) (R := [])
    (by simpa using hentry)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf vowAuthTailPc vowNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)
  exact hrev.reEquivExecutionRevert hcode (vowDispatch_cage hsel) (vowDecode_cage hsz) hbody

theorem vowCageLiveRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hliveEvm : vowSlotWord ⟨12⟩ σ_evm I ≠ ⟨1⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  let locals : Store := ∅
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hliveWord : vowSlotWord ⟨12⟩ σ_evm I = vowSlotWord ⟨12⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hliveSolm : vowSlotWord ⟨12⟩ σ_solm I ≠ ⟨1⟩ := by
    intro hsolm
    exact hliveEvm (by rw [hliveWord, hsolm])
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody : ExecTransitionBody config contract evm0 locals cageTransition.body .reverted := by
    have hguardAuth := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (locals := locals)
      (by simp [locals]) hauthSolm
    have hguardLive := vowLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (locals := locals)
      (by simp [locals]) hliveSolm
    have hblock :
        ExecBlock config { contract := contract, locals := locals } evm0
          (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
            .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
            .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
            cageAfterLive)
          .reverted := by
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
      refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
      exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
    simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
      evm0] using ExecFuncBody.execBlockRevert hblock
  have hreach :=
    vowReachCageBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hsize hsel
  obtain ⟨_, _, hbodyEntry⟩ := hreach
  obtain ⟨_, _, hentry⟩ := RD.solcNoArgsExternalEntry
    (code := vowBytecode) (pc := ⟨563⟩) (ret := ⟨412⟩) (routine := ⟨2488⟩)
    hbodyEntry
    (by
      unfold solcNoArgsExternalEntryWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
    (code := vowBytecode) (pc := ⟨2488⟩) (okPc := ⟨2577⟩)
    (key := ⟨412⟩) (ret := vowSelWord I) (R := [])
    (by simpa using hentry)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨12⟩ ≠ ⟨1⟩ := by
    simpa [vowSlotWord] using hliveEvm
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have hrev := RD.vowLiveGuardRevert
    (code := vowBytecode) (pc := ⟨2577⟩) (okPc := ⟨2647⟩)
    (key := ⟨412⟩) (ret := vowSelWord I) (R := [])
    hafterAuth
    (by
      unfold vowLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf vowLiveGuardTailPc vowNotLiveRawWord
      repeat' first | apply And.intro | native_decide)
    hliveSolc hmemAuth hread64 (by simp)
  exact hrev.reEquivExecutionRevert hcode (vowDispatch_cage hsel) (vowDecode_cage hsz) hbody

end Benchmarks.Dss.Vow

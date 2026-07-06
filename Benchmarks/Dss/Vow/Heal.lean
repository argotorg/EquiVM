import Benchmarks.Dss.Vow.Kiss

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `heal(uint256)` -/

abbrev healRad (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev healLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "rad" (.int (Int.ofNat (healRad I).toNat))

abbrev healLocalsVatDai (I : ExecutionEnv) (vatDai : UInt256) : Store :=
  (healLocals I).insert "vatDai" (.int (Int.ofNat vatDai.toNat))

theorem healLocals_get_rad (I : ExecutionEnv) :
    (healLocals I).get? "rad" = some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocals, store_get_self]

theorem healLocalsVatDai_get_rad (I : ExecutionEnv) (vatDai : UInt256) :
    (healLocalsVatDai I vatDai).get? "rad" =
      some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocalsVatDai, store_get_ne _ _ (by decide), healLocals_get_rad]

theorem healLocalsVatDai_get_vatDai (I : ExecutionEnv) (vatDai : UInt256) :
    (healLocalsVatDai I vatDai).get? "vatDai" =
      some (.int (Int.ofNat vatDai.toNat)) := by
  rw [healLocalsVatDai, store_get_self]

abbrev healSinSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨2016186517⟩ ⟨225⟩

abbrev healSinSelector : UInt256 :=
  ⟨4032373034⟩

abbrev healSinOutPtr : UInt256 :=
  ⟨128⟩

abbrev healSinInSize : UInt256 :=
  UInt256.add (UInt256.sub healSinOutPtr healSinOutPtr) ⟨36⟩

abbrev healSinEndPtr : UInt256 :=
  UInt256.add healSinOutPtr ⟨36⟩

noncomputable def healSinSelectorMem (mem : ByteArray) : ByteArray :=
  healSinSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def healSinCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 (healSinSelectorMem mem) 132 32

theorem healSinSelectorMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (healSinSelectorMem mem).size = 164 := by
  unfold healSinSelectorMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem healSinSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (healSinSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold healSinSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega), hread64]

theorem healSinCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (healSinCalldataMem I mem).size = 164 := by
  unfold healSinCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [healSinSelectorMem_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, healSinSelectorMem_size hmem, toByteArray_size]
  omega

theorem healSinCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (healSinCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold healSinCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [healSinSelectorMem_size hmem]; omega) (by omega),
    healSinSelectorMem_read64 hmem hread64]

theorem healSinSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 164) :
    (healSinSelectorMem mem).extract 128 132 = vatSinSelector := by
  unfold healSinSelectorMem
  rw [write32_eq _ _ 128 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  have hAsz : (mem.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, hmem]
    omega
  have hBsz : (healSinSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hABsz :
      (mem.extract 0 128 ++ healSinSelectorShifted.toByteArray.extract 0 32).size = 160 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  rw [extract_append_left _ _ 128 132 (by rw [hABsz]; omega),
    extract_append_right_window _ _ 128 132 (by rw [hAsz]),
    hAsz, show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    extract_extract_BA,
    show 0 + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega,
    toByteArray_eq_toBytesBE]
  native_decide

theorem healSinCalldataMem_read128_36 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (healSinCalldataMem I mem).readWithPadding 128 36 =
      vatSinSelector ++ (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [healSinCalldataMem_size I hmem]), healSinCalldataMem,
    write32_eq _ (healSinSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [healSinSelectorMem_size hmem]; omega)]
  have hAsz : ((healSinSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, healSinSelectorMem_size hmem]
    omega
  have hBsz : (((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((healSinSelectorMem mem).extract 0 132 ++
        ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32 =
        (UInt256.ofNat I.codeOwner.val).toByteArray := by
    have h := @ByteArray.extract_zero_size (UInt256.ofNat I.codeOwner.val).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), healSinSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem healSinInSize_eq : healSinInSize = ⟨36⟩ := by
  unfold healSinInSize healSinOutPtr
  native_decide

theorem healSinEndPtr_eq : healSinEndPtr = ⟨164⟩ := by
  unfold healSinEndPtr healSinOutPtr
  native_decide

theorem healSinEncode_eq (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "sin" [.address I.codeOwner] =
      some ((healSinCalldataMem I mem).readWithPadding
        healSinOutPtr.toNat healSinInSize.toNat) := by
  rw [healSinInSize_eq]
  change config.externalABI.encode? "sin" [.address I.codeOwner] =
    some ((healSinCalldataMem I mem).readWithPadding 128 36)
  rw [healSinCalldataMem_read128_36 I hmem]
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    vatSinSelector, selectorBytes]
  rw [show EVM.word (↑I.codeOwner : ℕ) = UInt256.ofNat (↑I.codeOwner : ℕ) from rfl]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]

theorem vowDispatch_heal {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩) :
    dispatchMsg contract I.calldata = some healTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition])
    (post := [humpTransition, kissTransition, liveTransition, relyTransition, sinTransition,
      sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := healTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, healSelectorBytes]
    exact hsel

theorem vowDecode_heal_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
      (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I) := by
  simpa [config, healTransition, healLocals, healRad, uint256] using
    (decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "rad") hsz36)

theorem vowDecode_heal_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
      (transitionSignature healTransition).paramTypes I.calldata = none := by
  simpa [config, healTransition, uint256] using
    (decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "rad") hsz4 hshort)

theorem vowReachHealBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨818⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨4084909596⟩ :=
    vowSelWord_eq_of_beq I hsz 0xf3 0x7a 0xc6 0x1c ⟨4084909596⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc 5))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighHighBody 5 (by omega) ⟨818⟩ hcode hwv hsz hsize hroot hhigh heq0
    htake (by jump_dest) (by native_decide)

theorem vowHealShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachHealBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨818⟩) (ret := ⟨412⟩)
    (decoded := ⟨840⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_heal hsel)
    (vowDecode_heal_none_short hsz4 hshort)

theorem RD.vowHealDecodeToDaiRoutine
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4640⟩
      [healRad I, ⟨412⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  let rad := healRad I
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨818⟩) (ret := ⟨412⟩)
    (decoded := ⟨840⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  have rd841 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd842 := rd841.pop (by native_decide) (by evm_ov)
  have rd843 := rd842.calldataload (by native_decide) (by evm_ov)
  have rd846 := rd843.push2 ⟨4640⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [rad, healRad, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd846.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.vowHealToDaiExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4703⟩
      (kissDaiTargetWord σ I :: kissDaiTargetWord σ I :: kissDaiOutPtr I ::
        kissDaiInSize I :: kissDaiOutPtr I :: ⟨32⟩ :: kissDaiEndPtr I ::
        ⟨1814410054⟩ :: kissDaiTargetWord σ I :: healRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  let target := kissDaiTargetWord σ I
  obtain ⟨_, _, rd4640⟩ := RD.vowHealDecodeToDaiRoutine hreach hsz36 hsize
  have rd4641 := rd4640.jumpdest (by native_decide) (by evm_ov)
  have rd4643 := rd4641.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4644⟩ := rd4643.sload (by native_decide) (by evm_ov)
  obtain ⟨k4703, C4703, rd4703⟩ : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4703⟩
      (target :: target :: kissDaiOutPtr I :: kissDaiInSize I ::
        kissDaiOutPtr I :: ⟨32⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        target :: healRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    have rdRaw := evm_run rd4644 with [
      push1 ⟨64⟩,
      dup1,
      raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
        mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
      push4 ⟨907205027⟩,
      push1 ⟨225⟩,
      shl,
      dup2,
      raw mstore 6 kissDaiSelectorMem (UInt256.ofNat 5) (by native_decide)
        mem_cost (by rfl) (by decide) (by evm_ov),
      uniswapAddress,
      push1 ⟨4⟩,
      dup3,
      add,
      raw mstore 3 (kissDaiCalldataMem I) (UInt256.ofNat 6) (by native_decide)
        mem_cost (by rfl) (by decide) (by evm_ov),
      swap1,
      raw mload 0 (kissDaiOutPtr I) (UInt256.ofNat 6) (by native_decide)
        mem_cost (by rfl) (by decide) (by evm_ov),
      push1 ⟨1⟩,
      push1 ⟨1⟩,
      push1 ⟨160⟩,
      shl,
      sub,
      swap1,
      swap3,
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
    exact ⟨_, _, by
      simpa [target, kissDaiTargetWord, kissDaiSelectorShifted, kissDaiSelectorMem,
        kissDaiCalldataMem, kissDaiOutPtr, kissDaiInSize, kissDaiEndPtr, vowSlotWord,
        solcSlotWord, solcAddrMask] using rdRaw⟩
  exact ⟨k4703, C4703, by simpa [target] using rd4703⟩

theorem RD.vowHealDaiNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let target := kissDaiTargetWord σ I
  obtain ⟨_, _, rd4703⟩ := RD.vowHealToDaiExtcodesizeGuard hreach hsz36 hsize
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨4703⟩) (okPc := ⟨4715⟩) rd4703
    (by simpa [target] using hcodeSize)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowHealToDaiStaticcall
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4718⟩
      (gasWord :: kissDaiTargetWord σ I :: kissDaiOutPtr I :: kissDaiInSize I ::
        kissDaiOutPtr I :: ⟨32⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ I :: healRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  let target := kissDaiTargetWord σ I
  obtain ⟨_, _, rd4703⟩ := RD.vowHealToDaiExtcodesizeGuard hreach hsz36 hsize
  obtain ⟨gasWord, k, C, rd4718⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4703⟩) (okPc := ⟨4715⟩) rd4703
      (by simpa [target] using hcodeSize)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k, C, by simpa [target] using rd4718⟩

theorem RD.vowHealDaiPostCall
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
          kissDaiTargetWord σ I :: healRad I :: ⟨412⟩ :: sel :: [])
        (o.write 0 (kissDaiCalldataMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k C
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) false
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4718⟩ :=
    RD.vowHealToDaiStaticcall hreach hsz36 hsize hcodeSize
  obtain ⟨cA', σ', z, o, A_in, callGas, k4719, C4719, hΘpack, rd4719raw, hosz⟩ :=
    RD.uniswapStaticcall rd4718 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k4719, C4719, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (kissDaiOutPtr I).toNat (kissDaiInSize I).toNat)
          (kissDaiOutPtr I).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      rw [kissDaiOutPtr_eq, kissDaiInSize_eq]
      native_decide
    have hoff : (kissDaiOutPtr I).toNat = 128 := by
      rw [kissDaiOutPtr_eq]
      native_decide
    have rd4719 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
          kissDaiTargetWord σ I :: healRad I :: ⟨412⟩ :: sel :: [])
        (o.write 0 (kissDaiCalldataMem I) (kissDaiOutPtr I).toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k4719 C4719 :=
      haw ▸ rd4719raw
    rw [hoff] at rd4719
    exact rd4719
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σ I)
      (mem := kissDaiCalldataMem I) (inOff := kissDaiOutPtr I)
      (inSize := kissDaiInSize I)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget σ I) (kissDaiEncode_eq I) ?_
    simpa [initState] using hΘ

theorem RD.vowHealDaiCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
      (⟨0⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ I :: healRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, _, rd4718⟩ :=
    RD.vowHealToDaiStaticcall hreach hsz36 hsize hcodeSize
  obtain ⟨k4719, C4719, rd4719raw⟩ :=
    RD.uniswapStaticcallDepthLimit rd4718 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (kissDaiOutPtr I).toNat (kissDaiInSize I).toNat)
        (kissDaiOutPtr I).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    rw [kissDaiOutPtr_eq, kissDaiInSize_eq]
    native_decide
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd4719 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
      (⟨0⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ I :: healRad I :: ⟨412⟩ :: sel :: [])
      (ByteArray.empty.write 0 (kissDaiCalldataMem I) (kissDaiOutPtr I).toNat
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k4719 C4719 :=
    haw ▸ rd4719raw
  rw [hmin, byteArray_write_len_zero] at rd4719
  exact ⟨k4719, C4719, rd4719⟩

theorem RD.vowHealDaiCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨4719⟩) (okPc := ⟨4735⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowHealDaiCallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4737⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨4719⟩) (okPc := ⟨4735⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowHealDaiReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4737⟩
      (d0 :: d1 :: d2 :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨4737⟩) (okPc := ⟨4757⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowHealDaiReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4737⟩
      (d0 :: d1 :: d2 :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
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
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4760⟩
      (retWord :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨4737⟩) (okPc := ⟨4757⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.vowHealInsufficientSurplus
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4760⟩
      (vatDai :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hinsuff : vatDai.toNat < (healRad I).toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd4761 := rd.dup2 (by native_decide) (by evm_ov)
  have rd4762₀ := rd4761.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (healRad I) vatDai = ⟨1⟩ :=
    ugt_one hinsuff
  have rd4762 := rd4762₀
  rw [hgt] at rd4762
  have rd4763₀ := rd4762.iszero (by native_decide) (by evm_ov)
  have rd4763 := rd4763₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4763
  have rd4766 := rd4763.push2 ⟨4838⟩ (by native_decide) (by evm_ov)
  have rd4767 := rd4766.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd4771 := evm_run rd4767 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd4775 := rd4771.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd4794 := evm_run rd4775 with [
    push1 ⟨229⟩,
    shl,
    dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨24⟩,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (solcErrorStringMem2 (⟨24⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4819 := rd4794.pushConst vowInsufficientSurplusRawWord
    (width := 24) (op := .PUSH24) (by decide) (by native_decide) (by evm_ov)
  have rd4822₀ := evm_run rd4819 with [
    push1 ⟨64⟩,
    shl]
  have rd4822 := rd4822₀
  rw [show UInt256.shiftLeft vowInsufficientSurplusRawWord ⟨64⟩ =
      vowInsufficientSurplusStringWord from rfl] at rd4822
  exact evm_run rd4822 with [
    push1 ⟨68⟩,
    dup3,
    add,
    raw mstore 3
      (solcErrorStringMem3 (⟨24⟩ : UInt256) vowInsufficientSurplusStringWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨24⟩ : UInt256)
        vowInsufficientSurplusStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1,
    dup2,
    swap1,
    sub,
    push1 ⟨100⟩,
    add,
    swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.vowHealDaiEnough
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4760⟩
      (vatDai :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : (healRad I).toNat ≤ vatDai.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4838⟩
      [healRad I, ⟨412⟩, sel]
      mem (UInt256.ofNat 6) o acc k' C' := by
  have rd4761 := rd.dup2 (by native_decide) (by evm_ov)
  have rd4762₀ := rd4761.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (healRad I) vatDai = ⟨0⟩ :=
    ugt_zero henough
  have rd4762 := rd4762₀
  rw [hgt] at rd4762
  have rd4763₀ := rd4762.iszero (by native_decide) (by evm_ov)
  have rd4763 := rd4763₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4763
  have rd4766 := rd4763.push2 ⟨4838⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4766.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowHealToSinExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4838⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4909⟩
      (kissDaiTargetWord σ' I :: kissDaiTargetWord σ' I :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ' I :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      (healSinCalldataMem I mem) (UInt256.ofNat 6) o (cA', σ') k' C' := by
  let target := kissDaiTargetWord σ' I
  let rawTarget := vowSlotWord ⟨1⟩ σ' I
  have rd4839 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd4841 := rd4839.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4842, C4842, rd4842₀⟩ := rd4841.sload (by native_decide) (by evm_ov)
  have rd4842 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4842⟩
      (rawTarget :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (cA', σ') k4842 C4842 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd4842₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hSinMem : (healSinCalldataMem I mem).size = 164 :=
    healSinCalldataMem_size I hmem
  have hSinRead64 :
      (healSinCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    healSinCalldataMem_read64 I hmem hread64
  have hmload64Sin :
      (if (⟨64⟩ : UInt256).toNat ≥ (healSinCalldataMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((healSinCalldataMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSinMem]; decide) (by decide) hSinRead64
  have rd4909 := evm_run rd4842 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨2016186517⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 0 (healSinSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    uniswapAddress,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (healSinCalldataMem I mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Sin (by decide) (by evm_ov),
    push2 ⟨4921⟩,
    swap3,
    push2 ⟨1325⟩,
    swap3,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap2,
    and,
    swap2,
    push4 healSinSelector,
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
  exact ⟨_, _, by
    simpa [target, rawTarget, kissDaiTargetWord, healSinSelectorShifted, healSinSelector,
      healSinSelectorMem, healSinCalldataMem, healSinOutPtr, healSinInSize, healSinEndPtr,
      vowSlotWord, solcSlotWord, solcAddrMask] using rd4909⟩

theorem RD.vowHealSinNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4838⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (kissDaiTargetWord σ' I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd4909⟩ := RD.vowHealToSinExtcodesizeGuard rd hmem hread64
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨4909⟩) (okPc := ⟨1273⟩) rd4909
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowHealToSinStaticcall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4838⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (kissDaiTargetWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1276⟩
      (gasWord :: kissDaiTargetWord σ' I :: healSinOutPtr :: healSinInSize ::
        healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ' I :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      (healSinCalldataMem I mem) (UInt256.ofNat 6) o (cA', σ') k' C' := by
  obtain ⟨_, _, rd4909⟩ := RD.vowHealToSinExtcodesizeGuard rd hmem hread64
  obtain ⟨gasWord, k1276, C1276, rd1276⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4909⟩) (okPc := ⟨1273⟩) rd4909
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k1276, C1276, by simpa using rd1276⟩

theorem RD.vowHealSinPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4838⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (kissDaiTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (out : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord σ' I :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
        (out.write 0 (healSinCalldataMem I mem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (EVM.address (kissVatAddress σ' I)) "sin" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, out) false
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1276⟩ :=
    RD.vowHealToSinStaticcall rd hmem hread64 hcodeSize
  obtain ⟨cA'', σ'', z, out, A_in, callGas, k1277, C1277, hΘpack, rd1277raw, houtsz⟩ :=
    RD.uniswapStaticcall rd1276 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A'', hΘ⟩ := hΘpack
  refine ⟨cA'', σ'', z, out, A'', k1277, C1277, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          healSinOutPtr.toNat healSinInSize.toNat)
          healSinOutPtr.toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      rw [healSinInSize_eq]
      unfold healSinOutPtr
      native_decide
    have hoff : healSinOutPtr.toNat = 128 := by
      unfold healSinOutPtr
      native_decide
    have rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord σ' I :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
        (out.write 0 (healSinCalldataMem I mem) healSinOutPtr.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA'', σ'') k1277 C1277 :=
      haw ▸ rd1277raw
    rw [hoff] at rd1277
    exact rd1277
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σ' I)
      (mem := healSinCalldataMem I mem) (inOff := healSinOutPtr)
      (inSize := healSinInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget σ' I) (healSinEncode_eq I hmem) ?_
    simpa [initState] using hΘ

theorem RD.vowHealSinCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨1277⟩) (okPc := ⟨1293⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem vowHealSourceDaiNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvat (by simpa [evm0] using hvatNoCode)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceDaiDecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, out) false)
    (hdecDai : config.externalABI.decode? "dai" out = none) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargs hcallDai hdecDai
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceDaiCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (false, evmDai, out) false) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallDai
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceInsufficientSurplus
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {out : ByteArray}
    {vatDai : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, out) false)
    (hdecDai :
      config.externalABI.decode? "dai" out =
        some [.int (Int.ofNat vatDai.toNat)])
    (hinsuff : vatDai.toNat < (healRad I).toNat) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := healLocalsVatDai I vatDai } evmDai) := by
    simpa [locals, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := healLocalsVatDai I vatDai } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
      (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := healLocalsVatDai I vatDai } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
      (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := healLocalsVatDai I vatDai } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool false) :=
    evalExpr_le_uint256_false hradDai hvatDai hinsuff
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqSurplus)
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceSinNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {outDai : ByteArray}
    {vatDai : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatNoCodeSin :
      (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat =
          0) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvatSin hvatNoCodeSin
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardSin)
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceSinCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin : EVM.State}
    {outDai outSin : ByteArray} {vatDai : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (false, evmSin, outSin) false) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvatSin (by simp [evalExpr?, pure]) hargsSin hcallSin
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    exact ExecBlock.consRevert hcallSinStmt
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealDaiNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hnoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hVat :
      vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hTarget : kissDaiTargetWord σ_evm I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hVat]
  have hnoCodeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
        (kissDaiTargetWord σ_evm I)
    have hsolmTargetEvm :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (kissDaiTargetWord σ_evm I) = ⟨0⟩ := by
      rw [← hsame]
      exact hnoCode
    simpa [hTarget] using hsolmTargetEvm
  have hvatAddr :
      kissVatAddress σ_solm I = AccountAddress.ofUInt256 (kissDaiTargetWord σ_solm I) := by
    apply Fin.ext
    simp [kissVatAddress, kissDaiTargetWord, vowAddressReturnWord,
      accountAddress_ofUInt256_eq_ofNat_toNat]
  have hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
    rw [hvatAddr]
    unfold Reasoning.Theory.uniswapExtCodeSizeWord at hnoCodeSolm
    cases hacc :
      σ_solm.find? (AccountAddress.ofUInt256 (kissDaiTargetWord σ_solm I)) with
    | none =>
        simpa [initState, State.lookupAccount, hacc] using
          (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
    | some acc =>
        have hword := congrArg UInt256.toNat hnoCodeSolm
        simpa [initState, State.lookupAccount, hacc] using hword
  have hbody := vowHealSourceDaiNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hvatNoCode
  have hrev := RD.vowHealDaiNoCode hreach hsz36 hsize hnoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealDaiCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {o mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd4719 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
      (⟨0⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ_evm I :: healRad I :: ⟨412⟩ :: sel :: [])
      mem aw o (cA', σ'_evm) k C)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          o) false)
    (hosz : o.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealDaiCallFailure rd4719 hosz (by simp)
  have hVatAddr : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    have hVat :
        vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissVatAddress, vowAddressReturnWord, hVat]
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDai)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (false,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) false := by
    simpa [hVatAddr] using hcallSolmRaw
  have hbody := vowHealSourceDaiCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
    (out := o) hwv hvatCodeSolm hcallSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealDaiDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {o mem : ByteArray} {k C : ℕ}
    {d0 d1 d2 : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd4737 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4737⟩
      (d0 :: d1 :: d2 :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (cA', σ'_evm) k C)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          o) false)
    (hshort : o.size < 32)
    (hosz : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealDaiReturnDecodeShortReverts rd4737 hshort hosz hMload64Value
  have hVatAddr : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    have hVat :
        vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissVatAddress, vowAddressReturnWord, hVat]
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDai)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) false := by
    simpa [hVatAddr] using hcallSolmRaw
  have hbody := vowHealSourceDaiDecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
    (out := o) hwv hvatCodeSolm hcallSolm (kissDaiDecode_none_short hshort)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealDaiSuccessInsufficientSurplusBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {o : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd4719 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
      (⟨1⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ_evm I :: healRad I :: ⟨412⟩ :: sel :: [])
      (o.write 0 (kissDaiCalldataMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
      (UInt256.ofNat 6) o (cA', σ'_evm) k C)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          o) false)
    (hosz : o.size < UInt256.size)
    (ho32 : 32 ≤ o.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hinsuff :
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat < (healRad I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let vatDai : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd4719' := rd4719
  rw [hmin] at rd4719'
  obtain ⟨_, _, rd4737⟩ :=
    RD.vowHealDaiCallSuccessToDecode rd4719' (by simp)
  have hmem : (o.write 0 (kissDaiCalldataMem I) 128 32).size = 164 :=
    kissDaiWrite_size I o 32 (by omega) ho32
  have hread64 :
      (o.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    kissDaiWrite_read64 I o 32 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (o.write 0 (kissDaiCalldataMem I) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((o.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (o.write 0 (kissDaiCalldataMem I) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((o.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        vatDai := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥ (o.write 0 (kissDaiCalldataMem I) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmem]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      kissDaiWrite_read128_32 I o ho32]
  obtain ⟨_, _, rd4760⟩ :=
    RD.vowHealDaiReturnDecodeOk (retWord := vatDai) rd4737 ho32 hosz hmload64 hmload128
  have hrev := RD.vowHealInsufficientSurplus rd4760
    (by simpa [vatDai] using hinsuff) hmem hread64
  have hVatAddr : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    have hVat :
        vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissVatAddress, vowAddressReturnWord, hVat]
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDai)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) false := by
    simpa [hVatAddr] using hcallSolmRaw
  have hdecDai :
      config.externalABI.decode? "dai" o = some [.int (Int.ofNat vatDai.toNat)] := by
    simpa [vatDai] using kissDaiDecode_ok (o := o) ho32
  have hbody := vowHealSourceInsufficientSurplus (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
    (out := o) (vatDai := vatDai) hwv hvatCodeSolm hcallSolm hdecDai
    (by simpa [vatDai] using hinsuff)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealSinNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatDai : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {evmDai : EVM.State} {mem outDai : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd4838 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4838⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) outDai
      (cA', σ'_evm) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeEvm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'_evm (kissDaiTargetWord σ'_evm I) =
        ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatNoCodeSin :
      (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealSinNoCode rd4838 hmem hread64 hcodeSizeEvm
  have hbody := vowHealSourceSinNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (outDai := outDai) (vatDai := vatDai)
    hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai hvatNoCodeSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealSinCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin : EVM.State} {mem outDai outSin rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (false, evmSin, outSin) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealSinCallFailure rd1277 hrdataSize (by simp)
  have hbody := vowHealSourceSinCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (outDai := outDai) (outSin := outSin)
    (vatDai := vatDai) hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai
    hvatCodeSin hcallSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow

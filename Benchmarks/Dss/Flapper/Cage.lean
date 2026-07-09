import Benchmarks.Dss.Flapper.Deny
import Benchmarks.Dss.Flopper.Dent.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

/-! ## `cage(uint256)` -/

abbrev cageRadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev cageRadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (cageRadWord I).toNat)

abbrev cageLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "rad" (cageRadValue I)

def cageLivePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩ ⟨0⟩

def cageLivePostAccountMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨7⟩ ⟨0⟩

abbrev cageVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperAddressReturnWord ⟨2⟩ σ I

abbrev cageMoveLocals (I : ExecutionEnv) : Store :=
  (cageLocals I).insert "_moveRet" (collapseReturns [])

abbrev cageThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

abbrev cageSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev cageMoveSelectorWord : UInt256 :=
  Benchmarks.Dss.Flopper.dentMoveSelectorWord

abbrev cageMoveOutPtr : UInt256 :=
  Benchmarks.Dss.Flopper.dentMoveOutPtr

abbrev cageMoveInSize : UInt256 :=
  Benchmarks.Dss.Flopper.dentMoveInSize

abbrev cageMoveOutSize : UInt256 :=
  Benchmarks.Dss.Flopper.dentMoveOutSize

abbrev cageMoveEndPtr : UInt256 :=
  Benchmarks.Dss.Flopper.dentMoveEndPtr

noncomputable abbrev cageMoveCalldataMem (src guy rad : UInt256) (mem : ByteArray) : ByteArray :=
  Benchmarks.Dss.Flopper.dentMoveCalldataMem src guy rad mem

theorem cageMoveEncode_eq (src guy rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hsrcCanon : src.toNat < EVM.addressModulus)
    (hguyCanon : guy.toNat < EVM.addressModulus) :
    config.externalABI.encode? "move"
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat rad.toNat)] =
      some ((cageMoveCalldataMem src guy rad mem).readWithPadding
        cageMoveOutPtr.toNat cageMoveInSize.toNat) := by
  simpa [config, externalABI, Benchmarks.Dss.Flopper.config,
    Benchmarks.Dss.Flopper.externalABI, moveSelector, Benchmarks.Dss.Flopper.moveSelector,
    cageMoveCalldataMem, cageMoveOutPtr, cageMoveInSize] using
    Benchmarks.Dss.Flopper.dentMoveEncode_eq src guy rad hmem hsrcCanon hguyCanon

/-- Legacy solc-0.5 single-`uint256` calldata decode, local to `cage`. -/
theorem cageDecodeCalldata_legacyUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem cageDecodeCalldata_legacyUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flapperDecode_cage_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some (cageLocals I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["rad"] [uint256] I.calldata =
    some (cageLocals I)
  simpa [config, cageLocals, cageRadValue, cageRadWord, uint256] using
    cageDecodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "rad") hsz36

theorem flapperDecode_cage_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["rad"] [uint256] I.calldata = none
  simpa [config, uint256] using
    cageDecodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "rad") hsz4 hshort

theorem cageLocals_get_wards (I : ExecutionEnv) :
    (cageLocals I).get? "wards" = none := by
  rw [cageLocals, store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem cageLocals_get_rad (I : ExecutionEnv) :
    (cageLocals I).get? "rad" = some (cageRadValue I) := by
  simp [cageLocals]

theorem cageAssignLive (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := cageLocals I } evm
      .storage liveRef (.int 0) =
        .ok ({ contract := contract, locals := cageLocals I }, cageLivePostState evm) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨7⟩)
      (hbase := by simp [liveRef, cageLocals])
      (her := by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [cageLivePostState, wordLoc, uint256Loc] using storageLocStore_uint256 evm ⟨7⟩ ⟨0⟩

theorem evalExpr_cage_rad_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := cageLocals I } evm (.var "rad") =
      .ok (cageRadValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((cageLocals I).get? "rad") =
    .ok (cageRadValue I)
  rw [cageLocals_get_rad]
  rfl

theorem flapperReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 2)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨700⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0xa2f91af2⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xa2 0xf9 0x1a 0xf2 ⟨0xa2f91af2⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 2 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc 2))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨700⟩ 2 hfirst
    (fun j hj => flapperHighLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperCageX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨700⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3106⟩
      [cageRadWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flapperBytecode) (sel := sel) (entry := ⟨700⟩) (ret := ⟨360⟩)
    (decoded := ⟨722⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd723 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd724 := rd723.pop (by native_decide) (by evm_ov)
  have rd725 := rd724.calldataload (by native_decide) (by evm_ov)
  have rd728 := rd725.push2 ⟨3106⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [cageRadWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd728.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperCageX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨700⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flapperBytecode) (sel := sel) (entry := ⟨700⟩) (ret := ⟨360⟩)
    (decoded := ⟨722⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flapperCageX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨3106⟩
      [cageRadWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨3199⟩
      [cageRadWord I, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd3111pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3112 := rd3111pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3117pre := evm_run rd3112 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3118 := rd3117pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3121pre := evm_run rd3118 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3122 := rd3121pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3123, C3123, rd3123raw⟩ := rd3122.sload (by native_decide) (by evm_ov)
  have rd3123 : RD flapperBytecode I g s0 ⟨3123⟩
      (relyAuthWord σ I :: cageRadWord I :: ⟨360⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3123 C3123 := by
    simpa [relyAuthWord, flapperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd3123raw
  have rd3126pre := evm_run rd3123 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd3126pre
  have rd3129 := rd3126pre.pushConst (⟨3199⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3129.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperCageX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨3106⟩
      [cageRadWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd3111pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3112 := rd3111pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3117pre := evm_run rd3112 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3118 := rd3117pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3121pre := evm_run rd3118 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3122 := rd3121pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3123, C3123, rd3123raw⟩ := rd3122.sload (by native_decide) (by evm_ov)
  have rd3123 : RD flapperBytecode I g s0 ⟨3123⟩
      (relyAuthWord σ I :: cageRadWord I :: ⟨360⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3123 C3123 := by
    simpa [relyAuthWord, flapperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd3123raw
  have rd3126pre := evm_run rd3123 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd3126pre
  have rd3129 := rd3126pre.pushConst (⟨3199⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd3130 := rd3129.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3130⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x119b185c1c195c8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x466c61707065722f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd3130
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp)

theorem flapperCageX_storeLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD flapperBytecode I g s0 ⟨3199⟩
      [cageRadWord I, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨3207⟩
      [⟨0⟩, cageRadWord I, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, cageLivePostAccountMap I σ) k' C' := by
  have rd3206pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k3207, C3207, rd3207raw⟩ := rd3206pre.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨k3207, C3207, by
    simpa [cageLivePostAccountMap] using rd3207raw⟩

set_option maxHeartbeats 1000000 in
theorem flapperCageX_toMoveExtcodesizeGuard
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (h : RD flapperBytecode I g s0 ⟨3207⟩
      [⟨0⟩, cageRadWord I, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    let vat := cageVatWord σ I
    ∃ k' C', RD flapperBytecode I g s0 ⟨3277⟩
      (vat :: vat :: cageMoveOutSize :: cageMoveOutPtr :: cageMoveInSize ::
        cageMoveOutPtr :: cageMoveOutSize :: cageMoveEndPtr :: cageMoveSelectorWord ::
        vat :: cageRadWord I :: ⟨360⟩ :: sel :: [])
      (cageMoveCalldataMem (cageThisWord I) (cageSenderWord I) (cageRadWord I)
        (relyAuthHashMem I))
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  intro vat
  let src := cageThisWord I
  let guy := cageSenderWord I
  let rad := cageRadWord I
  let mem0 := relyAuthHashMem I
  have hmem0 : mem0.size = 96 := by
    simpa [mem0] using relyAuthHashMem_size I
  have hread64Mem0 : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0] using relyAuthHashMem_read64 I
  have hmload64Mem0 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem0.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem0.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem0]; decide) (by decide) hread64Mem0
  have hcallMem :
      (cageMoveCalldataMem src guy rad mem0).size = 228 := by
    simpa [cageMoveCalldataMem, src, guy, rad, mem0] using
      Benchmarks.Dss.Flopper.dentMoveCalldataMem_size src guy rad hmem0
  have hcallRead64 :
      (cageMoveCalldataMem src guy rad mem0).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    simpa [cageMoveCalldataMem, src, guy, rad, mem0] using
      Benchmarks.Dss.Flopper.dentMoveCalldataMem_read64 src guy rad hmem0 hread64Mem0
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (cageMoveCalldataMem src guy rad mem0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((cageMoveCalldataMem src guy rad mem0).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd3209pre := evm_run h with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3210, C3210, rd3210raw⟩ :=
    rd3209pre.sload (by native_decide) (by evm_ov)
  have rd3210 : RD flapperBytecode I g s0 ⟨3210⟩
      (flapperSlotWord ⟨2⟩ σ I :: ⟨0⟩ :: rad :: ⟨360⟩ :: sel :: [])
      mem0 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3210 C3210 := by
    simpa [mem0, rad, flapperSlotWord] using rd3210raw
  have rd3277 := evm_run rd3210 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Mem0 (by decide) (by evm_ov),
    raw push4 cageMoveSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (Benchmarks.Dss.Flopper.dentMoveSelectorMem mem0) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw uniswapAddress (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (Benchmarks.Dss.Flopper.dentMoveSrcMem src mem0) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [Benchmarks.Dss.Flopper.dentMoveSrcMem, src, cageThisWord,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (Benchmarks.Dss.Flopper.dentMoveGuyMem src guy mem0) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [Benchmarks.Dss.Flopper.dentMoveGuyMem, src, guy, cageSenderWord,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (cageMoveCalldataMem src guy rad mem0) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 cageMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 cageMoveInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc3277 :
      (⟨3210⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨3277⟩ := by
    native_decide
  rw [hpc3277] at rd3277
  exact ⟨_, _, by
    simpa [vat, src, guy, rad, mem0, cageVatWord, flapperAddressReturnWord,
      flapperSlotWord, cageMoveCalldataMem, cageMoveSelectorWord, cageMoveOutPtr,
      cageMoveOutSize, cageMoveInSize, cageMoveEndPtr,
      Benchmarks.Dss.Flopper.dentMoveSelectorMem,
      Benchmarks.Dss.Flopper.dentMoveSrcMem,
      Benchmarks.Dss.Flopper.dentMoveGuyMem,
      Benchmarks.Dss.Flopper.dentMoveCalldataMem,
      Benchmarks.Dss.Flopper.dentMoveSelectorShifted,
      Benchmarks.Dss.Flopper.dentMoveSelectorWord,
      Benchmarks.Dss.Flopper.dentMoveOutPtr,
      Benchmarks.Dss.Flopper.dentMoveOutSize,
      Benchmarks.Dss.Flopper.dentMoveInSize,
      Benchmarks.Dss.Flopper.dentMoveEndPtr,
      solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + cageMoveInSize =
        cageMoveInSize from by native_decide,
      show (⟨128⟩ : UInt256) + cageMoveInSize = cageMoveEndPtr from by native_decide,
      show cageMoveInSize + cageMoveOutPtr = cageMoveEndPtr from by native_decide]
      using rd3277⟩

theorem flapperCageX_moveNoCode
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hnoCode : Reasoning.Theory.uniswapExtCodeSizeWord σ (cageVatWord σ I) = ⟨0⟩)
    (rd3207 : RD flapperBytecode I g
      (initState cA gh bl σStart σ₀ g A I) ⟨3207⟩
      [⟨0⟩, cageRadWord I, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σStart σ₀ g A I) := by
  obtain ⟨_, _, rd3277⟩ := flapperCageX_toMoveExtcodesizeGuard rd3207
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨3277⟩) (okPc := ⟨3289⟩)
    rd3277 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flapperCageX_moveCall
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (cageVatWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd3207 : RD flapperBytecode I g
      (initState cA gh bl σStart σ₀ g A I) ⟨3207⟩
      [⟨0⟩, cageRadWord I, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    let src := cageThisWord I
    let guy := cageSenderWord I
    let rad := cageRadWord I
    let vat := cageVatWord σ I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨3293⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: cageMoveEndPtr :: cageMoveSelectorWord ::
          vat :: rad :: ⟨360⟩ :: sel :: [])
        (cageMoveCalldataMem src guy rad (relyAuthHashMem I)) (UInt256.ofNat 8)
        out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA gh bl σStart σ₀ g A I with accountMap := σ })
        (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
        [.address I.codeOwner, .address I.source, .int (Int.ofNat rad.toNat)]
        (z,
          { { initState cA gh bl σStart σ₀ g A I with accountMap := σ } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  intro src guy rad vat
  have hmem : (relyAuthHashMem I).size = 96 := relyAuthHashMem_size I
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [show src = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, cageSenderWord, solcSourceWord] using solcSourceWord_canonical I
  have hsrcAddr : AccountAddress.ofNat src.toNat = I.codeOwner := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [src, cageThisWord] using accountAddress_roundtrip I.codeOwner
  have hguyAddr : AccountAddress.ofNat guy.toNat = I.source := by
    simpa [guy, cageSenderWord, solcSourceWord] using solcSource_ofNat I
  obtain ⟨_, _, rd3277⟩ := flapperCageX_toMoveExtcodesizeGuard rd3207
  obtain ⟨gasWord, _, _, rd3292⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3277⟩) (okPc := ⟨3289⟩) rd3277
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k3293, C3293, hΘpack, rd3293raw,
      houtsz⟩ :=
    RD.call rd3292 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k3293, C3293, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          cageMoveOutPtr.toNat cageMoveInSize.toNat)
          cageMoveOutPtr.toNat cageMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold cageMoveOutPtr cageMoveInSize cageMoveOutSize
      native_decide
    have hmin : (min cageMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold cageMoveOutSize
      rfl
    have rd3293 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨3293⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: cageMoveEndPtr :: cageMoveSelectorWord ::
          vat :: rad :: ⟨360⟩ :: sel :: [])
        (out.write 0 (cageMoveCalldataMem src guy rad (relyAuthHashMem I))
          cageMoveOutPtr.toNat (min cageMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k3293 C3293 :=
      haw ▸ rd3293raw
    rw [hmin, byteArray_write_len_zero] at rd3293
    exact rd3293
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := vat)
      (mem := cageMoveCalldataMem src guy rad (relyAuthHashMem I))
      (inOff := cageMoveOutPtr) (inSize := cageMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      Benchmarks.Dss.Flopper.flopperAddressWord_address_eq_target
      ?_ ?_
    · simpa [hsrcAddr, hguyAddr] using
        cageMoveEncode_eq src guy rad hmem hsrcCanon hguyCanon
    · simpa [initState, hperm] using hΘ

theorem flapperCageX_moveCallDepthLimit
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (cageVatWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (rd3207 : RD flapperBytecode I g
      (initState cA gh bl σStart σ₀ g A I) ⟨3207⟩
      [⟨0⟩, cageRadWord I, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    let src := cageThisWord I
    let guy := cageSenderWord I
    let rad := cageRadWord I
    let vat := cageVatWord σ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨3293⟩
      (⟨0⟩ :: cageMoveEndPtr :: cageMoveSelectorWord :: vat :: rad :: ⟨360⟩ :: sel :: [])
      (cageMoveCalldataMem src guy rad (relyAuthHashMem I)) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  intro src guy rad vat
  obtain ⟨_, _, rd3277⟩ := flapperCageX_toMoveExtcodesizeGuard rd3207
  obtain ⟨gasWord, _, _, rd3292⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3277⟩) (okPc := ⟨3289⟩) rd3277
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k3293, C3293, rd3293raw⟩ :=
    RD.callDepthLimit rd3292 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k3293, C3293, ?_⟩
  have hmin : (min cageMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold cageMoveOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        cageMoveOutPtr.toNat cageMoveInSize.toNat)
        cageMoveOutPtr.toNat cageMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold cageMoveOutPtr cageMoveInSize cageMoveOutSize
    native_decide
  simpa [cageMoveOutPtr, cageMoveInSize, cageMoveOutSize, hmin,
    byteArray_write_len_zero, haw] using rd3293raw

theorem flapperCageX_moveCallFailure
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd3293 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨3293⟩
      (⟨0⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
        cageVatWord σ I :: cageRadWord I :: ⟨360⟩ :: sel :: [])
      mem aw out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flapperBytecode g (initState cA gh bl σStart σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨3293⟩) (okPc := ⟨3309⟩) rd3293
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

theorem flapperCageX_moveCallSuccess
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (rd3293 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨3293⟩
      (⟨1⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
        cageVatWord σ I :: cageRadWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    RDret flapperBytecode g (initState cA gh bl σStart σ₀ g A I)
      (cA', σ') ByteArray.empty := by
  obtain ⟨k3311, C3311, rd3311raw⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨3293⟩) (okPc := ⟨3309⟩) rd3293
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3311 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨3311⟩
      (cageMoveEndPtr :: cageMoveSelectorWord :: cageVatWord σ I :: cageRadWord I ::
        ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k3311 C3311 := by
    simpa [show ((⟨3309⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨3311⟩ from by native_decide]
      using rd3311raw
  have rd3315 := evm_run rd3311 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd360 := rd3315.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd361 := rd360.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd361 (by native_decide) (by evm_ov)

theorem cageSlotWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperSlotWord slot σ I = flapperSlotWord slot τ I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩

theorem cageAddressReturnWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperAddressReturnWord slot σ I = flapperAddressReturnWord slot τ I := by
  simp [flapperAddressReturnWord, cageSlotWord_accountMapEquiv hAccounts slot]

theorem cageCodeSize_ne_accountMapEquiv_addressSlot {σ τ : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ) (slot : UInt256)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flapperAddressReturnWord slot σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flapperAddressReturnWord slot τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (flapperAddressReturnWord slot σ I)
  have htarget :
      flapperAddressReturnWord slot σ I = flapperAddressReturnWord slot τ I :=
    cageAddressReturnWord_accountMapEquiv hAccounts slot
  rw [hsame, htarget]
  exact hzero

theorem cageCodeSize_zero_accountMapEquiv_addressSlot {σ τ : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ) (slot : UInt256)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flapperAddressReturnWord slot σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flapperAddressReturnWord slot τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (flapperAddressReturnWord slot σ I)
  have htarget :
      flapperAddressReturnWord slot σ I = flapperAddressReturnWord slot τ I :=
    cageAddressReturnWord_accountMapEquiv hAccounts slot
  rw [← htarget, ← hsame]
  exact hzero

theorem cageStorageStore_sigma0 (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem cageStorageStore_genesisBlockHeader (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem cageStorageStore_blocks (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).blocks = evm.blocks := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem cageStorageStore_substate (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).substate = evm.substate := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem evalExpr_cage_extCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_cage_extCodeGuard_false {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_cage_vat_storage_of_locals
    (evm : EVM.State) (locals : Store) (hvat : "vat" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (flapperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (AccountAddress.ofNat
      (flapperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat))
    (by simpa [frame, vatRef] using hvat)
    (by simp [frame, evalStorageRef, evalStorageRefSteps, vatRef,
      EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [flapperAddressReturnWord, flapperSlotWord] using
        flapperStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_cage_this (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm thisAddr =
      .ok (.address evm.executionEnv.codeOwner) := by
  simp [thisAddr, evalExpr?, envValue, pure]

theorem evalExpr_cage_sender (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExprs_cage_move_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := cageLocals I } evm
        [thisAddr, sender, .var "rad"] =
      .ok [.address evm.executionEnv.codeOwner, .address evm.executionEnv.source,
        cageRadValue I] := by
  simp [evalExprs?, evalExpr_cage_this, evalExpr_cage_sender, evalExpr_cage_rad_var]
  rfl

theorem flapperCageBodyReverts_unauthorized (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (cageLocals I) cageTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts,
    List.cons_append, List.nil_append] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := cageLocals I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest :=
        [.assign .storage liveRef (.intLit 0)] ++
          checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [thisAddr, sender, .var "rad"] "_moveRet")
      hwv
      (evalExpr_auth_false_of_wards_none evm I (cageLocals I)
        (cageLocals_get_wards I) hsrc hauth)

theorem flapperCageBodyReverts_moveNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hnoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostState evm).accountMap
        (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
          (cageLivePostState evm).executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (cageLocals I) cageTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := cageLocals I }
          (cageLivePostState evm) (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat)) :=
    evalExpr_cage_vat_storage_of_locals (cageLivePostState evm) (cageLocals I)
      (by simp [cageLocals])
  have hnoCodeLookup :
      (UInt256.ofNat
        (((cageLivePostState evm).lookupAccount
          (AccountAddress.ofNat
            (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
              (cageLivePostState evm).executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      Benchmarks.Dss.Flopper.flopperExtCodeSizeWord_zero_lookup_code_zero
        (σ := (cageLivePostState evm).accountMap)
        (target := flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
          (cageLivePostState evm).executionEnv)
        (addr := AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := cageLocals I }
        (cageLivePostState evm)
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_cage_extCodeGuard_false hvat hnoCodeLookup
  have hchecked :
      ExecBlock config { contract := contract, locals := cageLocals I }
        (cageLivePostState evm)
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, sender, .var "rad"] "_moveRet")
        .reverted := by
    exact checkedExternalCallNoCode hguard
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts,
    List.cons_append, List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (cageLocals I)
            (cageLocals_get_wards I) hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (by simp [evalExpr?, pure]) (cageAssignLive evm I)) <|
      hchecked)

theorem flapperCageBodyReverts_moveCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostState evm).accountMap
        (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
          (cageLivePostState evm).executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (cageLivePostState evm)
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat))
        "move" 0
        [.address (cageLivePostState evm).executionEnv.codeOwner,
          .address (cageLivePostState evm).executionEnv.source, cageRadValue I]
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (cageLocals I) cageTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := cageLocals I }
          (cageLivePostState evm) (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat)) :=
    evalExpr_cage_vat_storage_of_locals (cageLivePostState evm) (cageLocals I)
      (by simp [cageLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        (((cageLivePostState evm).lookupAccount
          (AccountAddress.ofNat
            (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
              (cageLivePostState evm).executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      Benchmarks.Dss.Flopper.flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := (cageLivePostState evm).accountMap)
        (target := flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
          (cageLivePostState evm).executionEnv)
        (addr := AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := cageLocals I }
        (cageLivePostState evm)
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_cage_move_args (cageLivePostState evm) I
  have hchecked :
      ExecBlock config { contract := contract, locals := cageLocals I }
        (cageLivePostState evm)
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, sender, .var "rad"] "_moveRet")
        .reverted := by
    exact checkedExternalCallFailure hguard hvat hargs hcall
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts,
    List.cons_append, List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (cageLocals I)
            (cageLocals_get_wards I) hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (by simp [evalExpr?, pure]) (cageAssignLive evm I)) <|
      hchecked)

theorem flapperCageBodyReturns_moveCallSuccess
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostState evm).accountMap
        (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
          (cageLivePostState evm).executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (cageLivePostState evm)
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat))
        "move" 0
        [.address (cageLivePostState evm).executionEnv.codeOwner,
          .address (cageLivePostState evm).executionEnv.source, cageRadValue I]
        (true, evm', out) true) :
    ExecTransitionBody config contract evm (cageLocals I) cageTransition.body
      (.returned { contract := contract, locals := cageMoveLocals I } evm' none) := by
  have hvat :
      evalExpr? config { contract := contract, locals := cageLocals I }
          (cageLivePostState evm) (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat)) :=
    evalExpr_cage_vat_storage_of_locals (cageLivePostState evm) (cageLocals I)
      (by simp [cageLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        (((cageLivePostState evm).lookupAccount
          (AccountAddress.ofNat
            (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
              (cageLivePostState evm).executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      Benchmarks.Dss.Flopper.flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := (cageLivePostState evm).accountMap)
        (target := flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
          (cageLivePostState evm).executionEnv)
        (addr := AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evm).accountMap
            (cageLivePostState evm).executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := cageLocals I }
        (cageLivePostState evm)
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_cage_move_args (cageLivePostState evm) I
  have hdec : config.externalABI.decode? "move" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hchecked :
      ExecBlock config { contract := contract, locals := cageLocals I }
        (cageLivePostState evm)
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, sender, .var "rad"] "_moveRet")
        (.ok { contract := contract, locals := cageMoveLocals I } evm') := by
    simpa [checkedExternalCallStmts, cageMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall hdec
  refine ExecFuncBody.execBlockOK ?_
  simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts,
    List.cons_append, List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (cageLocals I)
            (cageLocals_get_wards I) hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (by simp [evalExpr?, pure]) (cageAssignLive evm I)) <|
      hchecked)

theorem flapperCageBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some (cageLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨700⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolmWord : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (cageLocals I)
        cageTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperCageBodyReverts_unauthorized evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthSolmWord
  obtain ⟨_, _, rd3106⟩ :=
    flapperCageX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
  exact (flapperCageX_unauthorized (I := I) hauth rd3106)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperCageBodyCoreMoveNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hnoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_evm)
        (cageVatWord (cageLivePostAccountMap I σ_evm) I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some (cageLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨700⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolmWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hAccountsLive :
      accountMapEquiv (cageLivePostAccountMap I σ_evm) (cageLivePostAccountMap I σ_solm) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩ ⟨0⟩ hAccounts
  have hnoCodeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_solm)
        (flapperAddressReturnWord ⟨2⟩ (cageLivePostAccountMap I σ_solm) I) = ⟨0⟩ := by
    simpa [cageVatWord] using
      cageCodeSize_zero_accountMapEquiv_addressSlot hAccountsLive ⟨2⟩ hnoCode
  have hnoCodePost :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostState evmSolm).accountMap
        (flapperAddressReturnWord ⟨2⟩ (cageLivePostState evmSolm).accountMap
          (cageLivePostState evmSolm).executionEnv) = ⟨0⟩ := by
    simpa [evmSolm, cageLivePostState, cageLivePostAccountMap, initState,
      storageStore_accountMap, storageStore_executionEnv] using hnoCodeSolm
  have hbody :
      ExecTransitionBody config contract evmSolm (cageLocals I)
        cageTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperCageBodyReverts_moveNoCode evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        (by
          simpa [evmSolm, relyAuthWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using hauthSolmWord)
        hnoCodePost
  obtain ⟨_, _, rd3106⟩ :=
    flapperCageX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
  obtain ⟨_, _, rd3199⟩ :=
    flapperCageX_authorized (I := I) hauth rd3106
  obtain ⟨_, _, rd3207⟩ :=
    flapperCageX_storeLive hperm rd3199
  exact (flapperCageX_moveNoCode (g := Sat256.ofUInt256 g) hnoCode rd3207)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperCageBodyCoreMoveCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_evm)
        (cageVatWord (cageLivePostAccountMap I σ_evm) I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some (cageLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨700⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLiveSolm := cageLivePostState evmSolm
  let vat := flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap evmLiveSolm.executionEnv
  let src := cageThisWord I
  let guy := cageSenderWord I
  let rad := cageRadWord I
  let A_move := (evmLiveSolm.addAccessedAccount
    (EVM.address (AccountAddress.ofNat vat.toNat))).substate
  have hmem : (relyAuthHashMem I).size = 96 := relyAuthHashMem_size I
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    have hsizeAddr : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsizeAddr)]
    rw [show src = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, cageSenderWord, solcSourceWord] using solcSourceWord_canonical I
  have hsrcAddr : AccountAddress.ofNat src.toNat = I.codeOwner := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [src, cageThisWord] using accountAddress_roundtrip I.codeOwner
  have hguyAddr : AccountAddress.ofNat guy.toNat = I.source := by
    simpa [guy, cageSenderWord, solcSourceWord] using solcSource_ofNat I
  have hdepthLive : evmLiveSolm.executionEnv.depth = 1024 := by
    simpa [evmLiveSolm, evmSolm, cageLivePostState, initState,
      storageStore_executionEnv] using hdepth
  have hcallSolm :
      typedCallViaEVM config evmLiveSolm
        (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
        [.address evmLiveSolm.executionEnv.codeOwner,
          .address evmLiveSolm.executionEnv.source, cageRadValue I]
        (false, { evmLiveSolm with substate := A_move }, ByteArray.empty) true := by
    simpa [evmLiveSolm, evmSolm, cageLivePostState, initState,
      storageStore_executionEnv, A_move, vat, src, guy, rad, hsrcAddr, hguyAddr,
      cageRadValue, cageRadWord] using
      (callNotMade_depthLimit (cfg := config) (evm := evmLiveSolm)
        (tgt := EVM.address (AccountAddress.ofNat vat.toNat)) (name := "move")
        (args := [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat rad.toNat)])
        (callPerm := true)
        (calldata := (cageMoveCalldataMem src guy rad (relyAuthHashMem I)).readWithPadding
          cageMoveOutPtr.toNat cageMoveInSize.toNat)
        (cageMoveEncode_eq src guy rad hmem hsrcCanon hguyCanon)
        hdepthLive)
  have hauthSolmWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hAccountsLive :
      accountMapEquiv (cageLivePostAccountMap I σ_evm) (cageLivePostAccountMap I σ_solm) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩ ⟨0⟩ hAccounts
  have hcodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord evmLiveSolm.accountMap
        (flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap evmLiveSolm.executionEnv) ≠
          ⟨0⟩ := by
    have hcodeSizeSolmMap :
        Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_solm)
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostAccountMap I σ_solm) I) ≠ ⟨0⟩ := by
      simpa [cageVatWord] using
        cageCodeSize_ne_accountMapEquiv_addressSlot hAccountsLive ⟨2⟩ hcodeSize
    simpa [evmLiveSolm, evmSolm, cageLivePostState, cageLivePostAccountMap, initState,
      storageStore_accountMap, storageStore_executionEnv] using hcodeSizeSolmMap
  have hbody :
      ExecTransitionBody config contract evmSolm (cageLocals I)
        cageTransition.body .reverted := by
    simpa [evmSolm, evmLiveSolm, relyAuthWord, flapperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flapperCageBodyReverts_moveCallFailure evmSolm
        { evmLiveSolm with substate := A_move } I ByteArray.empty
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        (by
          simpa [evmSolm, relyAuthWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using hauthSolmWord)
        hcodeSizeSolm hcallSolm
  obtain ⟨_, _, rd3106⟩ :=
    flapperCageX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
  obtain ⟨_, _, rd3199⟩ :=
    flapperCageX_authorized (I := I) hauth rd3106
  obtain ⟨_, _, rd3207⟩ :=
    flapperCageX_storeLive hperm rd3199
  obtain ⟨_, _, rd3293⟩ :=
    flapperCageX_moveCallDepthLimit (g := Sat256.ofUInt256 g) hcodeSize hdepth rd3207
  exact (flapperCageX_moveCallFailure rd3293 (by native_decide))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperCageBodyCoreMoveCallFailure
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flapperBytecode)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_evm)
        (cageVatWord (cageLivePostAccountMap I σ_evm) I) ≠ ⟨0⟩)
    (rd3293 : RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3293⟩
      (⟨0⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
        cageVatWord (cageLivePostAccountMap I σ_evm) I :: cageRadWord I ::
        ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := cageLivePostAccountMap I σ_evm })
        (EVM.address (AccountAddress.ofNat
          (cageVatWord (cageLivePostAccountMap I σ_evm) I).toNat))
        "move" 0
        [.address I.codeOwner, .address I.source, .int (Int.ofNat (cageRadWord I).toNat)]
        (false,
          { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := cageLivePostAccountMap I σ_evm } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (houtSize : out.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some (cageLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := cageLivePostAccountMap I σ_evm }
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLiveSolm := cageLivePostState evmSolm
  have hAccountsLiveMap :
      accountMapEquiv (cageLivePostAccountMap I σ_evm) (cageLivePostAccountMap I σ_solm) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩ ⟨0⟩ hAccounts
  have hLiveAccounts : accountMapEquiv evmEvm.accountMap evmLiveSolm.accountMap := by
    simpa [evmEvm, evmLiveSolm, evmSolm, cageLivePostState, cageLivePostAccountMap,
      initState, storageStore_accountMap] using hAccountsLiveMap
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hpostAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (hcall := hcall) hLiveAccounts
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_sigma0])
      (by simp [evmEvm, evmLiveSolm, evmSolm, cageLivePostState, initState,
        storageStore_createdAccounts])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_genesisBlockHeader])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_blocks])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_substate])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        storageStore_executionEnv])
  let evmCallSolm : EVM.State :=
    { evmLiveSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hvatEq :
      cageVatWord (cageLivePostAccountMap I σ_evm) I =
        flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap evmLiveSolm.executionEnv := by
    have hword := cageAddressReturnWord_accountMapEquiv (I := I) hAccountsLiveMap ⟨2⟩
    simpa [cageVatWord, evmLiveSolm, evmSolm, cageLivePostState,
      cageLivePostAccountMap, initState, storageStore_accountMap,
      storageStore_executionEnv] using hword
  have hcallSolm :
      typedCallViaEVM config evmLiveSolm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap
            evmLiveSolm.executionEnv).toNat))
        "move" 0
        [.address evmLiveSolm.executionEnv.codeOwner,
          .address evmLiveSolm.executionEnv.source, cageRadValue I]
        (false, evmCallSolm, out) true := by
    simpa [evmEvm, evmLiveSolm, evmSolm, evmCallSolm, cageLivePostState,
      initState, storageStore_executionEnv, cageRadValue, cageRadWord, hvatEq]
      using hcallSolmRaw
  have hauthSolmWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hcodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord evmLiveSolm.accountMap
        (flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap evmLiveSolm.executionEnv) ≠
          ⟨0⟩ := by
    have hcodeSizeSolmMap :
        Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_solm)
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostAccountMap I σ_solm) I) ≠ ⟨0⟩ := by
      simpa [cageVatWord] using
        cageCodeSize_ne_accountMapEquiv_addressSlot hAccountsLiveMap ⟨2⟩ hcodeSize
    simpa [evmLiveSolm, evmSolm, cageLivePostState, cageLivePostAccountMap, initState,
      storageStore_accountMap, storageStore_executionEnv] using hcodeSizeSolmMap
  have hbody :
      ExecTransitionBody config contract evmSolm (cageLocals I)
        cageTransition.body .reverted := by
    simpa [evmSolm, evmLiveSolm, evmCallSolm, relyAuthWord, flapperSlotWord,
      initState, Solm.EVM.storageLoad, State.lookupAccount] using
      flapperCageBodyReverts_moveCallFailure evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        (by
          simpa [evmSolm, relyAuthWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using hauthSolmWord)
        hcodeSizeSolm hcallSolm
  exact (flapperCageX_moveCallFailure rd3293 houtSize)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperCageBodyCoreMoveCallSuccess
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flapperBytecode)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_evm)
        (cageVatWord (cageLivePostAccountMap I σ_evm) I) ≠ ⟨0⟩)
    (rd3293 : RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3293⟩
      (⟨1⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
        cageVatWord (cageLivePostAccountMap I σ_evm) I :: cageRadWord I ::
        ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := cageLivePostAccountMap I σ_evm })
        (EVM.address (AccountAddress.ofNat
          (cageVatWord (cageLivePostAccountMap I σ_evm) I).toNat))
        "move" 0
        [.address I.codeOwner, .address I.source, .int (Int.ofNat (cageRadWord I).toNat)]
        (true,
          { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := cageLivePostAccountMap I σ_evm } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some (cageLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := cageLivePostAccountMap I σ_evm }
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLiveSolm := cageLivePostState evmSolm
  have hAccountsLiveMap :
      accountMapEquiv (cageLivePostAccountMap I σ_evm) (cageLivePostAccountMap I σ_solm) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩ ⟨0⟩ hAccounts
  have hLiveAccounts : accountMapEquiv evmEvm.accountMap evmLiveSolm.accountMap := by
    simpa [evmEvm, evmLiveSolm, evmSolm, cageLivePostState, cageLivePostAccountMap,
      initState, storageStore_accountMap] using hAccountsLiveMap
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (hcall := hcall) hLiveAccounts
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_sigma0])
      (by simp [evmEvm, evmLiveSolm, evmSolm, cageLivePostState, initState,
        storageStore_createdAccounts])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_genesisBlockHeader])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_blocks])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        cageStorageStore_substate])
      (by simp [evmLiveSolm, evmSolm, cageLivePostState, initState,
        storageStore_executionEnv])
  let evmCallSolm : EVM.State :=
    { evmLiveSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hvatEq :
      cageVatWord (cageLivePostAccountMap I σ_evm) I =
        flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap evmLiveSolm.executionEnv := by
    have hword := cageAddressReturnWord_accountMapEquiv (I := I) hAccountsLiveMap ⟨2⟩
    simpa [cageVatWord, evmLiveSolm, evmSolm, cageLivePostState,
      cageLivePostAccountMap, initState, storageStore_accountMap,
      storageStore_executionEnv] using hword
  have hcallSolm :
      typedCallViaEVM config evmLiveSolm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap
            evmLiveSolm.executionEnv).toNat))
        "move" 0
        [.address evmLiveSolm.executionEnv.codeOwner,
          .address evmLiveSolm.executionEnv.source, cageRadValue I]
        (true, evmCallSolm, out) true := by
    simpa [evmEvm, evmLiveSolm, evmSolm, evmCallSolm, cageLivePostState,
      initState, storageStore_executionEnv, cageRadValue, cageRadWord, hvatEq]
      using hcallSolmRaw
  have hauthSolmWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hcodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord evmLiveSolm.accountMap
        (flapperAddressReturnWord ⟨2⟩ evmLiveSolm.accountMap evmLiveSolm.executionEnv) ≠
          ⟨0⟩ := by
    have hcodeSizeSolmMap :
        Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_solm)
          (flapperAddressReturnWord ⟨2⟩ (cageLivePostAccountMap I σ_solm) I) ≠ ⟨0⟩ := by
      simpa [cageVatWord] using
        cageCodeSize_ne_accountMapEquiv_addressSlot hAccountsLiveMap ⟨2⟩ hcodeSize
    simpa [evmLiveSolm, evmSolm, cageLivePostState, cageLivePostAccountMap, initState,
      storageStore_accountMap, storageStore_executionEnv] using hcodeSizeSolmMap
  have hbody :
      ExecTransitionBody config contract evmSolm (cageLocals I)
        cageTransition.body
        (.returned { contract := contract, locals := cageMoveLocals I } evmCallSolm none) := by
    simpa [evmSolm, evmLiveSolm, evmCallSolm, relyAuthWord, flapperSlotWord,
      initState, Solm.EVM.storageLoad, State.lookupAccount] using
      flapperCageBodyReturns_moveCallSuccess evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        (by
          simpa [evmSolm, relyAuthWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using hauthSolmWord)
        hcodeSizeSolm hcallSolm
  exact (flapperCageX_moveCallSuccess rd3293)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [evmCallSolm, evmLiveSolm, evmSolm, cageLivePostState, initState,
        storageStore_createdAccounts])
      (by simpa [evmCallSolm] using hpostAccounts)
      (by
        simpa [cageTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flapperCageBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨700⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperCageX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch
      (flapperDecode_cage_none_short hsz4 hshort)

theorem flapperCageBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    flapperDispatchCage hsel
  have hreach := flapperReachCageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := flapperDecode_cage_ok (I := I) hsz36
    by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hnoCode :
          Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_evm)
            (cageVatWord (cageLivePostAccountMap I σ_evm) I) = ⟨0⟩
      · exact flapperCageBodyCoreMoveNoCode hcode hsize hperm hwv hsz36 hauth
          hnoCode hdispatch hdecode hreach hAccounts
      · have hcodeSize :
            Reasoning.Theory.uniswapExtCodeSizeWord (cageLivePostAccountMap I σ_evm)
              (cageVatWord (cageLivePostAccountMap I σ_evm) I) ≠ ⟨0⟩ := hnoCode
        by_cases hdepthEq : I.depth = 1024
        · exact flapperCageBodyCoreMoveCallDepthLimit hcode hsize hperm hwv hsz36
            hauth hcodeSize hdepthEq hdispatch hdecode hreach hAccounts
        · have hdepthLt : I.depth.val < 1024 := by
            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            by_contra hn
            have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
            have hval : I.depth.val = 1024 := by omega
            apply hdepthEq
            apply Fin.ext
            exact hval
          obtain ⟨_, _, rd3106⟩ :=
            flapperCageX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
          obtain ⟨_, _, rd3199⟩ :=
            flapperCageX_authorized (I := I) hauth rd3106
          obtain ⟨_, _, rd3207⟩ :=
            flapperCageX_storeLive hperm rd3199
          obtain ⟨cA', σ', z, out, A', k3293, C3293, rd3293, hcall,
              houtSize⟩ :=
            flapperCageX_moveCall (g := Sat256.ofUInt256 g) hperm hcodeSize
              hdepthLt rd3207
          by_cases hz : z = true
          · have rd3293True : RD flapperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3293⟩
                (⟨1⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
                  cageVatWord (cageLivePostAccountMap I σ_evm) I :: cageRadWord I ::
                  ⟨360⟩ :: flapperSelWord I :: [])
                (cageMoveCalldataMem (cageThisWord I) (cageSenderWord I)
                  (cageRadWord I) (relyAuthHashMem I))
                (UInt256.ofNat 8) out (cA', σ') k3293 C3293 := by
              simpa [hz] using rd3293
            have hcallTrue :
                typedCallViaEVM config
                  ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := cageLivePostAccountMap I σ_evm })
                  (EVM.address (AccountAddress.ofNat
                    (cageVatWord (cageLivePostAccountMap I σ_evm) I).toNat))
                  "move" 0
                  [.address I.codeOwner, .address I.source,
                    .int (Int.ofNat (cageRadWord I).toNat)]
                  (true,
                    { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := cageLivePostAccountMap I σ_evm } with
                        accountMap := σ', substate := A', createdAccounts := cA' },
                    out) true := by
              simpa [hz] using hcall
            exact flapperCageBodyCoreMoveCallSuccess hcode hperm hwv hauth hcodeSize
              rd3293True hcallTrue hdispatch hdecode hAccounts
          · have hzFalse : z = false := by
              cases z <;> simp at hz ⊢
            have rd3293False : RD flapperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3293⟩
                (⟨0⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
                  cageVatWord (cageLivePostAccountMap I σ_evm) I :: cageRadWord I ::
                  ⟨360⟩ :: flapperSelWord I :: [])
                (cageMoveCalldataMem (cageThisWord I) (cageSenderWord I)
                  (cageRadWord I) (relyAuthHashMem I))
                (UInt256.ofNat 8) out (cA', σ') k3293 C3293 := by
              simpa [hzFalse] using rd3293
            have hcallFalse :
                typedCallViaEVM config
                  ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := cageLivePostAccountMap I σ_evm })
                  (EVM.address (AccountAddress.ofNat
                    (cageVatWord (cageLivePostAccountMap I σ_evm) I).toNat))
                  "move" 0
                  [.address I.codeOwner, .address I.source,
                    .int (Int.ofNat (cageRadWord I).toNat)]
                  (false,
                    { { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := cageLivePostAccountMap I σ_evm } with
                        accountMap := σ', substate := A', createdAccounts := cA' },
                    out) true := by
              simpa [hzFalse] using hcall
            exact flapperCageBodyCoreMoveCallFailure hcode hperm hwv hauth hcodeSize
              rd3293False hcallFalse houtSize hdispatch hdecode hAccounts
    · exact flapperCageBodyCoreUnauthorized hcode hsize hwv hsz36 hauth
        hdispatch hdecode hreach hAccounts
  · exact flapperCageBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flapper

import Benchmarks.Dss.Clipper.Deny
import Benchmarks.Dss.Clipper.FileDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## `file(bytes32,uint256)` -/

abbrev clipperFileUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev clipperFileUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev clipperFileUintBufBytes : List UInt8 :=
  [98, 117, 102] ++ zeroPad29

abbrev clipperFileUintTailBytes : List UInt8 :=
  [116, 97, 105, 108] ++ zeroPad28

abbrev clipperFileUintCuspBytes : List UInt8 :=
  [99, 117, 115, 112] ++ zeroPad28

abbrev clipperFileUintChipBytes : List UInt8 :=
  [99, 104, 105, 112] ++ zeroPad28

abbrev clipperFileUintTipBytes : List UInt8 :=
  [116, 105, 112] ++ zeroPad29

abbrev clipperFileUintStoppedBytes : List UInt8 :=
  [115, 116, 111, 112, 112, 101, 100] ++ zeroPad25

abbrev clipperFileUintLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (clipperFileUintWhat I))).insert
    "data" (.int (Int.ofNat (clipperFileUintData I).toNat))

def clipperFileUintPostState (evm : EVM.State) (slot value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value

def clipperFileUintLockedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩

def clipperFileUintWordPostState (evm : EVM.State) (slot value : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore (clipperFileUintLockedState evm) evm.executionEnv.codeOwner slot value)
    evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩

abbrev clipperFileUintUint64Mask : UInt256 :=
  UInt256.ofNat (2 ^ 64 - 1)

abbrev clipperFileUintUint192Mask : UInt256 :=
  UInt256.ofNat (2 ^ 192 - 1)

abbrev clipperFileUintHigh64Mask : UInt256 :=
  UInt256.ofNat (2 ^ 256 - 2 ^ 64)

abbrev clipperFileUintShift64 : UInt256 :=
  UInt256.ofNat (2 ^ 64)

abbrev clipperFileUintChipData (I : ExecutionEnv) : UInt256 :=
  UInt256.land (clipperFileUintData I) clipperFileUintUint64Mask

abbrev clipperFileUintTipData (I : ExecutionEnv) : UInt256 :=
  UInt256.land (clipperFileUintData I) clipperFileUintUint192Mask

def clipperFileUintChipWord (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land clipperFileUintHigh64Mask old)
    (UInt256.land data clipperFileUintUint64Mask)

def clipperFileUintTipWord (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old clipperFileUintUint64Mask)
    (UInt256.mul (UInt256.land data clipperFileUintUint192Mask) clipperFileUintShift64)

def clipperFileUintChipPostState (evm : EVM.State) (data : UInt256) : EVM.State :=
  let evmLock := clipperFileUintLockedState evm
  let old := Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨8⟩
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨8⟩
      (clipperFileUintChipWord old data)
  Solm.EVM.storageStore evmStore evmStore.executionEnv.codeOwner ⟨13⟩ ⟨0⟩

def clipperFileUintTipPostState (evm : EVM.State) (data : UInt256) : EVM.State :=
  let evmLock := clipperFileUintLockedState evm
  let old := Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨8⟩
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨8⟩
      (clipperFileUintTipWord old data)
  Solm.EVM.storageStore evmStore evmStore.executionEnv.codeOwner ⟨13⟩ ⟨0⟩

theorem clipperFileUintWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (clipperFileUintWhat I).length = 32 := by
  simp [clipperFileUintWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem clipperFileUintWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (clipperFileUintWhat I) = calldataWord I.calldata 4 := by
  simpa [clipperFileUintWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem clipperFileUintWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    clipperFileUintWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := clipperFileUintWhat I)
    (clipperFileUintWhat_length (I := I) hsz36)
  rw [clipperFileUintWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem clipperFileUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : clipperFileUintWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (clipperFileUintWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem clipperDecode_fileUint_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata =
        some (clipperFileUintLocals I) := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    clipperFileUintLocals, clipperFileUintWhat, clipperFileUintData, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem clipperDecode_fileUint_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem clipperFileUintLocals_get_what (I : ExecutionEnv) :
    (clipperFileUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (clipperFileUintWhat I)) := by
  rw [clipperFileUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem clipperFileUintLocals_get_data (I : ExecutionEnv) :
    (clipperFileUintLocals I).get? "data" =
      some (.int (Int.ofNat (clipperFileUintData I).toNat)) := by
  rw [clipperFileUintLocals, store_get_self]

theorem clipperFileUintLocals_get_base_none (I : ExecutionEnv)
    {name : Ident} (hwhat : name ≠ "what") (hdata : name ≠ "data") :
    (clipperFileUintLocals I).get? name = none := by
  have hdataBeq : ("data" == name) = false := by
    exact beq_eq_false_iff_ne.mpr (by intro h; exact hdata h.symm)
  have hwhatBeq : ("what" == name) = false := by
    exact beq_eq_false_iff_ne.mpr (by intro h; exact hwhat h.symm)
  unfold clipperFileUintLocals
  rw [store_get_ne _ _ hdataBeq, store_get_ne _ _ hwhatBeq]
  simp

theorem evalExpr_clipperFileUint_data {v : ClipperImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (clipperFileUintData I).toNat))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (clipperFileUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (clipperFileUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_clipperFileUint_what_eq_true {v : ClipperImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (clipperFileUintWhat I)))
    (hwhat : clipperFileUintWhat I = bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (clipperFileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (clipperFileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_clipperFileUint_what_eq_false {v : ClipperImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (clipperFileUintWhat I)))
    (hwhat : clipperFileUintWhat I ≠ bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (clipperFileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (clipperFileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem clipperFileUintSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 9)) :
    clipperSelWord I = clipperSelNat 9 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 (clipperSelNat 9)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_fileUint (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 9)) :
    dispatchMsg (contract v) I.calldata = some fileUintTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition])
    (post :=
      [fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
        upchostTransition v, vatTransition v, vowTransition, wardsTransition, yankTransition v])
    (ti := fileUintTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
theorem clipperReachFileUintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 9)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨673⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperFileUintSelectorWord hsz hsel
  have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 20, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨260⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by native_decide))
    (by simp)
  have h272 := clipperSplitNotTaken (pc := (⟨261⟩ : UInt256))
    (next := (⟨272⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
      (by simp))
    (by change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 9, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨369⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h331 := clipperSplitTaken (pc := (⟨272⟩ : UInt256)) (pivot := clipperSelNat 6)
    (tgt := (⟨331⟩ : UInt256)) h272
    (by change decode code (⟨272⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨272⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 6, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨272⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨272⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨331⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨272⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨331⟩ : UInt256) (by native_decide))
    (by simp)
  have h673 := clipperArmTaken (pc := (⟨332⟩ : UInt256)) (sel := clipperSelNat 9)
    (tgt := (⟨673⟩ : UInt256))
    (h331.jumpdest
      (by change decode code (⟨331⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
      (by simp))
    (by change decode code (⟨332⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨332⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 9, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨332⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨332⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨673⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨332⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨673⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h673⟩

theorem clipperFileUintRoutineJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2621⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem RD.clipperFileUintDecodeToRoutine (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨695⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J code 0).contains ⟨2621⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2621⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd696 := h.jumpdest (by clipper_decode) (by evm_ov)
  have rd697 := rd696.pop (by clipper_decode) (by evm_ov)
  have rd698 := rd697.dup1 (by clipper_decode) (by evm_ov)
  have rd699 := rd698.calldataload (by clipper_decode) (by evm_ov)
  have rd700 := rd699.swap1 (by clipper_decode) (by evm_ov)
  have rd702 := rd700.push1 ⟨32⟩ (by clipper_decode) (by evm_ov)
  have rd703 := rd702.add (by clipper_decode) (by evm_ov)
  have rd704 := rd703.calldataload (by clipper_decode) (by evm_ov)
  have rd707 := rd704.push2 ⟨2621⟩ (by clipper_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd707.jump (by clipper_decode) hroutine (by evm_ov)⟩

theorem clipperFileUintDecodedToBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    {sel : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (⟨673⟩ : UInt256) [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨2621⟩ : UInt256)
      (clipperFileUintData I :: calldataWord I.calldata 4 :: ⟨502⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨673⟩) (ret := ⟨502⟩)
    (decoded := ⟨695⟩) hreach
    (by change decode code (⟨673⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2) = some (.DUP1, .none)
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩) = some (.CALLDATASIZE, .none)
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.SUB, .none)
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1))
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.DUP2, .none)
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none)
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none)
      clipper_decode)
    (by
      change decode code ((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (⟨695⟩, 2))
      clipper_decode)
    (by
      change decode code (((⟨673⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none)
      clipper_decode)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨695⟩ : UInt256) (by native_decide))
    hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.clipperFileUintDecodeToRoutine
    (ret := ⟨502⟩) (sel := sel) (R := []) v hpatch hdecoded
    (clipperFileUintRoutineJumpDest v hpatch) (by simp)
  exact ⟨_, _, by simpa [clipperFileUintData] using hroutine⟩

theorem evalStorageRef_clipperFileUint_auth (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      (wardsRef sender) = .ok (clipperRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue,
    clipperRelyAuthEvaledRef, clipperRelyAuthKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_clipperFileUint_auth_true (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileUintLocals I })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_auth v evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using clipperStorageLocLoad_uint256 evm
          (clipperRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_clipperFileUint_auth_false (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileUintLocals I })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_auth v evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact clipperStorageLocLoad_uint256 evm (clipperRelyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperRelyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact clipperUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperRelyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperRelyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalStorageRef_clipperFileUint_locked (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      lockedRef = .ok { base := "locked", steps := [] } := by
  simp [lockedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalExpr_clipperFileUint_locked_zero_true (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
        (.storage lockedRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileUintLocals I })
      (slot := lockedRef)
      (er := { base := "locked", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨13⟩)
      (value := .int 0)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_locked v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using clipperStorageLocLoad_uint256 evm ⟨13⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_clipperFileUint_locked_zero_false (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
        (.storage lockedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileUintLocals I })
      (slot := lockedRef)
      (er := { base := "locked", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨13⟩)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_locked v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact clipperStorageLocLoad_uint256 evm ⟨13⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat))
      (Value.int 0) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem assign_clipperFileUint_locked (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (value : UInt256) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      .storage lockedRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract v, locals := clipperFileUintLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ value) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨13⟩)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_locked v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨13⟩ value

theorem evalStorageRef_clipperFileUint_buf (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      bufRef = .ok { base := "buf", steps := [] } := by
  simp [bufRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem assign_clipperFileUint_buf (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (data : UInt256) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      .storage bufRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract v, locals := clipperFileUintLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ data) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨5⟩)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_buf v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨5⟩ data

theorem evalStorageRef_clipperFileUint_tail (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      tailRef = .ok { base := "tail", steps := [] } := by
  simp [tailRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem assign_clipperFileUint_tail (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (data : UInt256) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      .storage tailRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract v, locals := clipperFileUintLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ data) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨6⟩)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_tail v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨6⟩ data

theorem evalStorageRef_clipperFileUint_cusp (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      cuspRef = .ok { base := "cusp", steps := [] } := by
  simp [cuspRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem assign_clipperFileUint_cusp (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (data : UInt256) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      .storage cuspRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract v, locals := clipperFileUintLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩ data) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨7⟩)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_cusp v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨7⟩ data

theorem evalStorageRef_clipperFileUint_stopped (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      stoppedRef = .ok { base := "stopped", steps := [] } := by
  simp [stoppedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem assign_clipperFileUint_stopped (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (data : UInt256) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      .storage stoppedRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract v, locals := clipperFileUintLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨14⟩ data) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨14⟩)
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_stopped v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨14⟩ data

theorem clipperFileUintUint64Mask_toNat :
    clipperFileUintUint64Mask.toNat = 2 ^ 64 - 1 := by
  native_decide

theorem clipperFileUintUint192Mask_toNat :
    clipperFileUintUint192Mask.toNat = 2 ^ 192 - 1 := by
  native_decide

theorem clipperFileUintShift64_toNat :
    clipperFileUintShift64.toNat = 2 ^ 64 := by
  native_decide

theorem clipperFileUintLand64_toNat (w : UInt256) :
    (UInt256.land w clipperFileUintUint64Mask).toNat = w.toNat % 2 ^ 64 := by
  rw [u256_land_toNat, clipperFileUintUint64Mask_toNat, nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 64))
    (by norm_num [UInt256.size]))

theorem clipperFileUintLand192_toNat (w : UInt256) :
    (UInt256.land w clipperFileUintUint192Mask).toNat = w.toNat % 2 ^ 192 := by
  rw [u256_land_toNat, clipperFileUintUint192Mask_toNat, nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 192))
    (by norm_num [UInt256.size]))

theorem clipperFileUintChipWord_toNat (old data : UInt256) :
    (clipperFileUintChipWord old data).toNat =
      (data.toNat % 2 ^ 64) + (old.toNat / 2 ^ 64) * 2 ^ 64 := by
  unfold clipperFileUintChipWord
  rw [u256_lor_toNat]
  have hhigh :
      (UInt256.land clipperFileUintHigh64Mask old).toNat =
        (old.toNat / 2 ^ 64) * 2 ^ 64 := by
    simpa [clipperFileUintHigh64Mask] using u256_land_high_mask_toNat old 64 (by norm_num)
  rw [hhigh, clipperFileUintLand64_toNat]
  have hlowLt : data.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hqLt : old.toNat / 2 ^ 64 < 2 ^ 192 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 64 * 2 ^ 192 = UInt256.size by norm_num [UInt256.size, Nat.pow_add]]
    exact old.val.isLt
  have hsum :
      data.toNat % 2 ^ 64 + old.toNat / 2 ^ 64 * 2 ^ 64 < UInt256.size := by
    calc
      data.toNat % 2 ^ 64 + old.toNat / 2 ^ 64 * 2 ^ 64
          ≤ (2 ^ 64 - 1) + (2 ^ 192 - 1) * 2 ^ 64 := by
            exact Nat.add_le_add (Nat.le_pred_of_lt hlowLt)
              (Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hqLt))
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  rw [nat_lor_comm]
  rw [nat_lor_shift_add (data.toNat % 2 ^ 64) (old.toNat / 2 ^ 64) 64 hlowLt]
  exact Nat.mod_eq_of_lt hsum

theorem clipperFileUintTipShifted_toNat (data : UInt256) :
    (UInt256.mul (UInt256.land data clipperFileUintUint192Mask)
      clipperFileUintShift64).toNat = (data.toNat % 2 ^ 192) * 2 ^ 64 := by
  rw [u256_mul_toNat, clipperFileUintLand192_toNat, clipperFileUintShift64_toNat]
  have hdataLt : data.toNat % 2 ^ 192 < 2 ^ 192 := Nat.mod_lt _ (by norm_num)
  have hprod : (data.toNat % 2 ^ 192) * 2 ^ 64 < UInt256.size := by
    calc
      (data.toNat % 2 ^ 192) * 2 ^ 64 ≤ (2 ^ 192 - 1) * 2 ^ 64 := by
        exact Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hdataLt)
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  exact Nat.mod_eq_of_lt hprod

theorem clipperFileUintTipWord_toNat (old data : UInt256) :
    (clipperFileUintTipWord old data).toNat =
      (old.toNat % 2 ^ 64) + (data.toNat % 2 ^ 192) * 2 ^ 64 := by
  unfold clipperFileUintTipWord
  rw [u256_lor_toNat, clipperFileUintLand64_toNat, clipperFileUintTipShifted_toNat]
  have hlowLt : old.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hdataLt : data.toNat % 2 ^ 192 < 2 ^ 192 := Nat.mod_lt _ (by norm_num)
  have hsum :
      old.toNat % 2 ^ 64 + (data.toNat % 2 ^ 192) * 2 ^ 64 < UInt256.size := by
    calc
      old.toNat % 2 ^ 64 + (data.toNat % 2 ^ 192) * 2 ^ 64
          ≤ (2 ^ 64 - 1) + (2 ^ 192 - 1) * 2 ^ 64 := by
            exact Nat.add_le_add (Nat.le_pred_of_lt hlowLt)
              (Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hdataLt))
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  rw [nat_lor_shift_add (old.toNat % 2 ^ 64) (data.toNat % 2 ^ 192) 64 hlowLt]
  exact Nat.mod_eq_of_lt hsum

theorem storageLocStore_clipperFileUint_chip (evm : EVM.State) (data : UInt256) :
    storageLocStore evm (uint64Loc ⟨8⟩ ⟨0, by decide⟩ (by decide))
        (.int (Int.ofNat (UInt256.land data clipperFileUintUint64Mask).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
        (clipperFileUintChipWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) data)) := by
  unfold storageLocStore storageLocWriteWord uint64Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof
    (UInt256.land data clipperFileUintUint64Mask)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (8 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (8 : Fin 33).val) _) =
        (clipperFileUintChipWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) data).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (8 : Fin 33).val = 8 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hmaskedLt :
      (UInt256.land data clipperFileUintUint64Mask).toNat < 2 ^ 64 := by
    rw [clipperFileUintLand64_toNat]
    exact Nat.mod_lt _ (by norm_num)
  rw [show 256 ^ 8 = (2 : Nat) ^ 64 by norm_num]
  rw [Nat.mod_eq_of_lt hmaskedLt]
  have hlen8 :
      ((EVM.Word.toBytesLEWithSizeProof
        (UInt256.land data clipperFileUintUint64Mask)).1.take 8).length = 8 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen8, show 2 ^ (8 * 8) = (2 : Nat) ^ 64 by norm_num,
    clipperFileUintChipWord_toNat]
  rw [clipperFileUintLand64_toNat]
  ring

theorem storageLocStore_clipperFileUint_tip (evm : EVM.State) (data : UInt256) :
    storageLocStore evm (uint192Loc ⟨8⟩ ⟨8, by decide⟩ (by decide))
        (.int (Int.ofNat (UInt256.land data clipperFileUintUint192Mask).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
        (clipperFileUintTipWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) data)) := by
  unfold storageLocStore storageLocWriteWord uint192Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof
    (UInt256.land data clipperFileUintUint192Mask)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (8 : Fin 32).val _ ++ List.take (24 : Fin 33).val _
        ++ List.drop ((8 : Fin 32).val + (24 : Fin 33).val) _) =
        (clipperFileUintTipWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) data).toNat
  rw [show (8 : Fin 32).val = 8 from rfl, show (24 : Fin 33).val = 24 from rfl]
  rw [show 8 + 24 = 32 by norm_num, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil]
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_take_wordLE]
  have holdLowLt :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 256 ^ 8 <
        256 ^ 8 := Nat.mod_lt _ (by norm_num)
  have hmaskedLt :
      (UInt256.land data clipperFileUintUint192Mask).toNat < 2 ^ 192 := by
    rw [clipperFileUintLand192_toNat]
    exact Nat.mod_lt _ (by norm_num)
  have hlen8 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)).1.take 8).length =
        8 := by
    rw [List.length_take, hslen]
    norm_num
  rw [hlen8, show 256 ^ 8 = (2 : Nat) ^ 64 by norm_num]
  rw [show 256 ^ 24 = (2 : Nat) ^ 192 by norm_num]
  rw [Nat.mod_eq_of_lt hmaskedLt, clipperFileUintTipWord_toNat]
  rw [clipperFileUintLand192_toNat]
  ring

theorem evalStorageRef_clipperFileUint_chip (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      chipRef = .ok { base := "chip", steps := [] } := by
  simp [chipRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalExpr_clipperFileUint_wrap64_data {v : ClipperImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (clipperFileUintData I).toNat))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (wrap64 (.var "data")) = .ok (.int (Int.ofNat (clipperFileUintChipData I).toNat)) := by
  have hdata :=
    evalExpr_clipperFileUint_data (v := v) (evm := evm) (I := I) (locals := locals) h
  rw [wrap64, evalExpr?]
  simp only [hdata, EvalResult.bind, bind]
  simp only [evalExpr?, evalBinaryOp?]
  norm_num [uint64Modulus, clipperFileUintChipData]
  · rw [clipperFileUintLand64_toNat]
    norm_num
  · decide
  · decide

theorem assign_clipperFileUint_chip (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      .storage chipRef (.int (Int.ofNat (clipperFileUintChipData I).toNat)) =
        .ok ({ contract := contract v, locals := clipperFileUintLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
            (clipperFileUintChipWord
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
              (clipperFileUintData I))) := by
  apply assignStorageRef_storage_scalar
      (ty := uint64St)
      (loc := uint64Loc ⟨8⟩ ⟨0, by decide⟩ (by decide))
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_chip v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint64St])
      (hloc := by rfl)
  simpa [clipperFileUintChipData] using
    storageLocStore_clipperFileUint_chip evm (clipperFileUintData I)

theorem evalStorageRef_clipperFileUint_tip (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      tipRef = .ok { base := "tip", steps := [] } := by
  simp [tipRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalExpr_clipperFileUint_wrap192_data {v : ClipperImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (clipperFileUintData I).toNat))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (wrap192 (.var "data")) = .ok (.int (Int.ofNat (clipperFileUintTipData I).toNat)) := by
  have hdata :=
    evalExpr_clipperFileUint_data (v := v) (evm := evm) (I := I) (locals := locals) h
  rw [wrap192, evalExpr?]
  simp only [hdata, EvalResult.bind, bind]
  simp only [evalExpr?, evalBinaryOp?]
  norm_num [uint192Modulus, clipperFileUintTipData]
  · rw [clipperFileUintLand192_toNat]
    norm_num
  · decide
  · decide

theorem assign_clipperFileUint_tip (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileUintLocals I } evm
      .storage tipRef (.int (Int.ofNat (clipperFileUintTipData I).toNat)) =
        .ok ({ contract := contract v, locals := clipperFileUintLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
            (clipperFileUintTipWord
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
              (clipperFileUintData I))) := by
  apply assignStorageRef_storage_scalar
      (ty := uint192St)
      (loc := uint192Loc ⟨8⟩ ⟨8, by decide⟩ (by decide))
      (hbase := by
        exact clipperFileUintLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileUint_tip v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint192St])
      (hloc := by rfl)
  simpa [clipperFileUintTipData] using
    storageLocStore_clipperFileUint_tip evm (clipperFileUintData I)

end Benchmarks.Dss.Clipper

import Benchmarks.Dss.Clipper.Rely
import Benchmarks.Dss.Clipper.FileDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## `file(bytes32,address)` -/

abbrev clipperFileAddressWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev clipperFileAddressDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev clipperFileAddressDataMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (clipperFileAddressDataWord I)

abbrev clipperFileAddressData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (clipperFileAddressDataWord I).toNat

abbrev clipperFileAddressSpotterBytes : List UInt8 :=
  [115, 112, 111, 116, 116, 101, 114] ++ zeroPad25

abbrev clipperFileAddressDogBytes : List UInt8 :=
  [100, 111, 103] ++ zeroPad29

abbrev clipperFileAddressVowBytes : List UInt8 :=
  [118, 111, 119] ++ zeroPad29

abbrev clipperFileAddressCalcBytes : List UInt8 :=
  [99, 97, 108, 99] ++ zeroPad28

abbrev clipperFileAddressLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (clipperFileAddressWhat I))).insert
    "data" (.address (clipperFileAddressData I))

def clipperFileAddressLockedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩

def clipperFileAddressPostState (evm : EVM.State) (slot data : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore (clipperFileAddressLockedState evm) evm.executionEnv.codeOwner
      slot
      (setAddressOffset0Word
        (Solm.EVM.storageLoad (clipperFileAddressLockedState evm)
          (clipperFileAddressLockedState evm).executionEnv.codeOwner slot)
        data))
    evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩

theorem clipperFileAddressWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (clipperFileAddressWhat I).length = 32 := by
  simp [clipperFileAddressWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem clipperFileAddressWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (clipperFileAddressWhat I) = calldataWord I.calldata 4 := by
  simpa [clipperFileAddressWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem clipperFileAddressWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    clipperFileAddressWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := clipperFileAddressWhat I)
    (clipperFileAddressWhat_length (I := I) hsz36)
  rw [clipperFileAddressWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem clipperFileAddressWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : clipperFileAddressWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (clipperFileAddressWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem clipperFileAddressDataMaskedWord_canonical (I : ExecutionEnv) :
    (clipperFileAddressDataMaskedWord I).toNat < EVM.addressModulus := by
  unfold clipperFileAddressDataMaskedWord
  rw [u256_land_comm solcAddrMask (clipperFileAddressDataWord I)]
  exact solcAddrMask_result_canonical (clipperFileAddressDataWord I)

theorem clipperFileAddressData_value_masked (I : ExecutionEnv) :
    (.address (clipperFileAddressData I) : Value) =
      .address (AccountAddress.ofNat (clipperFileAddressDataMaskedWord I).toNat) := by
  simpa [clipperFileAddressData, clipperFileAddressDataMaskedWord,
    clipperFileAddressDataWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

theorem clipperDecode_fileAddress_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata =
        some (clipperFileAddressLocals I) := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr,
    clipperFileAddressLocals, clipperFileAddressWhat, clipperFileAddressData, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem clipperDecode_fileAddress_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata = none := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem clipperFileAddressSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 10)) :
    clipperSelWord I = clipperSelNat 10 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 (clipperSelNat 10)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_fileAddress (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 10)) :
    dispatchMsg (contract v) I.calldata = some fileAddressTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition])
    (post :=
      [getStatusTransition, ilkTransition v, kickTransition v, kicksTransition, listTransition,
        redoTransition v, relyTransition, salesTransition, spotterTransition, stoppedTransition,
        tailTransition, takeTransition v, tipTransition, upchostTransition v, vatTransition v,
        vowTransition, wardsTransition, yankTransition v])
    (ti := fileAddressTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
theorem clipperReachFileAddressBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 10)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1365⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperFileAddressSelectorWord hsz hsel
  have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
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
    (by native_decide)
    (by simp)
  have h54 := clipperSplitNotTaken (pc := (⟨43⟩ : UInt256))
    (next := (⟨54⟩ : UInt256)) (pivot := clipperSelNat 3)
    (tgt := (⟨162⟩ : UInt256)) h43
    (by change decode code (⟨43⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨43⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 3, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨43⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨43⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨162⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨43⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h65 := clipperSplitNotTaken (pc := (⟨54⟩ : UInt256))
    (next := (⟨65⟩ : UInt256)) (pivot := clipperSelNat 12)
    (tgt := (⟨113⟩ : UInt256)) h54
    (by change decode code (⟨54⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨54⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 12, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨54⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨54⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨113⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨54⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h76 := clipperArmNotTaken (pc := (⟨65⟩ : UInt256)) (next := (⟨76⟩ : UInt256))
    (sel := clipperSelNat 12) (tgt := (⟨1349⟩ : UInt256)) h65
    (by change decode code (⟨65⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨65⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 12, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨65⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨65⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1349⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨65⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h87 := clipperArmNotTaken (pc := (⟨76⟩ : UInt256)) (next := (⟨87⟩ : UInt256))
    (sel := clipperSelNat 14) (tgt := (⟨1357⟩ : UInt256)) h76
    (by change decode code (⟨76⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨76⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 14, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨76⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨76⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1357⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨76⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h1365 := clipperArmTaken (pc := (⟨87⟩ : UInt256)) (sel := clipperSelNat 10)
    (tgt := (⟨1365⟩ : UInt256)) h87
    (by change decode code (⟨87⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨87⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 10, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨87⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨87⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1365⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨87⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1365⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1365⟩

theorem clipperFileAddressLocals_get_what (I : ExecutionEnv) :
    (clipperFileAddressLocals I).get? "what" =
      some (.fixedBytes bytes32Width (clipperFileAddressWhat I)) := by
  rw [clipperFileAddressLocals, store_get_ne _ _ (by decide), store_get_self]

theorem clipperFileAddressLocals_get_data (I : ExecutionEnv) :
    (clipperFileAddressLocals I).get? "data" =
      some (.address (clipperFileAddressData I)) := by
  rw [clipperFileAddressLocals, store_get_self]

theorem clipperFileAddressLocals_get_base_none (I : ExecutionEnv)
    {name : Ident} (hwhat : name ≠ "what") (hdata : name ≠ "data") :
    (clipperFileAddressLocals I).get? name = none := by
  have hdataBeq : ("data" == name) = false := by
    exact beq_eq_false_iff_ne.mpr (by intro h; exact hdata h.symm)
  have hwhatBeq : ("what" == name) = false := by
    exact beq_eq_false_iff_ne.mpr (by intro h; exact hwhat h.symm)
  unfold clipperFileAddressLocals
  rw [store_get_ne _ _ hdataBeq, store_get_ne _ _ hwhatBeq]
  simp

theorem evalExpr_clipperFileAddress_data {v : ClipperImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.address (clipperFileAddressData I))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "data") =
      .ok (.address (clipperFileAddressData I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.address (clipperFileAddressData I))
  rw [h]
  rfl

theorem evalExpr_clipperFileAddress_what_eq_true {v : ClipperImmutables}
    {evm : EVM.State} {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (clipperFileAddressWhat I)))
    (hwhat : clipperFileAddressWhat I = bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (clipperFileAddressWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (clipperFileAddressWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_clipperFileAddress_what_eq_false {v : ClipperImmutables}
    {evm : EVM.State} {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (clipperFileAddressWhat I)))
    (hwhat : clipperFileAddressWhat I ≠ bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (clipperFileAddressWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (clipperFileAddressWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_clipperFileAddress_auth (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileAddressLocals I }
      evm (wardsRef sender) = .ok (clipperRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue,
    clipperRelyAuthEvaledRef, clipperRelyAuthKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_clipperFileAddress_auth_true (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
        evm (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileAddressLocals I })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by
        exact clipperFileAddressLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileAddress_auth v evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using clipperStorageLocLoad_uint256 evm
          (clipperRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_clipperFileAddress_auth_false (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
        evm (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileAddressLocals I })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (hbase := by
        exact clipperFileAddressLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileAddress_auth v evm I hsrc)
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

theorem evalStorageRef_clipperFileAddress_locked (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperFileAddressLocals I }
      evm lockedRef = .ok { base := "locked", steps := [] } := by
  simp [lockedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalExpr_clipperFileAddress_locked_zero_true (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I } evm
      (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
        evm (.storage lockedRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileAddressLocals I })
      (slot := lockedRef)
      (er := { base := "locked", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨13⟩)
      (value := .int 0)
      (hbase := by
        exact clipperFileAddressLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileAddress_locked v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using clipperStorageLocLoad_uint256 evm ⟨13⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_clipperFileAddress_locked_zero_false (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I } evm
      (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
        evm (.storage lockedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperFileAddressLocals I })
      (slot := lockedRef)
      (er := { base := "locked", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨13⟩)
      (hbase := by
        exact clipperFileAddressLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileAddress_locked v evm I)
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

theorem assign_clipperFileAddress_locked (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (value : UInt256) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
      evm .storage lockedRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract v, locals := clipperFileAddressLocals I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ value) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨13⟩)
      (hbase := by
        exact clipperFileAddressLocals_get_base_none I (by native_decide) (by native_decide))
      (her := evalStorageRef_clipperFileAddress_locked v evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨13⟩ value

theorem assign_clipperFileAddress_spotter (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        (clipperFileAddressDataMaskedWord I))
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
      evm .storage spotterRef (.address (clipperFileAddressData I)) =
        .ok ({ contract := contract v, locals := clipperFileAddressLocals I }, evm') := by
  intro evm'
  rw [clipperFileAddressData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "spotter", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨3⟩)
      (hbase := clipperFileAddressLocals_get_base_none I
        (by native_decide) (by native_decide))
      (her := by simp [spotterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure,
        bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [addrLoc, evm'] using
    storageLocStore_address_offset0 evm ⟨3⟩ (clipperFileAddressDataMaskedWord I)
      (clipperFileAddressDataMaskedWord_canonical I)

theorem assign_clipperFileAddress_dog (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
        (clipperFileAddressDataMaskedWord I))
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
      evm .storage dogRef (.address (clipperFileAddressData I)) =
        .ok ({ contract := contract v, locals := clipperFileAddressLocals I }, evm') := by
  intro evm'
  rw [clipperFileAddressData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "dog", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨1⟩)
      (hbase := clipperFileAddressLocals_get_base_none I
        (by native_decide) (by native_decide))
      (her := by simp [dogRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [addrLoc, evm'] using
    storageLocStore_address_offset0 evm ⟨1⟩ (clipperFileAddressDataMaskedWord I)
      (clipperFileAddressDataMaskedWord_canonical I)

theorem assign_clipperFileAddress_vow (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
        (clipperFileAddressDataMaskedWord I))
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
      evm .storage vowRef (.address (clipperFileAddressData I)) =
        .ok ({ contract := contract v, locals := clipperFileAddressLocals I }, evm') := by
  intro evm'
  rw [clipperFileAddressData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨2⟩)
      (hbase := clipperFileAddressLocals_get_base_none I
        (by native_decide) (by native_decide))
      (her := by simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [addrLoc, evm'] using
    storageLocStore_address_offset0 evm ⟨2⟩ (clipperFileAddressDataMaskedWord I)
      (clipperFileAddressDataMaskedWord_canonical I)

theorem assign_clipperFileAddress_calc (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        (clipperFileAddressDataMaskedWord I))
    assignStorageRef? (config v) { contract := contract v, locals := clipperFileAddressLocals I }
      evm .storage calcRef (.address (clipperFileAddressData I)) =
        .ok ({ contract := contract v, locals := clipperFileAddressLocals I }, evm') := by
  intro evm'
  rw [clipperFileAddressData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "calc", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨4⟩)
      (hbase := clipperFileAddressLocals_get_base_none I
        (by native_decide) (by native_decide))
      (her := by simp [calcRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [addrLoc, evm'] using
    storageLocStore_address_offset0 evm ⟨4⟩ (clipperFileAddressDataMaskedWord I)
      (clipperFileAddressDataMaskedWord_canonical I)

end Benchmarks.Dss.Clipper

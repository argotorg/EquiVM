import Benchmarks.Dss.Clipper.Arithmetic
import Benchmarks.Dss.Clipper.GetStatusEVMReverts
import Benchmarks.Dss.Clipper.GetStatusReverts
import Benchmarks.Dss.Clipper.Guards
import Benchmarks.Dss.Clipper.Sales

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## ABI decode and dispatch prerequisites for `redo(uint256,address)` -/

theorem clipperRedoSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 16)) :
    clipperSelWord I = clipperSelNat 16 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xd8 0x43 0x41 0x6d (clipperSelNat 16)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

abbrev clipperRedoIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperRedoKprWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev clipperRedoKprMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (clipperRedoKprWord I)

abbrev clipperRedoIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperRedoIdWord I).toNat)

abbrev clipperRedoKprValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (clipperRedoKprWord I).toNat)

abbrev clipperRedoIdKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (clipperRedoIdWord I).toNat)

abbrev clipperRedoStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "id" (clipperRedoIdValue I)).insert "kpr" (clipperRedoKprValue I)

def clipperRedoLockedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩

abbrev clipperRedoSalesBaseSlot (I : ExecutionEnv) : UInt256 :=
  salesBase (clipperRedoIdKey I)

theorem clipperRedoSalesBaseSlot_eq (I : ExecutionEnv) :
    clipperRedoSalesBaseSlot I = solcMappingSlot ⟨12⟩ (clipperRedoIdWord I) := by
  unfold clipperRedoSalesBaseSlot salesBase mapSlot solcMappingSlot clipperRedoIdKey
  rw [keyValueToWord_uint256]

abbrev clipperRedoSalesPackedSlot (I : ExecutionEnv) : UInt256 :=
  clipperRedoSalesBaseSlot I + ⟨3⟩

abbrev clipperRedoSalesTopSlot (I : ExecutionEnv) : UInt256 :=
  clipperRedoSalesBaseSlot I + ⟨4⟩

abbrev clipperRedoSalesUsrWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I (clipperRedoSalesPackedSlot I)) solcAddrMask

abbrev clipperRedoSalesTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div (solcSlotWord σ I (clipperRedoSalesPackedSlot I))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)

abbrev clipperRedoSalesTopWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperRedoSalesTopSlot I)

abbrev clipperRedoSalesUsrRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperRedoIdKey I), .field "usr"] }

abbrev clipperRedoSalesTicRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperRedoIdKey I), .field "tic"] }

abbrev clipperRedoSalesTopRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperRedoIdKey I), .field "top"] }

abbrev clipperRedoSalesUsrEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperRedoSalesPackedSlot I))
    solcAddrMask

abbrev clipperRedoSalesTicEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperRedoSalesPackedSlot I))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)

abbrev clipperRedoSalesTopEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperRedoSalesTopSlot I)

abbrev clipperRedoLocalsUsr (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperRedoStore I).insert "usr"
    (.address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evm I).toNat))

abbrev clipperRedoLocalsTic (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperRedoLocalsUsr evm I).insert "tic"
    (.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat))

abbrev clipperRedoLocalsTop (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperRedoLocalsTic evm I).insert "top"
    (.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat))

noncomputable abbrev clipperRedoSalesHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperRedoIdWord I) ⟨12⟩ solcFreePtrMem

theorem clipperRedoSalesHashMem_size (I : ExecutionEnv) :
    (clipperRedoSalesHashMem I).size = 96 := by
  simpa [clipperRedoSalesHashMem] using
    twoWordHashMem_size_96 (clipperRedoIdWord I) (⟨12⟩ : UInt256) solcFreePtrMem_size

theorem clipperRedoSalesHashMem_read64 (I : ExecutionEnv) :
    (clipperRedoSalesHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [clipperRedoSalesHashMem, twoWordHashMem_read64 _ _ solcFreePtrMem_size]
  exact solcFreePtrMem_read64

theorem clipperDispatch_redo (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 16)) :
    dispatchMsg (contract v) I.calldata = some (redoTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition])
    (post :=
      [relyTransition, salesTransition, spotterTransition, stoppedTransition, tailTransition,
        takeTransition v, tipTransition, upchostTransition v, vatTransition v, vowTransition,
        wardsTransition, yankTransition v])
    (ti := redoTransition v) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, ilkSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, redoSelectorBytes v]
    simpa [clipperSelBytes] using hsel

-- LIBRARY CANDIDATE: legacy-solc05 two-word scalar decoding for `(uint256,address)`.
theorem decodeCalldata_legacyUint256_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [x, y] [uint256, addr] cd =
      some (((∅ : Solm.Store).insert x
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 36 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_solcV1SignedScalarWords_eq (names := [x, y])
    (types := [uint256, addr]) (cd := cd) (by native_decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have hdecode0 :
      decodeScalarWordWithMode? DecodeMode.solcV1Signed uint256 (cd.toList.drop 4) 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
          0 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
        (bytes := cd.toList.drop 4) (start := 0) htake4
  have hdecode32 :
      decodeScalarWordWithMode? DecodeMode.solcV1Signed addr (cd.toList.drop 4) 32 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [addr] using
      decodeScalarWord_solcV1SignedAddress_ok (bytes := cd.toList.drop 4) (start := 32) htake36
  rw [hdecode0, hdecode32]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [x, y]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 36).toNat)))
  rw [hword4, hword36]
  simp [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: legacy-solc05 short calldata failure for `(uint256,address)`.
theorem decodeCalldata_legacyUint256_address_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [x, y] [uint256, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_solcV1SignedScalarWords_eq (names := [x, y])
    (types := [uint256, addr]) (cd := cd) (by native_decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.solcV1Signed uint256 (cd.toList.drop 4) 0 =
          some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
            0 + 32) := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
          (bytes := cd.toList.drop 4) (start := 0) htake0
    rw [hdecode0]
    have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    have hdecode32 :
        decodeScalarWordWithMode? DecodeMode.solcV1Signed addr (cd.toList.drop 4) 32 =
          none := by
      simpa [addr] using
        decodeScalarWord_solcV1SignedAddress_none_short (bytes := cd.toList.drop 4) (start := 32)
          htake32n
    rw [hdecode32]
    simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.solcV1Signed uint256 (cd.toList.drop 4) 0 =
          none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.solcV1Signed)
          (bytes := cd.toList.drop 4) (start := 0) htake0n
    rw [hdecode0]
    simp only [Option.bind, bind]

theorem clipperDecode_redo_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((redoTransition v).params.map Param.name)
      (transitionSignature (redoTransition v)).paramTypes I.calldata =
        some (clipperRedoStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["id", "kpr"]
    [uint256, addr] I.calldata = _
  simpa [config, clipperRedoStore, clipperRedoIdValue, clipperRedoKprValue,
    clipperRedoIdWord, clipperRedoKprWord] using
    decodeCalldata_legacyUint256_address_ok
      (cd := I.calldata) (x := "id") (y := "kpr") hsz68

theorem clipperDecode_redo_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode ((redoTransition v).params.map Param.name)
      (transitionSignature (redoTransition v)).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["id", "kpr"]
    [uint256, addr] I.calldata = none
  simpa [config] using
    decodeCalldata_legacyUint256_address_none_short
      (cd := I.calldata) (x := "id") (y := "kpr") hsz4 hshort

set_option maxHeartbeats 1000000 in
theorem clipperReachRedoBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 16)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1409⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperRedoSelectorWord hsz hsel
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
  have h76 := clipperArmNotTaken (pc := (⟨65⟩ : UInt256))
    (next := (⟨76⟩ : UInt256)) (sel := clipperSelNat 12)
    (tgt := (⟨1349⟩ : UInt256)) h65
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
  have h87 := clipperArmNotTaken (pc := (⟨76⟩ : UInt256))
    (next := (⟨87⟩ : UInt256)) (sel := clipperSelNat 14)
    (tgt := (⟨1357⟩ : UInt256)) h76
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
  have h98 := clipperArmNotTaken (pc := (⟨87⟩ : UInt256))
    (next := (⟨98⟩ : UInt256)) (sel := clipperSelNat 10)
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
    (by native_decide)
    (by simp)
  have h1409 := clipperArmTaken (pc := (⟨98⟩ : UInt256)) (sel := clipperSelNat 16)
    (tgt := (⟨1409⟩ : UInt256)) h98
    (by change decode code (⟨98⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨98⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 16, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨98⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨98⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1409⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨98⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1409⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1409⟩

theorem clipperRedoDecodedJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1431⟩ : UInt256) = true := by
  exact clipperJumpDestBeforeFirstPatch v hpatch (⟨1431⟩ : UInt256) (by native_decide)

theorem clipperJumpDest7261 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7261⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 8000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest7338 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7338⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 8000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest7428 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7428⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 8000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest7563 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7563⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 8000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperRedoPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 1431 ≤ lo) (hhi : hi ≤ 1453) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  have _ : 1431 ≤ lo := hlo
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      try omega
  | some bs =>
      simp [hIlk]
      try omega

theorem clipperRedoDecodeArgs (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 1431 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 1453)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperRedoPatchesWindowDisjoint32 v pc.toNat (pc.toNat + 1) hlo (by omega))
    (clipperRedoPatchesWindowDisjoint32 v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega) hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      omega)
    (by exact Nat.lt_of_le_of_lt hhi (by native_decide))

set_option maxHeartbeats 1000000 in
theorem clipperRedoX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1409⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨7261⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := (⟨1409⟩ : UInt256))
    (ret := (⟨502⟩ : UInt256)) (decoded := (⟨1431⟩ : UInt256)) hreach
    (by change decode code (⟨1409⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code (⟨1410⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨1413⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨1415⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨1416⟩ : UInt256) = some (.CALLDATASIZE, .none); clipper_decode)
    (by change decode code (⟨1417⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨1418⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨64⟩, 1))
      clipper_decode)
    (by change decode code (⟨1420⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨1421⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨1422⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨1423⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨1431⟩, 2))
      clipper_decode)
    (by change decode code (⟨1426⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (clipperRedoDecodedJumpDest v hpatch) hsz68 hsize
  have hdec1431 :
      decode code (⟨1431⟩ : UInt256) = some (.JUMPDEST, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1432 : decode code (⟨1432⟩ : UInt256) = some (.POP, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1433 : decode code (⟨1433⟩ : UInt256) = some (.DUP1, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1434 : decode code (⟨1434⟩ : UInt256) = some (.CALLDATALOAD, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1435 : decode code (⟨1435⟩ : UInt256) = some (.SWAP1, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1436 :
      decode code (⟨1436⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1438 : decode code (⟨1438⟩ : UInt256) = some (.ADD, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1439 : decode code (⟨1439⟩ : UInt256) = some (.CALLDATALOAD, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1440 :
      decode code (⟨1440⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1442 :
      decode code (⟨1442⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1444 :
      decode code (⟨1444⟩ : UInt256) = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1446 : decode code (⟨1446⟩ : UInt256) = some (.SHL, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1447 : decode code (⟨1447⟩ : UInt256) = some (.SUB, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1448 : decode code (⟨1448⟩ : UInt256) = some (.AND, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1449 :
      decode code (⟨1449⟩ : UInt256) = some (.Push .PUSH2, some (⟨7261⟩, 2)) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have hdec1452 : decode code (⟨1452⟩ : UInt256) = some (.JUMP, .none) := by
    exact clipperRedoDecodeArgs v hpatch (by native_decide) (by native_decide)
      (by native_decide)
  have rd1432 := hdecoded.jumpdest
    hdec1431
    (by evm_ov)
  have rd1433 := rd1432.pop
    hdec1432
    (by evm_ov)
  have rd1434 := rd1433.dup1
    hdec1433
    (by evm_ov)
  have rd1435 := rd1434.calldataload
    hdec1434
    (by evm_ov)
  have rd1436 := rd1435.swap1
    hdec1435
    (by evm_ov)
  have rd1438 := rd1436.push1 ⟨32⟩
    hdec1436
    (by evm_ov)
  have rd1439 := rd1438.add
    hdec1438
    (by evm_ov)
  have rd1440 := rd1439.calldataload
    hdec1439
    (by evm_ov)
  have rd1442 := rd1440.push1 ⟨1⟩
    hdec1440
    (by evm_ov)
  have rd1444 := rd1442.push1 ⟨1⟩
    hdec1442
    (by evm_ov)
  have rd1446 := rd1444.push1 ⟨160⟩
    hdec1444
    (by evm_ov)
  have rd1447 := rd1446.shl
    hdec1446
    (by evm_ov)
  have rd1448 := rd1447.sub
    hdec1447
    (by evm_ov)
  have rd1449 := rd1448.and
    hdec1448
    (by evm_ov)
  have rd1452 := rd1449.push2 (⟨7261⟩ : UInt256)
    hdec1449
    (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperRedoKprMaskedWord, clipperRedoKprWord, clipperRedoIdWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd1452.jump
        hdec1452 (clipperJumpDest7261 v hpatch) (by evm_ov)⟩

theorem clipperRedoLockedSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  intro locals evm0
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_clipperLocked_zero_false v evm0 locals (by simp [locals]) hlocked
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (redoTransition v).body .reverted := by
    simpa [redoTransition, nonpayable, lockPrefix] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        exact ExecBlock.consRevert (ExecStmt.requireFalse hlockedEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem evalStorageRef_clipperRedoStopped (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) :
    evalStorageRef (config v) { contract := contract v, locals := locals } evm
      stoppedRef = .ok { base := "stopped", steps := [] } := by
  simp [stoppedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalExpr_clipperRedoStopped_lt_two_false (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "stopped" = none)
    (hload : 2 ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage stoppedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := stoppedRef)
      (er := { base := "stopped", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨14⟩)
      (hbase := hbase)
      (her := evalStorageRef_clipperRedoStopped v evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa using clipperStorageLocLoad_uint256 evm ⟨14⟩)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.lt
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat))
      (Value.int 2) = .ok (.bool false)
  simp [evalBinaryOp?]
  omega

theorem evalExpr_clipperRedoStopped_lt_two_true (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "stopped" = none)
    (hload : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat < 2) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage stoppedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := stoppedRef)
      (er := { base := "stopped", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨14⟩)
      (hbase := hbase)
      (her := evalStorageRef_clipperRedoStopped v evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa using clipperStorageLocLoad_uint256 evm ⟨14⟩)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.lt
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat))
      (Value.int 2) = .ok (.bool true)
  simp [evalBinaryOp?]
  omega

theorem clipperEvalRedoVarId (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := clipperRedoStore I } evm
      (.var "id") = .ok (clipperRedoIdValue I) := by
  simp only [evalExpr?, clipperRedoStore]
  rw [store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoSalesUsr (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoStore I } evm
      (.storage (salesF (.var "id") "usr")) =
      .ok (.address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperRedoStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "usr") (er := clipperRedoSalesUsrRef I)
    (t := .address) (loc := addrLoc (clipperRedoSalesPackedSlot I))
    (value := .address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evm I).toNat))
    (by simp [frame, salesF, clipperRedoStore])
    (by
      simp only [frame, clipperRedoSalesUsrRef, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, pure, bind]
      rw [clipperEvalRedoVarId v evm I]
      simp [clipperRedoIdKey, valueToKey?, EvalResult.ofOption, pure])
    (by simp [frame, clipperRedoIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, addrSt])
    (by rfl)
    (by simpa [clipperRedoSalesUsrEVMWord, clipperRedoSalesPackedSlot,
      clipperRedoSalesBaseSlot] using
      clipperStorageLocLoad_address evm (clipperRedoSalesPackedSlot I))

theorem clipperEvalRedoVarIdAfterUsr (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsUsr evmLoc I }
      evmRead (.var "id") = .ok (clipperRedoIdValue I) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsUsr, store_get_ne _ _ (by decide),
    clipperRedoStore, store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoSalesTicAfterUsr (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsUsr evm I } evm
      (.storage (salesF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperRedoLocalsUsr evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "tic") (er := clipperRedoSalesTicRef I)
    (t := .int uint96Int)
    (loc := uint96Loc (clipperRedoSalesPackedSlot I) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat))
    (by simp [frame, salesF, clipperRedoLocalsUsr, clipperRedoStore])
    (by
      simp [frame, clipperRedoSalesTicRef, clipperRedoIdValue, clipperRedoIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalRedoVarIdAfterUsr v evm evm I, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperRedoIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint96St])
    (by rfl)
    (by simpa [clipperRedoSalesTicEVMWord, clipperRedoSalesPackedSlot,
      clipperRedoSalesBaseSlot] using
      clipperStorageLocLoad_uint96 evm (clipperRedoSalesPackedSlot I))

theorem clipperEvalRedoVarIdAfterTic (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTic evm I } evm
      (.var "id") = .ok (clipperRedoIdValue I) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsTic, store_get_ne _ _ (by decide),
    clipperRedoLocalsUsr, store_get_ne _ _ (by decide),
    clipperRedoStore, store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoSalesTopAfterTic (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTic evm I } evm
      (.storage (salesF (.var "id") "top")) =
      .ok (.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperRedoLocalsTic evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "top") (er := clipperRedoSalesTopRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperRedoSalesTopSlot I))
    (value := .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat))
    (by simp [frame, salesF, clipperRedoLocalsTic, clipperRedoLocalsUsr,
      clipperRedoStore])
    (by
      simp [frame, clipperRedoSalesTopRef, clipperRedoIdValue, clipperRedoIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalRedoVarIdAfterTic v evm I, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperRedoIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperRedoSalesTopEVMWord, clipperRedoSalesTopSlot,
      clipperRedoSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperRedoSalesTopSlot I))

theorem clipperEvalRedoZeroAddr (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    pure, bind]

theorem clipperEvalRedoVarUsrAfterTop (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.var "usr") =
      .ok (.address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evm I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsTop, store_get_ne _ _ (by decide),
    clipperRedoLocalsTic, store_get_ne _ _ (by decide),
    clipperRedoLocalsUsr, store_get_self]
  rfl

theorem clipperEvalRedoUsrNeZeroAfterTop_false (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (husr : clipperRedoSalesUsrEVMWord evm I = ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.binary .ne (.var "usr") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, clipperEvalRedoVarUsrAfterTop, clipperEvalRedoZeroAddr,
    EvalResult.bind, bind]
  rw [husr]
  native_decide

theorem clipperRedoMaskedAddress_ne_zero {w : UInt256}
    (h : UInt256.land w solcAddrMask ≠ ⟨0⟩) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  have hval : (UInt256.land w solcAddrMask).toNat = 0 := by
    have hlt : (UInt256.land w solcAddrMask).toNat < AccountAddress.size := by
      rw [u256_land_toNat]
      have hland : Nat.land w.toNat solcAddrMask.toNat ≤ solcAddrMask.toNat :=
        Nat.and_le_right
      have hmask : solcAddrMask.toNat < AccountAddress.size := by
        native_decide
      have hlandlt : Nat.land w.toNat solcAddrMask.toNat < UInt256.size := by
        have hsize : AccountAddress.size < UInt256.size := by decide
        omega
      rw [Nat.mod_eq_of_lt hlandlt]
      omega
    apply congrArg Fin.val at haddr
    simpa [AccountAddress.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hlt] using haddr
  exact h (u256_inj (by simpa using hval))

theorem clipperEvalRedoUsrNeZeroAfterTop_true (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (husr : clipperRedoSalesUsrEVMWord evm I ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.binary .ne (.var "usr") zeroAddr) = .ok (.bool true) := by
  simp only [evalExpr?, clipperEvalRedoVarUsrAfterTop, clipperEvalRedoZeroAddr,
    EvalResult.bind, bind]
  have haddr : AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evm I).toNat ≠
      AccountAddress.ofNat 0 := by
    simpa [clipperRedoSalesUsrEVMWord] using
      clipperRedoMaskedAddress_ne_zero
        (w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperRedoSalesPackedSlot I))
        (by simpa [clipperRedoSalesUsrEVMWord] using husr)
  simp [evalBinaryOp?, haddr]

theorem clipperEvalRedoVarTicAfterTop (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.var "tic") = .ok (.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsTop, store_get_ne _ _ (by decide),
    clipperRedoLocalsTic, store_get_self]
  rfl

theorem clipperEvalRedoVarTopAfterTop (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.var "top") = .ok (.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsTop, store_get_self]
  rfl

theorem clipperEvalRedoStatusArgs (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      [.var "tic", .var "top"] =
      .ok [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
        .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)] := by
  simp only [evalExprs?, clipperEvalRedoVarTicAfterTop, clipperEvalRedoVarTopAfterTop,
    EvalResult.bind, bind, pure]

theorem clipperRedoStatusCallRevertsAgeForPrice (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (clipperTimestampWord evm).toNat < (clipperRedoSalesTicEVMWord evm I).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .var "top"])
    (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperEvalRedoStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsAgeForPrice v evm
      (clipperRedoSalesTicEVMWord evm I) (clipperRedoSalesTopEVMWord evm I) hlt)

theorem clipperRedoInactiveSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I = ⟨0⟩) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  intro locals evm0
  let evmLock := clipperRedoLockedState evm0
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperRedoLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTic evmLock I }
  let topFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock, clipperRedoLockedState] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool true) := by
    apply evalExpr_clipperRedoStopped_lt_two_true
    · simp [locals]
    · simpa [evmLock, clipperRedoLockedState, evm0, initState, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
        storageStore_executionEnv] using hstopped
  have husrLoad : clipperRedoSalesUsrEVMWord evmLock I = ⟨0⟩ := by
    simpa [clipperRedoSalesUsrEVMWord, clipperRedoSalesUsrWord, evmLock,
      clipperRedoLockedState, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperRedoLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalRedoSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperRedoLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperRedoSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalRedoSalesTicAfterUsr v evmLock I))
  have hletTop :
      ExecStmt (config v) ticFrame evmLock
        (.letDecl "top" (some uint256) (.storage (salesF (.var "id") "top")))
        (.ok topFrame evmLock) := by
    simpa [ticFrame, topFrame, clipperRedoLocalsTop] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := ticFrame) (evm := evmLock) (name := "top")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "top"))
        (value := .int (Int.ofNat (clipperRedoSalesTopEVMWord evmLock I).toNat))
        (by simpa [ticFrame] using clipperEvalRedoSalesTopAfterTic v evmLock I))
  have husrEval :
      evalExpr? (config v) topFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool false) := by
    simpa [topFrame] using clipperEvalRedoUsrNeZeroAfterTop_false v evmLock I husrLoad
  have hblock :
      ExecBlock (config v) startFrame evm0 (redoTransition v).body .reverted := by
    simpa [redoTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal hletTop ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse husrEval))
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperRedoStatusAgeForPriceSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hlt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (clipperRedoSalesTicWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I).toNat) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  intro locals evm0
  let evmLock := clipperRedoLockedState evm0
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperRedoLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTic evmLock I }
  let topFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock, clipperRedoLockedState] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool true) := by
    apply evalExpr_clipperRedoStopped_lt_two_true
    · simp [locals]
    · simpa [evmLock, clipperRedoLockedState, evm0, initState, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
        storageStore_executionEnv] using hstopped
  have husrLoad : clipperRedoSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperRedoSalesUsrEVMWord, clipperRedoSalesUsrWord, evmLock,
      clipperRedoLockedState, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using husr
  have hltLoad :
      (clipperTimestampWord evmLock).toNat < (clipperRedoSalesTicEVMWord evmLock I).toNat := by
    simpa [clipperTimestampWord, clipperRedoSalesTicEVMWord, clipperRedoSalesTicWord,
      evmLock, clipperRedoLockedState, evm0, initState, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
      storageStore_executionEnv] using hlt
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperRedoLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalRedoSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperRedoLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperRedoSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalRedoSalesTicAfterUsr v evmLock I))
  have hletTop :
      ExecStmt (config v) ticFrame evmLock
        (.letDecl "top" (some uint256) (.storage (salesF (.var "id") "top")))
        (.ok topFrame evmLock) := by
    simpa [ticFrame, topFrame, clipperRedoLocalsTop] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := ticFrame) (evm := evmLock) (name := "top")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "top"))
        (value := .int (Int.ofNat (clipperRedoSalesTopEVMWord evmLock I).toNat))
        (by simpa [ticFrame] using clipperEvalRedoSalesTopAfterTic v evmLock I))
  have husrEval :
      evalExpr? (config v) topFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [topFrame] using clipperEvalRedoUsrNeZeroAfterTop_true v evmLock I husrLoad
  have hstatus :
      ExecStmt (config v) topFrame evmLock
        (.internalCall "status" [.var "tic", .var "top"] "st") .reverted := by
    simpa [topFrame] using clipperRedoStatusCallRevertsAgeForPrice v evmLock I hltLoad
  have hblock :
      ExecBlock (config v) startFrame evm0 (redoTransition v).body .reverted := by
    simpa [redoTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal hletTop ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        exact ExecBlock.consRevert hstatus)
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperRedoStoppedSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      2 ≤ (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  intro locals evm0
  let evmLock := clipperRedoLockedState evm0
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock, clipperRedoLockedState] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool false) := by
    apply evalExpr_clipperRedoStopped_lt_two_false
    · simp [locals]
    · simpa [evmLock, clipperRedoLockedState, evm0, initState, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
        storageStore_executionEnv] using hstopped
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (redoTransition v).body .reverted := by
    simpa [redoTransition, nonpayable, lockPrefix, isStopped] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse hstoppedEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperRedoLockRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨7270⟩ : UInt256) ⟨21⟩
      ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ .PUSH21 21 := by
  unfold solcErrorStringRevertTailWf
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> (norm_num1; clipper_runtime_decode)

theorem clipperRedoStoppedRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨7356⟩ : UInt256) ⟨25⟩
      ⟨105806016908988270734738552397420409440386134862091135834333⟩ ⟨58⟩ .PUSH25
      25 := by
  unfold solcErrorStringRevertTailWf
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> (norm_num1; clipper_runtime_decode)

set_option maxHeartbeats 1000000 in
theorem clipperRedoX_locked {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩)
    (h : RD code I g s0 (⟨7261⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd7264pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k7265, C7265, rd7265raw⟩ := rd7264pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7265 : RD code I g s0 (⟨7265⟩ : UInt256)
      (solcSlotWord σ I ⟨13⟩ :: clipperRedoKprMaskedWord I ::
        clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k7265 C7265 := by
    simpa [solcSlotWord] using rd7265raw
  have rd7266pre := rd7265.iszero (by clipper_runtime_decode) (by evm_ov)
  rw [isZero_eq_zero_of_ne hlocked] at rd7266pre
  have rd7269 := rd7266pre.pushConst (⟨7338⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd7270 := rd7269.jumpiNT (by clipper_runtime_decode)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (word := (⟨30496508052792062404420069455133111715513420844312188351800969105462834233344⟩ :
      UInt256))
    rd7270
    (clipperRedoLockRevertTailWf v hpatch)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp)

set_option maxHeartbeats 1000000 in
theorem clipperRedoX_lockOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (h : RD code I g s0 (⟨7261⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 (⟨7338⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7264pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k7265, C7265, rd7265raw⟩ := rd7264pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7265 : RD code I g s0 (⟨7265⟩ : UInt256)
      (solcSlotWord σ I ⟨13⟩ :: clipperRedoKprMaskedWord I ::
        clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k7265 C7265 := by
    simpa [solcSlotWord] using rd7265raw
  have rd7266 := rd7265.iszero (by clipper_runtime_decode) (by evm_ov)
  have hcond : UInt256.isZero (solcSlotWord σ I ⟨13⟩) ≠ ⟨0⟩ := by
    rw [hlocked]
    native_decide
  have rd7269 := rd7266.pushConst (⟨7338⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd7269.jumpiT (by clipper_runtime_decode) hcond
    (clipperJumpDest7338 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperRedoX_lockStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 (⟨7338⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 (⟨7344⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) k' C' := by
  have rd7343pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd7344raw⟩ := rd7343pre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd7344raw⟩

set_option maxHeartbeats 1000000 in
theorem clipperRedoX_stoppedClosed {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hstopped : 2 ≤ (solcSlotWord σ I ⟨14⟩).toNat)
    (h : RD code I g s0 (⟨7344⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd7346pre := h.pushConst (⟨14⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨k7347, C7347, rd7347raw⟩ := rd7346pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7347 : RD code I g s0 (⟨7347⟩ : UInt256)
      (solcSlotWord σ I ⟨14⟩ :: clipperRedoKprMaskedWord I ::
        clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k7347 C7347 := by
    simpa [solcSlotWord] using rd7347raw
  have rd7349 := rd7347.pushConst (⟨2⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd7350 := rd7349.swap1 (by clipper_runtime_decode) (by evm_ov)
  have rd7351 := rd7350.dup2 (by clipper_runtime_decode) (by evm_ov)
  have rd7352 := rd7351.gt (by clipper_runtime_decode) (by evm_ov)
  have hgt : UInt256.gt (⟨2⟩ : UInt256) (solcSlotWord σ I ⟨14⟩) = ⟨0⟩ := by
    exact ugt_zero (by simpa using hstopped)
  rw [hgt] at rd7352
  have rd7355 := rd7352.pushConst (⟨7428⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd7356 := rd7355.jumpiNT (by clipper_runtime_decode)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (word := (⟨30496508052792062404419589047915533211324476653882280781143920003575554506752⟩ :
      UInt256))
    rd7356
    (clipperRedoStoppedRevertTailWf v hpatch)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp)

set_option maxHeartbeats 1000000 in
theorem clipperRedoX_stoppedOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hstopped : (solcSlotWord σ I ⟨14⟩).toNat < 2)
    (h : RD code I g s0 (⟨7344⟩ : UInt256)
      [clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 (⟨7428⟩ : UInt256)
      [⟨2⟩, clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7346pre := h.pushConst (⟨14⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨k7347, C7347, rd7347raw⟩ := rd7346pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7347 : RD code I g s0 (⟨7347⟩ : UInt256)
      (solcSlotWord σ I ⟨14⟩ :: clipperRedoKprMaskedWord I ::
        clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k7347 C7347 := by
    simpa [solcSlotWord] using rd7347raw
  have rd7349 := rd7347.pushConst (⟨2⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd7350 := rd7349.swap1 (by clipper_runtime_decode) (by evm_ov)
  have rd7351 := rd7350.dup2 (by clipper_runtime_decode) (by evm_ov)
  have rd7352 := rd7351.gt (by clipper_runtime_decode) (by evm_ov)
  have hgt : UInt256.gt (⟨2⟩ : UInt256) (solcSlotWord σ I ⟨14⟩) = ⟨1⟩ := by
    exact ugt_one (by
      rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
      exact hstopped)
  rw [hgt] at rd7352
  have rd7355 := rd7352.pushConst (⟨7428⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd7355.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (clipperJumpDest7428 v hpatch) (by evm_ov)⟩

abbrev clipperRedoNotRunningAuctionWord : UInt256 :=
  ⟨0x436c69707065722f6e6f742d72756e6e696e672d61756374696f6e0000000000⟩

set_option maxHeartbeats 1000000 in
theorem clipperRedoX_inactiveAuctionTail {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨7487⟩
      [clipperRedoSalesTopWord σ I, clipperRedoSalesTicWord σ I,
        clipperRedoSalesUsrWord σ I, ⟨2⟩, clipperRedoKprMaskedWord I,
        clipperRedoIdWord I, ⟨502⟩, sel]
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_runtime_decode)
      mem_cost
      (mloadFreePtrValue (by rw [clipperRedoSalesHashMem_size I]; decide)
        (by decide) (clipperRedoSalesHashMem_read64 I))
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (clipperRedoSalesHashMem I))
      (UInt256.ofNat 5) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (clipperRedoSalesHashMem I))
      (UInt256.ofNat 6) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ (clipperRedoSalesHashMem I))
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst clipperRedoNotRunningAuctionWord
    (width := 32) (op := .PUSH32) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨27⟩ clipperRedoNotRunningAuctionWord
        (clipperRedoSalesHashMem I))
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ clipperRedoNotRunningAuctionWord
        (clipperRedoSalesHashMem_size I) (clipperRedoSalesHashMem_read64 I))
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem clipperRedoX_usrZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr : clipperRedoSalesUsrWord σ I = ⟨0⟩)
    (h : RD code I g s0 (⟨7428⟩ : UInt256)
      [⟨2⟩, clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  let base : UInt256 := solcMappingSlot ⟨12⟩ (clipperRedoIdWord I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRedoSalesHashMem I).readWithPadding 0 64))) =
        base := by
    simpa [clipperRedoSalesHashMem, base] using
      twoWordHashMem_solcMappingSlot ⟨12⟩ (clipperRedoIdWord I) solcFreePtrMem_size
  have rd7433pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd7434 := rd7433pre.mstore 0
    (wordAt0Mem (clipperRedoIdWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd7438pre := evm_run rd7434 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd7439 := rd7438pre.mstore 0 (clipperRedoSalesHashMem I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd7442pre := evm_run rd7439 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd7443 := rd7442pre.keccak256 0 base
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd7446pre := evm_run rd7443 with [
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have hpackedSlot : base + ⟨3⟩ = clipperRedoSalesPackedSlot I := by
    change base + ⟨3⟩ = clipperRedoSalesBaseSlot I + ⟨3⟩
    rw [clipperRedoSalesBaseSlot_eq I]
  rw [hpackedSlot] at rd7446pre
  obtain ⟨k7448, C7448, rd7448raw⟩ := rd7446pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7448 : RD code I g s0 (⟨7448⟩ : UInt256)
      (solcSlotWord σ I (clipperRedoSalesPackedSlot I) :: base :: ⟨2⟩ ::
        clipperRedoKprMaskedWord I :: clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7448 C7448 := by
    simpa [solcSlotWord] using rd7448raw
  have rd7452pre := evm_run rd7448 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have htopSlot : base + ⟨4⟩ = clipperRedoSalesTopSlot I := by
    change base + ⟨4⟩ = clipperRedoSalesBaseSlot I + ⟨4⟩
    rw [clipperRedoSalesBaseSlot_eq I]
  rw [htopSlot] at rd7452pre
  obtain ⟨k7454, C7454, rd7454raw⟩ := rd7452pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7454 : RD code I g s0 (⟨7454⟩ : UInt256)
      (clipperRedoSalesTopWord σ I :: solcSlotWord σ I (clipperRedoSalesPackedSlot I) ::
        ⟨2⟩ :: clipperRedoKprMaskedWord I :: clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7454 C7454 := by
    simpa [clipperRedoSalesTopWord, solcSlotWord] using rd7454raw
  have rd7464pre := evm_run rd7454 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd7464pre
  have rd7483pre := evm_run rd7464pre with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7563⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩ =
    UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩ from rfl] at rd7483pre
  have husrStack :
      UInt256.land (solcSlotWord σ I (clipperRedoSalesPackedSlot I)) solcAddrMask =
        ⟨0⟩ := by
    simpa [clipperRedoSalesUsrWord, u256_land_comm] using husr
  have rd7487 := rd7483pre.jumpiNT (by clipper_runtime_decode) husrStack (by evm_ov)
  exact clipperRedoX_inactiveAuctionTail (v := v) hpatch (by
    simpa [clipperRedoSalesUsrWord, clipperRedoSalesTicWord, clipperRedoSalesTopWord,
      u256_land_comm] using rd7487)

set_option maxHeartbeats 2000000 in
theorem clipperRedoX_usrNonzero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr : clipperRedoSalesUsrWord σ I ≠ ⟨0⟩)
    (h : RD code I g s0 (⟨7428⟩ : UInt256)
      [⟨2⟩, clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 (⟨7563⟩ : UInt256)
      [clipperRedoSalesTopWord σ I, clipperRedoSalesTicWord σ I,
        clipperRedoSalesUsrWord σ I, ⟨2⟩, clipperRedoKprMaskedWord I,
        clipperRedoIdWord I, ⟨502⟩, sel]
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let base : UInt256 := solcMappingSlot ⟨12⟩ (clipperRedoIdWord I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRedoSalesHashMem I).readWithPadding 0 64))) =
        base := by
    simpa [clipperRedoSalesHashMem, base] using
      twoWordHashMem_solcMappingSlot ⟨12⟩ (clipperRedoIdWord I) solcFreePtrMem_size
  have rd7433pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd7434 := rd7433pre.mstore 0
    (wordAt0Mem (clipperRedoIdWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd7438pre := evm_run rd7434 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd7439 := rd7438pre.mstore 0 (clipperRedoSalesHashMem I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd7442pre := evm_run rd7439 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd7443 := rd7442pre.keccak256 0 base
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd7446pre := evm_run rd7443 with [
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have hpackedSlot : base + ⟨3⟩ = clipperRedoSalesPackedSlot I := by
    change base + ⟨3⟩ = clipperRedoSalesBaseSlot I + ⟨3⟩
    rw [clipperRedoSalesBaseSlot_eq I]
  rw [hpackedSlot] at rd7446pre
  obtain ⟨k7448, C7448, rd7448raw⟩ := rd7446pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7448 : RD code I g s0 (⟨7448⟩ : UInt256)
      (solcSlotWord σ I (clipperRedoSalesPackedSlot I) :: base :: ⟨2⟩ ::
        clipperRedoKprMaskedWord I :: clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7448 C7448 := by
    simpa [solcSlotWord] using rd7448raw
  have rd7452pre := evm_run rd7448 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have htopSlot : base + ⟨4⟩ = clipperRedoSalesTopSlot I := by
    change base + ⟨4⟩ = clipperRedoSalesBaseSlot I + ⟨4⟩
    rw [clipperRedoSalesBaseSlot_eq I]
  rw [htopSlot] at rd7452pre
  obtain ⟨k7454, C7454, rd7454raw⟩ := rd7452pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd7454 : RD code I g s0 (⟨7454⟩ : UInt256)
      (clipperRedoSalesTopWord σ I :: solcSlotWord σ I (clipperRedoSalesPackedSlot I) ::
        ⟨2⟩ :: clipperRedoKprMaskedWord I :: clipperRedoIdWord I :: ⟨502⟩ :: [sel])
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7454 C7454 := by
    simpa [clipperRedoSalesTopWord, solcSlotWord] using rd7454raw
  have rd7464pre := evm_run rd7454 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd7464pre
  have rd7483pre := evm_run rd7464pre with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7563⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩ =
    UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩ from rfl] at rd7483pre
  have husrStack :
      UInt256.land (solcSlotWord σ I (clipperRedoSalesPackedSlot I)) solcAddrMask ≠
        ⟨0⟩ := by
    simpa [clipperRedoSalesUsrWord, u256_land_comm] using husr
  exact ⟨_, _, by
    simpa [clipperRedoSalesUsrWord, clipperRedoSalesTicWord, clipperRedoSalesTopWord,
      u256_land_comm] using
      rd7483pre.jumpiT (by clipper_runtime_decode) husrStack
        (clipperJumpDest7563 v hpatch) (by evm_ov)⟩

theorem clipperRedoX_enterStatus {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 (⟨7563⟩ : UInt256)
      [clipperRedoSalesTopWord σ I, clipperRedoSalesTicWord σ I,
        clipperRedoSalesUsrWord σ I, ⟨2⟩, clipperRedoKprMaskedWord I,
        clipperRedoIdWord I, ⟨502⟩, sel]
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 (⟨8460⟩ : UInt256)
      [clipperRedoSalesTopWord σ I, clipperRedoSalesTicWord σ I, ⟨7575⟩, ⟨0⟩,
        clipperRedoSalesTopWord σ I, clipperRedoSalesTicWord σ I,
        clipperRedoSalesUsrWord σ I, ⟨2⟩, clipperRedoKprMaskedWord I,
        clipperRedoIdWord I, ⟨502⟩, sel]
      (clipperRedoSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8460pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7575⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8460⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd8460pre.jump (by clipper_runtime_decode)
    (clipperJumpDest8460 v hpatch) (by evm_ov)⟩

theorem clipperRedoX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1409⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := (⟨1409⟩ : UInt256))
    (ret := (⟨502⟩ : UInt256)) (decoded := (⟨1431⟩ : UInt256))
    (need := (⟨64⟩ : UInt256)) hreach
    (by change decode code (⟨1409⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code (⟨1410⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨1413⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨1415⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨1416⟩ : UInt256) = some (.CALLDATASIZE, .none); clipper_decode)
    (by change decode code (⟨1417⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨1418⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨64⟩, 1))
      clipper_decode)
    (by change decode code (⟨1420⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨1421⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨1422⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨1423⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨1431⟩, 2))
      clipper_decode)
    (by change decode code (⟨1426⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (by
      change decode code (⟨1427⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨0⟩, 1))
      clipper_decode)
    (by change decode code (⟨1429⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨1430⟩ : UInt256) = some (.REVERT, .none); clipper_decode)
    hlt

end Benchmarks.Dss.Clipper

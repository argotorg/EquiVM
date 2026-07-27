import Benchmarks.Dss.Clipper.Dispatch
import Benchmarks.Dss.Clipper.UintEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! ## ABI decode and dispatch for `yank(uint256)` -/

abbrev clipperYankArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperYankArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperYankArgWord I).toNat)

abbrev clipperYankArgKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (clipperYankArgWord I).toNat)

abbrev clipperYankStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (clipperYankArgValue I)

abbrev clipperYankActiveSlot (idx : UInt256) : UInt256 :=
  activeSlot (.int (Int.ofNat idx.toNat))

theorem clipperYankActiveSlot_eq (idx : UInt256) :
    clipperYankActiveSlot idx = activeDataSlot + idx := by
  unfold clipperYankActiveSlot activeSlot
  rw [keyValueToWord_uint256]

abbrev clipperYankSalesBaseSlot (I : ExecutionEnv) : UInt256 :=
  salesBase (clipperYankArgKey I)

abbrev clipperYankSalesPosSlot (I : ExecutionEnv) : UInt256 :=
  clipperYankSalesBaseSlot I

abbrev clipperYankSalesPosRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "pos"] }

abbrev clipperYankSalesPosWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperYankSalesPosSlot I)

abbrev clipperYankSalesBaseSlotOfWord (w : UInt256) : UInt256 :=
  salesBase (.int (Int.ofNat w.toNat))

abbrev clipperYankSalesMovePosSlot (move : UInt256) : UInt256 :=
  clipperYankSalesBaseSlotOfWord move

abbrev clipperYankSalesMovePosRef (move : UInt256) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (.int (Int.ofNat move.toNat)), .field "pos"] }

abbrev clipperYankSalesUsrSlot (I : ExecutionEnv) : UInt256 :=
  clipperYankSalesBaseSlot I + ⟨3⟩

abbrev clipperYankSalesPackedSlot (I : ExecutionEnv) : UInt256 :=
  clipperYankSalesBaseSlot I + ⟨3⟩

abbrev clipperYankSalesUsrRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "usr"] }

abbrev clipperYankSalesUsrWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I (clipperYankSalesUsrSlot I)) solcAddrMask

abbrev clipperYankSalesTabSlot (I : ExecutionEnv) : UInt256 :=
  clipperYankSalesBaseSlot I + ⟨1⟩

abbrev clipperYankSalesTabRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "tab"] }

abbrev clipperYankSalesTabWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperYankSalesTabSlot I)

abbrev clipperYankSalesLotSlot (I : ExecutionEnv) : UInt256 :=
  clipperYankSalesBaseSlot I + ⟨2⟩

abbrev clipperYankSalesLotRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "lot"] }

abbrev clipperYankSalesLotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperYankSalesLotSlot I)

abbrev clipperYankSalesTopSlot (I : ExecutionEnv) : UInt256 :=
  clipperYankSalesBaseSlot I + ⟨4⟩

abbrev clipperYankSalesDeleteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperYankArgKey I)] }

abbrev clipperYankDogWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I ⟨1⟩

abbrev clipperYankDogTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (clipperYankDogWord σ I)

theorem clipperYankSalesBaseSlot_eq (I : ExecutionEnv) :
    clipperYankSalesBaseSlot I = solcMappingSlot ⟨12⟩ (clipperYankArgWord I) := by
  unfold clipperYankSalesBaseSlot salesBase mapSlot solcMappingSlot clipperYankArgKey
  rw [keyValueToWord_uint256]

theorem clipperDecode_yank_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((yankTransition v).params.map Param.name)
      (transitionSignature (yankTransition v)).paramTypes I.calldata =
        some (clipperYankStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["id"] [uint256] I.calldata = _
  simpa [config, clipperYankStore, clipperYankArgValue, clipperYankArgWord] using
    decodeCalldataWithMode_legacyUint256_ok (cd := I.calldata) (x := "id") hsz36

theorem clipperDecode_yank_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode ((yankTransition v).params.map Param.name)
      (transitionSignature (yankTransition v)).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["id"] [uint256] I.calldata = none
  simpa [config] using
    decodeCalldataWithMode_legacyUint256_none_short (cd := I.calldata) (x := "id") hsz4
      hshort

theorem clipperYankSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 28)) :
    clipperSelWord I = clipperSelNat 28 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x26 0xe0 0x27 0xf1 (clipperSelNat 28)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_yank (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 28)) :
    dispatchMsg (contract v) I.calldata = some (yankTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
        upchostTransition v, vatTransition v, vowTransition, wardsTransition])
    (post := [])
    (ti := yankTransition v) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [selectorOf, redoSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, relySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, salesSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, spotterSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, stoppedSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tailSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, takeSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, upchostSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, vatSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, vowSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, wardsSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, yankSelectorBytes v]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
set_option linter.unusedTactic false in
theorem clipperReachYankBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 28)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperYankSelectorWord hsz hsel
  have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by
        change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
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
  have h369 := clipperSplitTaken (pc := (⟨261⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by
          change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 9, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨369⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨369⟩ : UInt256) (by native_decide))
    (by simp)
  have h381 := clipperSplitNotTaken (pc := (⟨370⟩ : UInt256))
    (next := (⟨381⟩ : UInt256)) (pivot := clipperSelNat 21)
    (tgt := (⟨429⟩ : UInt256))
    (h369.jumpdest
      (by
          change decode code (⟨369⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨370⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨370⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨429⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨370⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h392 := clipperArmNotTaken (pc := (⟨381⟩ : UInt256))
    (next := (⟨392⟩ : UInt256)) (sel := clipperSelNat 21)
    (tgt := (⟨592⟩ : UInt256)) h381
    (by
        change decode code (⟨381⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨381⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨381⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨381⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨592⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨381⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h403 := clipperArmNotTaken (pc := (⟨392⟩ : UInt256))
    (next := (⟨403⟩ : UInt256)) (sel := clipperSelNat 1)
    (tgt := (⟨600⟩ : UInt256)) h392
    (by
        change decode code (⟨392⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨392⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 1, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨392⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨392⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨600⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨392⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h608 := clipperArmTaken (pc := (⟨403⟩ : UInt256)) (sel := clipperSelNat 28)
    (tgt := (⟨608⟩ : UInt256)) h403
    (by
        change decode code (⟨403⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨403⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 28, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨403⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨403⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨608⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨403⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨608⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h608⟩

theorem clipperYankEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcOneUintExternalEntryWf code (⟨608⟩ : UInt256) (⟨502⟩ : UInt256)
      (⟨1912⟩ : UInt256) := by
  unfold solcOneUintExternalEntryWf solcOneUintExternalDecodedPc
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperJumpDest1912 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1912⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2500) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1912⟩ : UInt256)
      (clipperYankArgWord I :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := solcOneUintExternalLenOk
    (entry := (⟨608⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
    (routine := (⟨1912⟩ : UInt256)) hreach (clipperYankEntryWf v hpatch)
    (by
      simpa [solcOneUintExternalDecodedPc, solcOneAddressExternalDecodedPc] using
        clipperJumpDestBeforeFirstPatch v hpatch (⟨630⟩ : UInt256) (by native_decide))
    hsz36 hsize
  simpa [clipperYankArgWord] using
    solcOneUintExternalLoadAndJump
      (entry := (⟨608⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
      (routine := (⟨1912⟩ : UInt256)) hdecoded (clipperYankEntryWf v hpatch)
      (clipperJumpDest1912 v hpatch) (by simp)

theorem clipperYankX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  exact solcOneUintExternalShort (entry := (⟨608⟩ : UInt256))
    (ret := (⟨502⟩ : UInt256)) (routine := (⟨1912⟩ : UInt256)) hreach
    (clipperYankEntryWf v hpatch) hsz4 hsize hshort

end Benchmarks.Dss.Clipper

import Reasoning.ABIComposite
import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! ## ABI decode and dispatch prerequisites for `kick(uint256,uint256,address,address)` -/

abbrev clipperKickTabWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperKickLotWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev clipperKickUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev clipperKickKprWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev clipperKickTabValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperKickTabWord I).toNat)

abbrev clipperKickLotValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperKickLotWord I).toNat)

abbrev clipperKickUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (clipperKickUsrWord I).toNat)

abbrev clipperKickKprValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (clipperKickKprWord I).toNat)

abbrev clipperKickStore (I : ExecutionEnv) : Store :=
  ((((∅ : Store).insert "tab" (clipperKickTabValue I)).insert "lot"
    (clipperKickLotValue I)).insert "usr" (clipperKickUsrValue I)).insert "kpr"
    (clipperKickKprValue I)

theorem clipperDispatch_kick (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 13)) :
    dispatchMsg (contract v) I.calldata = some (kickTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v])
    (post :=
      [kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
        upchostTransition v, vatTransition v, vowTransition, wardsTransition, yankTransition v])
    (ti := kickTransition v) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | hfalse
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
    · cases hfalse
  · rw [selectorOf, kickSelectorBytes v]
    simpa [clipperSelBytes] using hsel


theorem clipperDecode_kick_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((kickTransition v).params.map Param.name)
      (transitionSignature (kickTransition v)).paramTypes I.calldata =
        some (clipperKickStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["tab", "lot", "usr", "kpr"]
    [uint256, uint256, addr, addr] I.calldata = _
  simpa [config, clipperKickStore, clipperKickTabValue, clipperKickLotValue,
    clipperKickUsrValue, clipperKickKprValue, clipperKickTabWord, clipperKickLotWord,
    clipperKickUsrWord, clipperKickKprWord] using
    decodeCalldata_legacyUint256_uint256_address_address_ok
      (cd := I.calldata) (w := "tab") (x := "lot") (y := "usr") (z := "kpr") hsz132

theorem clipperDecode_kick_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132) :
    decodeCalldataWithMode (config v).abiDecodeMode ((kickTransition v).params.map Param.name)
      (transitionSignature (kickTransition v)).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["tab", "lot", "usr", "kpr"]
    [uint256, uint256, addr, addr] I.calldata = none
  simpa [config] using
    decodeCalldata_legacyUint256_uint256_address_address_none_short
      (cd := I.calldata) (w := "tab") (x := "lot") (y := "usr") (z := "kpr")
      hsz4 hshort

abbrev clipperKickUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (clipperKickUsrWord I)

abbrev clipperKickKprMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (clipperKickKprWord I)

theorem clipperKickSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 13)) :
    clipperSelWord I = clipperSelNat 13 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x89 0x8e 0xb2 0x67 (clipperSelNat 13)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

set_option maxHeartbeats 1000000 in
theorem clipperReachKickEntry {σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 13)) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨1057⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperKickSelectorWord hsz hsel
  have h43 := RD.selectorSplitNotTakenPush2 (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide) (by native_decide) (by simp)
  have h162 := RD.selectorSplitTakenPush2 (pc := (⟨43⟩ : UInt256))
    (pivot := clipperSelNat 3) (tgt := (⟨162⟩ : UInt256)) h43
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨162⟩ : UInt256) (by native_decide))
    (by simp)
  have h174 := RD.selectorSplitNotTakenPush2 (pc := (⟨163⟩ : UInt256))
    (next := (⟨174⟩ : UInt256)) (pivot := clipperSelNat 13)
    (tgt := (⟨222⟩ : UInt256))
    (h162.jumpdest (by clipper_decode) (by simp))
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide) (by native_decide) (by simp)
  have h1057 := RD.selectorArmTakenPush2 (pc := (⟨174⟩ : UInt256))
    (sel := clipperSelNat 13) (tgt := (⟨1057⟩ : UInt256)) h174
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1057⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1057⟩

theorem clipperKickJumpDest1079 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1079⟩ : UInt256) = true :=
  clipperJumpDestBeforeFirstPatch v hpatch (⟨1079⟩ : UInt256) (by native_decide)

theorem clipperKickJumpDest5361 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5361⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : Reasoning.Theory.wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperKickX_headOk {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨1057⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨1079⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz132) hsize
  exact RD.solcExternalStaticArgsLenOk
    (entry := (⟨1057⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (decoded := (⟨1079⟩ : UInt256)) (need := (⟨128⟩ : UInt256)) hreach
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by clipper_decode)
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by clipper_decode)
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by clipper_decode)
    (clipperKickJumpDest1079 v hpatch) hlt

theorem clipperKickX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 132)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨1057⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (entry := (⟨1057⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (decoded := (⟨1079⟩ : UInt256)) (need := (⟨128⟩ : UInt256)) hreach
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by clipper_decode)
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by clipper_decode)
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by clipper_decode)
    (by clipper_decode) (by clipper_decode) (by clipper_decode) hlt

set_option maxHeartbeats 4000000 in
theorem clipperKickX_decoded {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨1057⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨5361⟩ : UInt256)
      (clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, rd1079⟩ := clipperKickX_headOk v hpatch hsz132 hsize hreach
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by native_decide
  have h100 : (⟨96⟩ : UInt256) + ⟨4⟩ = ⟨100⟩ := by native_decide
  have h68 : (⟨4⟩ : UInt256) + ⟨64⟩ = ⟨68⟩ := by native_decide
  have h36 : (⟨4⟩ : UInt256) + ⟨32⟩ = ⟨36⟩ := by native_decide
  have rd1114 := evm_run rd1079 with [
    raw jumpdest (by clipper_decode) (by evm_ov),
    raw pop (by clipper_decode) (by evm_ov),
    raw dup1 (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw swap1 (by clipper_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_decode) (by evm_ov),
    raw dup2 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw swap1 (by clipper_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_decode) (by evm_ov),
    raw shl (by clipper_decode) (by evm_ov),
    raw sub (by clipper_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_decode) (by evm_ov),
    raw dup3 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw dup2 (by clipper_decode) (by evm_ov),
    raw and (by clipper_decode) (by evm_ov),
    raw swap2 (by clipper_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw and (by clipper_decode) (by evm_ov),
    raw push2 ⟨5361⟩ (by clipper_decode) (by evm_ov)]
  rw [hmask] at rd1114
  exact ⟨_, _, by
    simpa [clipperKickTabWord, clipperKickLotWord, clipperKickUsrMaskedWord,
      clipperKickUsrWord, clipperKickKprMaskedWord, clipperKickKprWord,
      calldataWord, u256_land_comm, h100, h68, h36,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      rd1114.jump (by clipper_decode) (clipperKickJumpDest5361 v hpatch) (by evm_ov)⟩

end Benchmarks.Dss.Clipper

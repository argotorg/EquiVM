import Reasoning.ABIComposite
import Reasoning.EVMWord
import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! ## ABI decode prerequisites for `take(uint256,uint256,uint256,address,bytes)` -/

theorem clipperTakeSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 22)) :
    clipperSelWord I = clipperSelNat 22 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x81 0xa7 0x94 0xcb (clipperSelNat 22)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

abbrev clipperTakeIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperTakeAmtWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev clipperTakeMaxWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev clipperTakeWhoWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev clipperTakeDataOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev clipperTakeDataLenWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata (4 + (clipperTakeDataOffsetWord I).toNat)

abbrev clipperTakeDataBytes (I : ExecutionEnv) : List UInt8 :=
  ((I.calldata.toList.drop 4).drop ((clipperTakeDataOffsetWord I).toNat + 32)).take
    (clipperTakeDataLenWord I).toNat


abbrev clipperTakeIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperTakeIdWord I).toNat)

abbrev clipperTakeAmtValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperTakeAmtWord I).toNat)

abbrev clipperTakeMaxValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperTakeMaxWord I).toNat)

abbrev clipperTakeWhoValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)

abbrev clipperTakeDataValue (I : ExecutionEnv) : Value :=
  .bytes (ByteArray.mk (clipperTakeDataBytes I).toArray)

abbrev clipperTakeStore (I : ExecutionEnv) : Store :=
  (((((∅ : Store).insert "id" (clipperTakeIdValue I)).insert "amt"
    (clipperTakeAmtValue I)).insert "max" (clipperTakeMaxValue I)).insert "who"
    (clipperTakeWhoValue I)).insert "data" (clipperTakeDataValue I)


theorem clipperDecode_take_ok {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat)
    (hpayload :
      (((I.calldata.toList.drop 4).drop ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat) :
    decodeCalldataWithMode config.abiDecodeMode (takeTransition.params.map Param.name)
      (transitionSignature takeTransition).paramTypes I.calldata =
        some (clipperTakeStore I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata =
      some (legacyThreeUintAddressBytesDecodedStore I.calldata "id" "amt" "max" "who" "data")
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_ok
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hlenWord hlenMax hpayload

theorem clipperDecode_take_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 164) :
    decodeCalldataWithMode config.abiDecodeMode (takeTransition.params.map Param.name)
      (transitionSignature takeTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_short
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsz4 hshort


theorem clipperDecode_take_none_offset_huge {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoff : solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat) :
    decodeCalldataWithMode config.abiDecodeMode (takeTransition.params.map Param.name)
      (transitionSignature takeTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_offset_huge
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoff


theorem clipperDecode_take_none_length_short {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hshort : I.calldata.size < 4 + (clipperTakeDataOffsetWord I).toNat + 32) :
    decodeCalldataWithMode config.abiDecodeMode (takeTransition.params.map Param.name)
      (transitionSignature takeTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_short
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hshort


theorem clipperDecode_take_none_length_huge {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenHuge : solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat) :
    decodeCalldataWithMode config.abiDecodeMode (takeTransition.params.map Param.name)
      (transitionSignature takeTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_huge
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hlenWord hlenHuge


theorem clipperDecode_take_none_payload_short {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat)
    (hpayloadShort :
      (((I.calldata.toList.drop 4).drop ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length ≠ (clipperTakeDataLenWord I).toNat) :
    decodeCalldataWithMode config.abiDecodeMode (takeTransition.params.map Param.name)
      (transitionSignature takeTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_payload_short
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hlenWord hlenMax hpayloadShort

/-! ## Dispatch prerequisite for `take(uint256,uint256,uint256,address,bytes)` -/

theorem clipperDispatch_take {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 22)) :
    dispatchMsg contract I.calldata = some takeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition, kickTransition,
        kicksTransition, listTransition, redoTransition, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition])
    (post :=
      [tipTransition, upchostTransition, vatTransition, vowTransition, wardsTransition,
        yankTransition])
    (ti := takeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · rw [selectorOf, ilkSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, redoSelectorBytes, ← byteArray_eq_of_beq hsel]
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
    · cases hfalse
  · rw [selectorOf, takeSelectorBytes]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
theorem clipperReachTakeBody {σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 22)) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨912⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperTakeSelectorWord hsz hsel
  have h43 := RD.selectorSplitNotTakenPush2 (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h162 := RD.selectorSplitTakenPush2 (pc := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 3)
    (tgt := (⟨162⟩ : UInt256)) h43
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨162⟩ : UInt256) (by native_decide))
    (by simp)
  have h222 := RD.selectorSplitTakenPush2 (pc := (⟨163⟩ : UInt256)) (pivot := clipperSelNat 13)
    (tgt := (⟨222⟩ : UInt256))
    (h162.jumpdest (by clipper_decode) (by simp))
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨222⟩ : UInt256) (by native_decide))
    (by simp)
  have h234 := RD.selectorArmNotTakenPush2 (pc := (⟨223⟩ : UInt256))
    (next := (⟨234⟩ : UInt256)) (sel := clipperSelNat 20)
    (tgt := (⟨875⟩ : UInt256))
    (h222.jumpdest (by clipper_decode) (by simp))
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h245 := RD.selectorArmNotTakenPush2 (pc := (⟨234⟩ : UInt256))
    (next := (⟨245⟩ : UInt256)) (sel := clipperSelNat 0)
    (tgt := (⟨883⟩ : UInt256)) h234
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h912 := RD.selectorArmTakenPush2 (pc := (⟨245⟩ : UInt256)) (sel := clipperSelNat 22)
    (tgt := (⟨912⟩ : UInt256)) h245
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨912⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h912⟩

theorem clipperTakeX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 164)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨912⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := (⟨912⟩ : UInt256))
    (ret := (⟨502⟩ : UInt256)) (decoded := (⟨934⟩ : UInt256))
    (need := (⟨160⟩ : UInt256)) hreach
    (by clipper_decode)
    (by
      change decode code (⟨913⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨916⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨918⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨919⟩ : UInt256) = some (.CALLDATASIZE, .none); clipper_decode)
    (by change decode code (⟨920⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨921⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨160⟩, 1))
      clipper_decode)
    (by change decode code (⟨923⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨924⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨925⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨926⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨934⟩, 2))
      clipper_decode)
    (by change decode code (⟨929⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (by
      change decode code (⟨930⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨0⟩, 1))
      clipper_decode)
    (by change decode code (⟨932⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨933⟩ : UInt256) = some (.REVERT, .none); clipper_decode)
    hlt

theorem clipperTakeX_head_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz164 : 164 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨912⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  exact RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := (⟨912⟩ : UInt256))
    (ret := (⟨502⟩ : UInt256)) (decoded := (⟨934⟩ : UInt256))
    (need := (⟨160⟩ : UInt256)) hreach
    (by clipper_decode)
    (by
      change decode code (⟨913⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨916⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨918⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨919⟩ : UInt256) = some (.CALLDATASIZE, .none); clipper_decode)
    (by change decode code (⟨920⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨921⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨160⟩, 1))
      clipper_decode)
    (by change decode code (⟨923⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨924⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨925⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨926⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨934⟩, 2))
      clipper_decode)
    (by change decode code (⟨929⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨934⟩ : UInt256) (by native_decide))
    (by
      exact solcDecodeLenCheckOkUnsigned (by
        change (4 : Nat) + 160 ≤ I.calldata.size
        omega) hsize)

theorem clipperTakeLenWordGt_one {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hshort : I.calldata.size < 4 + (clipperTakeDataOffsetWord I).toNat + 32) :
    UInt256.gt
      ((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256)))
      ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨1⟩ := by
  apply ugt_one
  have hoffLe : (clipperTakeDataOffsetWord I).toNat ≤ 4294967296 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hoffMax)
  have hoff32 : (clipperTakeDataOffsetWord I).toNat + 32 < UInt256.size := by
    have hbound : 4294967296 + 32 < UInt256.size := by native_decide
    omega
  have hleft :
      (((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256))).toNat) =
        4 + (clipperTakeDataOffsetWord I).toNat + 32 := by
    rw [uadd_toNat, uadd_word_lit32_toNat (clipperTakeDataOffsetWord I) hoff32,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by
        have hbound : 4 + (4294967296 + 32) < UInt256.size := by native_decide
        omega)]
    omega
  have hright :
      (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
        I.calldata.size := by
    rw [show (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size from
      uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
        (by simpa using hsz4) hsize]
    exact ulit_toNat' I.calldata.size hsize
  rw [hleft, hright]
  omega

theorem clipperTakeLenWordGt_zero {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size) :
    UInt256.gt
      ((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256)))
      ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩ := by
  apply ugt_zero
  have hoffLe : (clipperTakeDataOffsetWord I).toNat ≤ 4294967296 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hoffMax)
  have hoff32 : (clipperTakeDataOffsetWord I).toNat + 32 < UInt256.size := by
    have hbound : 4294967296 + 32 < UInt256.size := by native_decide
    omega
  have hleft :
      (((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256))).toNat) =
        4 + (clipperTakeDataOffsetWord I).toNat + 32 := by
    rw [uadd_toNat, uadd_word_lit32_toNat (clipperTakeDataOffsetWord I) hoff32,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by
        have hbound : 4 + (4294967296 + 32) < UInt256.size := by native_decide
        omega)]
    omega
  have hright :
      (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
        I.calldata.size := by
    rw [show (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size from
      uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
        (by simpa using hsz4) hsize]
    exact ulit_toNat' I.calldata.size hsize
  rw [hleft, hright]
  exact hlenWord

theorem clipperTakeDataLenLoad_eq {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat) :
    uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I).toNat) 32) =
      clipperTakeDataLenWord I := by
  have hoffLe : (clipperTakeDataOffsetWord I).toNat ≤ 4294967296 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hoffMax)
  have hoff4 :
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I).toNat) =
        4 + (clipperTakeDataOffsetWord I).toNat := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by
        have hbound : 4 + 4294967296 < UInt256.size := by native_decide
        omega)]
  simp [clipperTakeDataLenWord, calldataWord, hoff4]

theorem clipperTakeDataLenGt_one {I : ExecutionEnv}
    (hlenHuge : solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat) :
    UInt256.gt (clipperTakeDataLenWord I) (⟨4294967296⟩ : UInt256) = ⟨1⟩ := by
  exact ugt_one (by
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    simpa [solcMaxLen, solcMaxLenV1] using hlenHuge)

theorem clipperTakeDataLenGt_zero {I : ExecutionEnv}
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat) :
    UInt256.gt (clipperTakeDataLenWord I) (⟨4294967296⟩ : UInt256) = ⟨0⟩ := by
  exact ugt_zero (by
    have hle : (clipperTakeDataLenWord I).toNat ≤ 4294967296 := by
      exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hlenMax)
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    exact hle)

theorem clipperTakePayloadGt_one {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat)
    (hpayloadShort :
      (((I.calldata.toList.drop 4).drop ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length ≠ (clipperTakeDataLenWord I).toNat) :
    UInt256.gt
      (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) +
        UInt256.mul (clipperTakeDataLenWord I) ⟨1⟩))
      ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨1⟩ := by
  apply ugt_one
  have hoffLe : (clipperTakeDataOffsetWord I).toNat ≤ 4294967296 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hoffMax)
  have hlenLe : (clipperTakeDataLenWord I).toNat ≤ 4294967296 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hlenMax)
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htailLt :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32))).length <
        (clipperTakeDataLenWord I).toNat := by
    apply Nat.lt_of_not_ge
    intro hle
    apply hpayloadShort
    rw [List.length_take, Nat.min_eq_left hle]
  have htailLen :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32))).length =
        I.calldata.size - 4 - ((clipperTakeDataOffsetWord I).toNat + 32) := by
    rw [List.length_drop, List.length_drop, htlen]
  have hshortNat :
      I.calldata.size <
        4 + (clipperTakeDataOffsetWord I).toNat + 32 + (clipperTakeDataLenWord I).toNat := by
    rw [htailLen] at htailLt
    omega
  have hoff4 :
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I).toNat) =
        4 + (clipperTakeDataOffsetWord I).toNat := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by
        have hbound : 4 + 4294967296 < UInt256.size := by native_decide
        omega)]
  have hmul1 :
      (UInt256.mul (clipperTakeDataLenWord I) (⟨1⟩ : UInt256)).toNat =
        (clipperTakeDataLenWord I).toNat := by
    rw [u256_mul_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by decide, Nat.mul_one]
    exact Nat.mod_eq_of_lt
      (show (clipperTakeDataLenWord I).toNat < UInt256.size from
        (clipperTakeDataLenWord I).val.isLt)
  have hleft :
      ((((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) +
        UInt256.mul (clipperTakeDataLenWord I) ⟨1⟩)).toNat) =
        32 + (4 + (clipperTakeDataOffsetWord I).toNat) +
          (clipperTakeDataLenWord I).toNat := by
    rw [uadd_toNat]
    rw [uadd_toNat, hoff4, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    nth_rewrite 2 [Nat.mod_eq_of_lt (by
      have hbound : 32 + (4 + 4294967296) < UInt256.size := by native_decide
      omega)]
    rw [hmul1]
    rw [Nat.mod_eq_of_lt (by
      have hbound : 32 + (4 + 4294967296) + 4294967296 < UInt256.size := by
        native_decide
      omega)]
  have hright :
      (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
        I.calldata.size := by
    rw [show (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size from
      uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
        (by simpa using hsz4) hsize]
    exact ulit_toNat' I.calldata.size hsize
  rw [hleft, hright]
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem clipperTakeX_offsetPrefix {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨977⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, rd934⟩ := hreach
  have rd977 := evm_run rd934 with [
    raw jumpdest (by clipper_decode) (by evm_ov),
    raw dup2 (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw swap2 (by clipper_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_decode) (by evm_ov),
    raw dup2 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw swap2 (by clipper_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_decode) (by evm_ov),
    raw dup3 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw swap2 (by clipper_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_decode) (by evm_ov),
    raw shl (by clipper_decode) (by evm_ov),
    raw sub (by clipper_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_decode) (by evm_ov),
    raw dup3 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov),
    raw and (by clipper_decode) (by evm_ov),
    raw swap2 (by clipper_decode) (by evm_ov),
    raw dup2 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw swap1 (by clipper_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_decode) (by evm_ov),
    raw dup2 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw push1 ⟨128⟩ (by clipper_decode) (by evm_ov),
    raw dup3 (by clipper_decode) (by evm_ov),
    raw add (by clipper_decode) (by evm_ov),
    raw calldataload (by clipper_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [clipperTakeDataOffsetWord, clipperTakeWhoWord, clipperTakeMaxWord,
      clipperTakeAmtWord, clipperTakeIdWord, calldataWord, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using rd977⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem clipperTakeX_offset_huge {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt : UInt256.gt (clipperTakeDataOffsetWord I) (⟨4294967296⟩ : UInt256) = ⟨1⟩)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd977⟩ := clipperTakeX_offsetPrefix v hpatch hreach
  have hd977 : decode code (⟨977⟩ : UInt256) =
      some (.Push .PUSH5, some ((⟨4294967296⟩ : UInt256), 5)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨977⟩ : UInt256) (by native_decide)]
    native_decide
  have rd983raw := rd977.pushConst (⟨4294967296⟩ : UInt256)
    (width := 5) (op := .PUSH5) (by decide) hd977 (by evm_ov)
  have rd983 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨983⟩ : UInt256)
      ((⟨4294967296⟩ : UInt256) :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd983raw⟩
  obtain ⟨_, _, rd983⟩ := rd983
  have hd983 : decode code (⟨983⟩ : UInt256) = some (.DUP2, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨983⟩ : UInt256) (by native_decide)]
    native_decide
  have rd984raw := rd983.dup2 hd983 (by evm_ov)
  have rd984 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨984⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: (⟨4294967296⟩ : UInt256) ::
        clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd984raw⟩
  obtain ⟨_, _, rd984⟩ := rd984
  have hd984 : decode code (⟨984⟩ : UInt256) = some (.GT, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨984⟩ : UInt256) (by native_decide)]
    native_decide
  have rd985raw := rd984.gt hd984 (by evm_ov)
  have rd985 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨985⟩ : UInt256)
      (⟨1⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa [hgt] using rd985raw⟩
  obtain ⟨_, _, rd985⟩ := rd985
  have hd985 : decode code (⟨985⟩ : UInt256) = some (.ISZERO, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨985⟩ : UInt256) (by native_decide)]
    native_decide
  have rd986raw := rd985.iszero hd985 (by evm_ov)
  have rd986 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨986⟩ : UInt256)
      (⟨0⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd986raw⟩
  obtain ⟨_, _, rd986⟩ := rd986
  have hd986 : decode code (⟨986⟩ : UInt256) =
      some (.Push .PUSH2, some ((⟨994⟩ : UInt256), 2)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨986⟩ : UInt256) (by native_decide)]
    native_decide
  have rd989raw := rd986.pushConst (⟨994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd986 (by evm_ov)
  have rd989 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨989⟩ : UInt256)
      ((⟨994⟩ : UInt256) :: ⟨0⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd989raw⟩
  obtain ⟨_, _, rd989⟩ := rd989
  have hd989 : decode code (⟨989⟩ : UInt256) = some (.JUMPI, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨989⟩ : UInt256) (by native_decide)]
    native_decide
  have rd990raw := rd989.jumpiNT hd989 rfl (by evm_ov)
  have rd990 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨990⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd990raw⟩
  obtain ⟨_, _, rd990⟩ := rd990
  have hd990 : decode code (⟨990⟩ : UInt256) =
      some (.Push .PUSH1, some ((⟨0⟩ : UInt256), 1)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨990⟩ : UInt256) (by native_decide)]
    native_decide
  have hd992 : decode code (⟨992⟩ : UInt256) = some (.DUP1, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨992⟩ : UInt256) (by native_decide)]
    native_decide
  have hd993 : decode code (⟨993⟩ : UInt256) = some (.REVERT, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨993⟩ : UInt256) (by native_decide)]
    native_decide
  exact evm_run rd990 with [
    raw push1 ⟨0⟩ hd990 (by evm_ov),
    raw dup1 hd992 (by evm_ov),
    raw rev 0 hd993 mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem clipperTakeX_offset_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt : UInt256.gt (clipperTakeDataOffsetWord I) (⟨4294967296⟩ : UInt256) = ⟨0⟩)
    (hreach : ∃ k C, RD code I g
      (initState σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨994⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, rd977⟩ := clipperTakeX_offsetPrefix v hpatch hreach
  have hd977 : decode code (⟨977⟩ : UInt256) =
      some (.Push .PUSH5, some ((⟨4294967296⟩ : UInt256), 5)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨977⟩ : UInt256) (by native_decide)]
    native_decide
  have rd983raw := rd977.pushConst (⟨4294967296⟩ : UInt256)
    (width := 5) (op := .PUSH5) (by decide) hd977 (by evm_ov)
  have rd983 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨983⟩ : UInt256)
      ((⟨4294967296⟩ : UInt256) :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd983raw⟩
  obtain ⟨_, _, rd983⟩ := rd983
  have hd983 : decode code (⟨983⟩ : UInt256) = some (.DUP2, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨983⟩ : UInt256) (by native_decide)]
    native_decide
  have rd984raw := rd983.dup2 hd983 (by evm_ov)
  have rd984 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨984⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: (⟨4294967296⟩ : UInt256) ::
        clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd984raw⟩
  obtain ⟨_, _, rd984⟩ := rd984
  have hd984 : decode code (⟨984⟩ : UInt256) = some (.GT, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨984⟩ : UInt256) (by native_decide)]
    native_decide
  have rd985raw := rd984.gt hd984 (by evm_ov)
  have rd985 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨985⟩ : UInt256)
      (⟨0⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa [hgt] using rd985raw⟩
  obtain ⟨_, _, rd985⟩ := rd985
  have hd985 : decode code (⟨985⟩ : UInt256) = some (.ISZERO, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨985⟩ : UInt256) (by native_decide)]
    native_decide
  have rd986raw := rd985.iszero hd985 (by evm_ov)
  have rd986 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨986⟩ : UInt256)
      (⟨1⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd986raw⟩
  obtain ⟨_, _, rd986⟩ := rd986
  have hd986 : decode code (⟨986⟩ : UInt256) =
      some (.Push .PUSH2, some ((⟨994⟩ : UInt256), 2)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨986⟩ : UInt256) (by native_decide)]
    native_decide
  have rd989raw := rd986.pushConst (⟨994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd986 (by evm_ov)
  have rd989 : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨989⟩ : UInt256)
      ((⟨994⟩ : UInt256) :: ⟨1⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa using rd989raw⟩
  obtain ⟨_, _, rd989⟩ := rd989
  have hd989 : decode code (⟨989⟩ : UInt256) = some (.JUMPI, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨989⟩ : UInt256) (by native_decide)]
    native_decide
  exact ⟨_, _, rd989.jumpiT hd989 (by native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨994⟩ : UInt256) (by native_decide))
    (by evm_ov)⟩

theorem clipperTakeX_length_short {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt :
      UInt256.gt
        ((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256)))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨1⟩)
    (hreach : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨994⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd994⟩ := hreach
  have hgt' :
      UInt256.gt
        (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) + (⟨32⟩ : UInt256))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨1⟩ := by
    simpa [u256_add_assoc] using hgt
  have rd1003 := evm_run rd994 with [
    raw jumpdest
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd1007 := evm_run rd1003 with [
    raw iszero
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨1012⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd1008 := rd1007.jumpiNT
    (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
    (by rw [hgt']; native_decide) (by evm_ov)
  exact evm_run rd1008 with [
    raw push1 ⟨0⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw rev 0
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      mem_cost (by evm_ov)]

theorem clipperTakeX_length_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt :
      UInt256.gt
        ((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256)))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩)
    (hreach : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨994⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨1012⟩ : UInt256)
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, rd994⟩ := hreach
  have hgt' :
      UInt256.gt
        (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) + (⟨32⟩ : UInt256))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩ := by
    simpa [u256_add_assoc] using hgt
  have rd1003 := evm_run rd994 with [
    raw jumpdest
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd1007 := evm_run rd1003 with [
    raw iszero
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨1012⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd1012 := rd1007.jumpiT
    (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
    (by rw [hgt']; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1012⟩ : UInt256) (by native_decide))
    (by evm_ov)
  exact ⟨_, _, by simpa using rd1012⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem clipperTakeX_length_huge {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenHuge : solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat)
    (hreach : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨1012⟩ : UInt256)
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd1012⟩ := hreach
  have hload := clipperTakeDataLenLoad_eq (I := I) hoffMax
  have hlenGt := clipperTakeDataLenGt_one (I := I) hlenHuge
  have rd1028 := evm_run rd1012 with [
    raw jumpdest
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw calldataload
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have hd1028 : decode code (⟨1028⟩ : UInt256) =
      some (.Push .PUSH5, some ((⟨4294967296⟩ : UInt256), 5)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨1028⟩ : UInt256) (by native_decide)]
    native_decide
  have rd1034 := rd1028.pushConst (⟨4294967296⟩ : UInt256)
    (width := 5) (op := .PUSH5) (by decide) hd1028 (by evm_ov)
  have rd1041 := evm_run rd1034 with [
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw or
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw iszero
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨1046⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd1042 := rd1041.jumpiNT
    (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
    (by
      rw [hload, hlenGt]
      exact isZero_eq_zero_of_ne (u256_lor_one_ne_zero _))
    (by evm_ov)
  exact evm_run rd1042 with [
    raw push1 ⟨0⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw rev 0
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem clipperTakeX_payload_short {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat)
    (hpayloadGt :
      UInt256.gt
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) +
          UInt256.mul (clipperTakeDataLenWord I) ⟨1⟩))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨1⟩)
    (hreach : ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨1012⟩ : UInt256)
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd1012⟩ := hreach
  have hload := clipperTakeDataLenLoad_eq (I := I) hoffMax
  have hlenGt := clipperTakeDataLenGt_zero (I := I) hlenMax
  have rd1028 := evm_run rd1012 with [
    raw jumpdest
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw calldataload
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have hd1028 : decode code (⟨1028⟩ : UInt256) =
      some (.Push .PUSH5, some ((⟨4294967296⟩ : UInt256), 5)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨1028⟩ : UInt256) (by native_decide)]
    native_decide
  have rd1034 := rd1028.pushConst (⟨4294967296⟩ : UInt256)
    (width := 5) (op := .PUSH5) (by decide) hd1028 (by evm_ov)
  have rd1041 := evm_run rd1034 with [
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw or
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw iszero
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨1046⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd1042 := rd1041.jumpiNT
    (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
    (by
      rw [hload, hlenGt, hpayloadGt]
      native_decide)
    (by evm_ov)
  exact evm_run rd1042 with [
    raw push1 ⟨0⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw rev 0
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      mem_cost (by evm_ov)]

end Benchmarks.Dss.Clipper

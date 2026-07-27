import Benchmarks.Dss.Clipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
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

-- LIBRARY CANDIDATE: legacy-solc05 four-word scalar decoding for
-- `(uint256,uint256,address,address)`.
theorem decodeCalldata_legacyUint256_uint256_address_address_ok {cd : ByteArray}
    {w x y z : Solm.Ident} (hsz132 : 132 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [w, x, y, z]
        [uint256, uint256, addr, addr] cd =
      some (((((∅ : Solm.Store).insert w
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert x
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert z
        (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 100 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [w, x, y, z])
    (types := [uint256, uint256, addr, addr]) (cd := cd) (by native_decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have hdecode0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 (cd.toList.drop 4) 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
          0 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 0) htake4
  have hdecode32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 (cd.toList.drop 4) 32 =
        some (.int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 32) htake36
  have hdecode64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr (cd.toList.drop 4) 64 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
    simpa [addr] using
      decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 64) htake68
  have hdecode96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr (cd.toList.drop 4) 96 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat), 96 + 32) := by
    simpa [addr] using
      decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 96) htake100
  rw [hdecode0, hdecode32, hdecode64, hdecode96]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [w, x, y, z]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat)] ∅ =
    some (((((∅ : Solm.Store).insert w
      (.int (Int.ofNat (calldataWord cd 4).toNat))).insert x
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert z
      (.address (AccountAddress.ofNat (calldataWord cd 100).toNat)))
  rw [hword4, hword36, hword68, hword100]
  simp [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: legacy-solc05 short calldata failure for
-- `(uint256,uint256,address,address)`.
theorem decodeCalldata_legacyUint256_uint256_address_address_none_short {cd : ByteArray}
    {w x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 132) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [w, x, y, z]
      [uint256, uint256, addr, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [w, x, y, z])
    (types := [uint256, uint256, addr, addr]) (cd := cd) (by native_decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 (cd.toList.drop 4) 0 =
          some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
            0 + 32) := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 0) htake0
    rw [hdecode0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hdecode32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 (cd.toList.drop 4) 32 =
            some (.int (Int.ofNat
              (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := cd.toList.drop 4) (start := 32) htake32
      rw [hdecode32]
      by_cases hlen64 : 96 ≤ (cd.toList.drop 4).length
      · have htake64 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have hdecode64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 addr (cd.toList.drop 4) 64 =
              some (.address (AccountAddress.ofNat
                (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
          simpa [addr] using
            decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 64)
              htake64
        rw [hdecode64]
        have htake96n : ¬ (((cd.toList.drop 4).drop 96).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, List.length_drop, htlen]
          omega
        have hdecode96 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 addr (cd.toList.drop 4) 96 =
              none := by
          simpa [addr] using
            decodeScalarWord_legacyAddress_none_short (bytes := cd.toList.drop 4)
              (start := 96) htake96n
        rw [hdecode96]
        simp only [Option.bind, bind]
      · have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have hdecode64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 addr (cd.toList.drop 4) 64 =
              none := by
          simpa [addr] using
            decodeScalarWord_legacyAddress_none_short (bytes := cd.toList.drop 4)
              (start := 64) htake64n
        rw [hdecode64]
        simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hdecode32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 (cd.toList.drop 4) 32 =
            none := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := cd.toList.drop 4) (start := 32) htake32n
      rw [hdecode32]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 (cd.toList.drop 4) 0 =
          none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 0) htake0n
    rw [hdecode0]
    simp only [Option.bind, bind]

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

theorem clipperKickBody (v : ClipperImmutables) {code : ByteArray}
    (_hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = code) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (clipperSelBytes 13))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

end Benchmarks.Dss.Clipper

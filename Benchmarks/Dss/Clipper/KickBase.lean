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

-- LIBRARY CANDIDATE: legacy-solc05 four-word scalar decoding for
-- `(uint256,uint256,address,address)`.
theorem decodeCalldata_legacyUint256_uint256_address_address_ok {cd : ByteArray}
    {w x y z : Solm.Ident} (hsz132 : 132 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [w, x, y, z]
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
  rw [decodeCalldataWithMode_solcV1SignedScalarWords_eq (names := [w, x, y, z])
    (types := [uint256, uint256, addr, addr]) (cd := cd) (by native_decide)]
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
      decodeScalarWordWithMode? DecodeMode.solcV1Signed uint256 (cd.toList.drop 4) 32 =
        some (.int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
        (bytes := cd.toList.drop 4) (start := 32) htake36
  have hdecode64 :
      decodeScalarWordWithMode? DecodeMode.solcV1Signed addr (cd.toList.drop 4) 64 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
    simpa [addr] using
      decodeScalarWord_solcV1SignedAddress_ok (bytes := cd.toList.drop 4) (start := 64) htake68
  have hdecode96 :
      decodeScalarWordWithMode? DecodeMode.solcV1Signed addr (cd.toList.drop 4) 96 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat), 96 + 32) := by
    simpa [addr] using
      decodeScalarWord_solcV1SignedAddress_ok (bytes := cd.toList.drop 4) (start := 96) htake100
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
    decodeCalldataWithMode DecodeMode.solcV1Signed [w, x, y, z]
      [uint256, uint256, addr, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_solcV1SignedScalarWords_eq (names := [w, x, y, z])
    (types := [uint256, uint256, addr, addr]) (cd := cd) (by native_decide)]
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
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hdecode32 :
          decodeScalarWordWithMode? DecodeMode.solcV1Signed uint256 (cd.toList.drop 4) 32 =
            some (.int (Int.ofNat
              (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
            (bytes := cd.toList.drop 4) (start := 32) htake32
      rw [hdecode32]
      by_cases hlen64 : 96 ≤ (cd.toList.drop 4).length
      · have htake64 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have hdecode64 :
            decodeScalarWordWithMode? DecodeMode.solcV1Signed addr (cd.toList.drop 4) 64 =
              some (.address (AccountAddress.ofNat
                (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
          simpa [addr] using
            decodeScalarWord_solcV1SignedAddress_ok (bytes := cd.toList.drop 4) (start := 64)
              htake64
        rw [hdecode64]
        have htake96n : ¬ (((cd.toList.drop 4).drop 96).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, List.length_drop, htlen]
          omega
        have hdecode96 :
            decodeScalarWordWithMode? DecodeMode.solcV1Signed addr (cd.toList.drop 4) 96 =
              none := by
          simpa [addr] using
            decodeScalarWord_solcV1SignedAddress_none_short (bytes := cd.toList.drop 4)
              (start := 96) htake96n
        rw [hdecode96]
        simp only [Option.bind, bind]
      · have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have hdecode64 :
            decodeScalarWordWithMode? DecodeMode.solcV1Signed addr (cd.toList.drop 4) 64 =
              none := by
          simpa [addr] using
            decodeScalarWord_solcV1SignedAddress_none_short (bytes := cd.toList.drop 4)
              (start := 64) htake64n
        rw [hdecode64]
        simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hdecode32 :
          decodeScalarWordWithMode? DecodeMode.solcV1Signed uint256 (cd.toList.drop 4) 32 =
            none := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.solcV1Signed)
            (bytes := cd.toList.drop 4) (start := 32) htake32n
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
theorem clipperReachKickEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 13)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1057⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperKickSelectorWord hsz hsel
  have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide) (by native_decide) (by simp)
  have h162 := clipperSplitTaken (pc := (⟨43⟩ : UInt256))
    (pivot := clipperSelNat 3) (tgt := (⟨162⟩ : UInt256)) h43
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨162⟩ : UInt256) (by native_decide))
    (by simp)
  have h174 := clipperSplitNotTaken (pc := (⟨163⟩ : UInt256))
    (next := (⟨174⟩ : UInt256)) (pivot := clipperSelNat 13)
    (tgt := (⟨222⟩ : UInt256))
    (h162.jumpdest (by clipper_decode) (by simp))
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide) (by native_decide) (by simp)
  have h1057 := clipperArmTaken (pc := (⟨174⟩ : UInt256))
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
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperKickX_headOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1057⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1079⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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

theorem clipperKickX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 132)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1057⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
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
theorem clipperKickX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1057⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨5361⟩ : UInt256)
      (clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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

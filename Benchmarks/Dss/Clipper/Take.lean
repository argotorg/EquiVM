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

-- LIBRARY CANDIDATE: bitwise OR with low bit `1` is nonzero.
theorem nat_lor_one_mod_two (n : Nat) : Nat.lor 1 n % 2 = 1 := by
  nth_rewrite 1 [show 1 = Nat.bit true 0 by rfl]
  nth_rewrite 1 [← Nat.bit_bodd_div2 n]
  change (Nat.bit true 0 ||| Nat.bit n.bodd n.div2) % 2 = 1
  rw [Nat.lor_bit]
  simp

-- LIBRARY CANDIDATE: bitwise OR with word `1` is nonzero.
theorem u256_lor_one_ne_zero (x : UInt256) :
    UInt256.lor (⟨1⟩ : UInt256) x ≠ ⟨0⟩ := by
  intro h
  have hodd : (UInt256.lor (⟨1⟩ : UInt256) x).toNat % 2 = 1 := by
    rw [u256_lor_toNat]
    change (Nat.lor 1 x.toNat % UInt256.size) % 2 = 1
    rw [Nat.mod_mod_of_dvd _ (by norm_num [UInt256.size])]
    exact nat_lor_one_mod_two x.toNat
  rw [h] at hodd
  norm_num at hodd

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

abbrev clipperTakeDecodedBytes (cd : ByteArray) : ByteArray :=
  ByteArray.mk
    ((((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
      (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).toArray)

abbrev clipperTakeDecodedStore (cd : ByteArray) (a b c d e : Solm.Ident) : Store :=
  (((((∅ : Store).insert a (.int (Int.ofNat (calldataWord cd 4).toNat))).insert b
    (.int (Int.ofNat (calldataWord cd 36).toNat))).insert c
    (.int (Int.ofNat (calldataWord cd 68).toNat))).insert d
    (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))).insert e
    (.bytes (clipperTakeDecodedBytes cd))

-- LIBRARY CANDIDATE: read a word from calldata's ABI argument region at a generic offset.
theorem readNat_drop4_at_eq_calldataWord {cd : ByteArray} (off : Nat)
    (hlenWord : 4 + off + 32 ≤ cd.size) :
    readNat? (cd.toList.drop 4) off = some (calldataWord cd (4 + off)).toNat := by
  unfold readNat? readWord?
  have hread : readBytes? (cd.toList.drop 4) off 32 =
      some (((cd.toList.drop 4).drop off).take 32) := by
    unfold readBytes?
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    have hlen : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_pos hlen]
  rw [hread]
  have hword :
      bytesToWord (((cd.toList.drop 4).drop off).take 32) =
        calldataWord cd (4 + off) := by
    have h := decode_word_at_eq_any cd (4 + off) hlenWord
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simp only [Option.bind, bind, hword]
  rfl

-- LIBRARY CANDIDATE: read a dynamic payload from calldata's ABI argument region.
theorem readBytes_drop4_payload {cd : ByteArray} {off len : Nat}
    (hpayload : (((cd.toList.drop 4).drop off).take len).length = len) :
    readBytes? (cd.toList.drop 4) off len =
      some (((cd.toList.drop 4).drop off).take len) := by
  unfold readBytes?
  rw [if_pos hpayload]

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI value decoding at a known tail.
theorem decodeABIValue_legacyBytes_ok {bytes : List UInt8} {start len : Nat}
    (hreadLen : readNat? bytes start = some len)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed < len)
    (hpayload : ((bytes.drop (start + 32)).take len).length = len) :
    decodeABIValue? ABIType.bytes bytes start DecodeMode.solcV1Signed =
      some (.bytes (ByteArray.mk (((bytes.drop (start + 32)).take len).toArray)),
        start + 32 + paddedSize len) := by
  unfold decodeABIValue?
  rw [hreadLen]
  simp only [Option.bind, bind]
  rw [if_neg hlenMax]
  have hreadPayload :
      readBytes? bytes (start + 32) len = some ((bytes.drop (start + 32)).take len) := by
    unfold readBytes?
    rw [if_pos hpayload]
  rw [hreadPayload]

-- LIBRARY CANDIDATE: legacy-solc05 full-width uint256 ABI value decoding.
theorem decodeABIValue_legacyUint256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint256 bytes start DecodeMode.solcV1Signed =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
        start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.solcV1Signed)
    (ty := uint256) (bytes := bytes) (start := start) (by native_decide)]
  simpa [uint256, uint256Int] using
    decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
      (bytes := bytes) (start := start) hlen

-- LIBRARY CANDIDATE: legacy-solc05 address ABI value decoding.
theorem decodeABIValue_legacyAddress_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? addr bytes start DecodeMode.solcV1Signed =
      some (.address (AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.solcV1Signed)
    (ty := addr) (bytes := bytes) (start := start) (by native_decide)]
  simpa [addr] using
    decodeScalarWord_solcV1SignedAddress_ok (bytes := bytes) (start := start) hlen

-- LIBRARY CANDIDATE: legacy-solc05 calldata decoding for
-- `(uint256,uint256,uint256,address,bytes)`.
set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_ok {cd : ByteArray}
    {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (calldataWord cd 132).toNat)
    (hlenWord : 4 + (calldataWord cd 132).toNat + 32 ≤ cd.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed <
      (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)
    (hpayload :
      (((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [a, b, c, d, e]
        [uint256, uint256, uint256, addr, bytesDyn] cd =
      some (clipperTakeDecodedStore cd a b c d e) := by
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
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat =
        some (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat :=
    readNat_drop4_at_eq_calldataWord (cd := cd) (calldataWord cd 132).toNat hlenWord
  have hdecodeBytes :
      decodeABIValue? bytesDyn (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.solcV1Signed =
        some (.bytes (ByteArray.mk
            ((((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
              (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).toArray)),
          (calldataWord cd 132).toNat + 32 +
            paddedSize (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) := by
    simpa [bytesDyn] using
      decodeABIValue_legacyBytes_ok (bytes := cd.toList.drop 4)
        (start := (calldataWord cd 132).toNat)
        (len := (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)
        hreadLen hlenMax hpayload
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, bytesDyn] = some 160 by
    native_decide]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType uint256 = false := by
    native_decide
  have hsizeUInt : staticABIEncodedSize? uint256 = some 32 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hsizeAddr : staticABIEncodedSize? addr = some 32 := by
    native_decide
  have hdynBytes : isDynamicABIType bytesDyn = true := by
    native_decide
  have hvalues :
      decodeABIValues? [uint256, uint256, uint256, addr, bytesDyn] (cd.toList.drop 4)
          0 0 160 160 DecodeMode.solcV1Signed =
        some ([Value.int (Int.ofNat (calldataWord cd 4).toNat),
          Value.int (Int.ofNat (calldataWord cd 36).toNat),
          Value.int (Int.ofNat (calldataWord cd 68).toNat),
          Value.address (AccountAddress.ofNat (calldataWord cd 100).toNat),
          Value.bytes (ByteArray.mk
            ((((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
              (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).toArray))],
          max 160 ((calldataWord cd 132).toNat + 32 +
            paddedSize (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)) := by
    rw [decodeABIValues?]
    rw [hdynUInt]
    simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
    rw [hdecode0]
    simp only [Nat.zero_add, if_true]
    rw [decodeABIValues?]
    rw [hdynUInt]
    simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
    rw [hdecode32]
    simp only [if_true]
    rw [decodeABIValues?]
    rw [hdynUInt]
    simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
    rw [hdecode64]
    simp only [if_true]
    rw [decodeABIValues?]
    rw [hdynAddr]
    simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
    rw [hdecode96]
    simp only [if_true]
    rw [decodeABIValues?]
    rw [hdynBytes]
    simp only [if_true, Option.bind, bind]
    rw [hreadOff]
    dsimp only
    rw [if_neg hoffMax]
    simp only [Nat.zero_add]
    rw [hdecodeBytes]
    simp only [ABI.decodeABIValues?.eq_def, hword4, hword36, hword68, hword100,
      List.drop_zero]
    norm_num
  rw [hvalues]
  simp [decodeCalldata.insertValues, clipperTakeDecodedStore, clipperTakeDecodedBytes]

-- LIBRARY CANDIDATE: legacy-solc05 short calldata failure for
-- `(uint256,uint256,uint256,address,bytes)`.
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_short
    {cd : ByteArray} {a b c d e : Solm.Ident} (hsz4 : 4 ≤ cd.size)
    (hshort : cd.size < 164) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [a, b, c, d, e]
      [uint256, uint256, uint256, addr, bytesDyn] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, bytesDyn] = some 160 by
    native_decide]
  simp only [Option.bind, bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (cd.toList.drop 4).length < 160)]

theorem clipperDecode_take_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat)
    (hpayload :
      (((I.calldata.toList.drop 4).drop ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode ((takeTransition v).params.map Param.name)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I) := by
  change decodeCalldataWithMode DecodeMode.solcV1Signed ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata =
      some (clipperTakeDecodedStore I.calldata "id" "amt" "max" "who" "data")
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_ok
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hlenWord hlenMax hpayload

theorem clipperDecode_take_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 164) :
    decodeCalldataWithMode (config v).abiDecodeMode ((takeTransition v).params.map Param.name)
      (transitionSignature (takeTransition v)).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.solcV1Signed ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_short
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsz4 hshort

-- LIBRARY CANDIDATE: dynamic ABI calldata decoding rejects signed-huge calldata.
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_huge
    {cd : ByteArray} {a b c d e : Solm.Ident} (hhuge : 2 ^ 255 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [a, b, c, d, e]
      [uint256, uint256, uint256, addr, bytesDyn] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos (by
    constructor
    · native_decide
    · rw [htlen]
      exact hhuge)]

theorem clipperDecode_take_none_huge (v : ClipperImmutables) {I : ExecutionEnv}
    (hhuge : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((takeTransition v).params.map Param.name)
      (transitionSignature (takeTransition v)).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.solcV1Signed ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_huge
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hhuge

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI calldata decoding rejects
-- offsets above the solc-v1 dynamic data bound.
set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_offset_huge
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoff : solcMaxLen DecodeMode.solcV1Signed < (calldataWord cd 132).toNat) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [a, b, c, d, e]
      [uint256, uint256, uint256, addr, bytesDyn] cd = none := by
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
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, bytesDyn] = some 160 by
    native_decide]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType uint256 = false := by
    native_decide
  have hsizeUInt : staticABIEncodedSize? uint256 = some 32 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hsizeAddr : staticABIEncodedSize? addr = some 32 := by
    native_decide
  have hdynBytes : isDynamicABIType bytesDyn = true := by
    native_decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_pos hoff]

theorem clipperDecode_take_none_offset_huge (v : ClipperImmutables) {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoff : solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode ((takeTransition v).params.map Param.name)
      (transitionSignature (takeTransition v)).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.solcV1Signed ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_offset_huge
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoff

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI value decoding fails when
-- the dynamic length word cannot be read.
theorem decodeABIValue_legacyBytes_none_length_short {bytes : List UInt8} {start : Nat}
    (hreadLen : readNat? bytes start = none) :
    decodeABIValue? bytesDyn bytes start DecodeMode.solcV1Signed = none := by
  unfold decodeABIValue?
  simp [bytesDyn, hreadLen, Option.bind, bind]

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI value decoding fails when
-- the decoded dynamic byte length is above solc's legacy bound.
theorem decodeABIValue_legacyBytes_none_length_huge {bytes : List UInt8} {start len : Nat}
    (hreadLen : readNat? bytes start = some len)
    (hlenHuge : solcMaxLen DecodeMode.solcV1Signed < len) :
    decodeABIValue? bytesDyn bytes start DecodeMode.solcV1Signed = none := by
  unfold decodeABIValue?
  simp [bytesDyn, hreadLen, Option.bind, bind, hlenHuge]

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI value decoding fails when
-- the declared payload length cannot be read from the calldata tail.
theorem decodeABIValue_legacyBytes_none_payload_short {bytes : List UInt8} {start len : Nat}
    (hreadLen : readNat? bytes start = some len)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed < len)
    (hpayloadShort : ((bytes.drop (start + 32)).take len).length ≠ len) :
    decodeABIValue? bytesDyn bytes start DecodeMode.solcV1Signed = none := by
  unfold decodeABIValue?
  simp only [bytesDyn, hreadLen, Option.bind, bind]
  rw [if_neg hlenMax]
  unfold readBytes?
  rw [if_neg hpayloadShort]

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI calldata decoding rejects
-- accepted offsets whose following length word lies outside calldata.
set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_short
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (calldataWord cd 132).toNat)
    (hshort : cd.size < 4 + (calldataWord cd 132).toNat + 32) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [a, b, c, d, e]
      [uint256, uint256, uint256, addr, bytesDyn] cd = none := by
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
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat = none := by
    unfold readNat? readWord? readBytes?
    have hlen :
        ¬ (((cd.toList.drop 4).drop (calldataWord cd 132).toNat).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
    rfl
  have hdecodeBytes :
      decodeABIValue? bytesDyn (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.solcV1Signed = none :=
    decodeABIValue_legacyBytes_none_length_short hreadLen
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, bytesDyn] = some 160 by
    native_decide]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType uint256 = false := by
    native_decide
  have hsizeUInt : staticABIEncodedSize? uint256 = some 32 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hsizeAddr : staticABIEncodedSize? addr = some 32 := by
    native_decide
  have hdynBytes : isDynamicABIType bytesDyn = true := by
    native_decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_neg hoffMax]
  simp only [Nat.zero_add]
  rw [hdecodeBytes]

theorem clipperDecode_take_none_length_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
    (hshort : I.calldata.size < 4 + (clipperTakeDataOffsetWord I).toNat + 32) :
    decodeCalldataWithMode (config v).abiDecodeMode ((takeTransition v).params.map Param.name)
      (transitionSignature (takeTransition v)).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.solcV1Signed ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_short
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hshort

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI calldata decoding rejects
-- accepted offsets whose decoded byte length is above the solc-v1 dynamic data bound.
set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_huge
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (calldataWord cd 132).toNat)
    (hlenWord : 4 + (calldataWord cd 132).toNat + 32 ≤ cd.size)
    (hlenHuge :
      solcMaxLen DecodeMode.solcV1Signed <
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [a, b, c, d, e]
      [uint256, uint256, uint256, addr, bytesDyn] cd = none := by
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
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat =
        some (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat :=
    readNat_drop4_at_eq_calldataWord (cd := cd) (calldataWord cd 132).toNat hlenWord
  have hdecodeBytes :
      decodeABIValue? bytesDyn (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.solcV1Signed = none :=
    decodeABIValue_legacyBytes_none_length_huge hreadLen hlenHuge
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, bytesDyn] = some 160 by
    native_decide]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType uint256 = false := by
    native_decide
  have hsizeUInt : staticABIEncodedSize? uint256 = some 32 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hsizeAddr : staticABIEncodedSize? addr = some 32 := by
    native_decide
  have hdynBytes : isDynamicABIType bytesDyn = true := by
    native_decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_neg hoffMax]
  simp only [Nat.zero_add]
  rw [hdecodeBytes]

theorem clipperDecode_take_none_length_huge (v : ClipperImmutables) {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenHuge : solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode ((takeTransition v).params.map Param.name)
      (transitionSignature (takeTransition v)).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.solcV1Signed ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_huge
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hlenWord hlenHuge

-- LIBRARY CANDIDATE: legacy-solc05 dynamic `bytes` ABI calldata decoding rejects
-- accepted offsets and lengths whose declared payload extends past calldata.
set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_payload_short
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (calldataWord cd 132).toNat)
    (hlenWord : 4 + (calldataWord cd 132).toNat + 32 ≤ cd.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed <
      (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)
    (hpayloadShort :
      (((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) :
    decodeCalldataWithMode DecodeMode.solcV1Signed [a, b, c, d, e]
      [uint256, uint256, uint256, addr, bytesDyn] cd = none := by
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
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat =
        some (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat :=
    readNat_drop4_at_eq_calldataWord (cd := cd) (calldataWord cd 132).toNat hlenWord
  have hdecodeBytes :
      decodeABIValue? bytesDyn (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.solcV1Signed = none :=
    decodeABIValue_legacyBytes_none_payload_short hreadLen hlenMax hpayloadShort
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, bytesDyn] = some 160 by
    native_decide]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType uint256 = false := by
    native_decide
  have hsizeUInt : staticABIEncodedSize? uint256 = some 32 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hsizeAddr : staticABIEncodedSize? addr = some 32 := by
    native_decide
  have hdynBytes : isDynamicABIType bytesDyn = true := by
    native_decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_neg hoffMax]
  simp only [Nat.zero_add]
  rw [hdecodeBytes]

theorem clipperDecode_take_none_payload_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsmall : I.calldata.size < 2 ^ 255)
    (hsz164 : 164 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat)
    (hpayloadShort :
      (((I.calldata.toList.drop 4).drop ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length ≠ (clipperTakeDataLenWord I).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode ((takeTransition v).params.map Param.name)
      (transitionSignature (takeTransition v)).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.solcV1Signed ["id", "amt", "max", "who", "data"]
    [uint256, uint256, uint256, addr, bytesDyn] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_payload_short
    (cd := I.calldata) (a := "id") (b := "amt") (c := "max") (d := "who") (e := "data")
    hsmall hsz164 hoffMax hlenWord hlenMax hpayloadShort

/-! ## Dispatch prerequisite for `take(uint256,uint256,uint256,address,bytes)` -/

theorem clipperDispatch_take (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 22)) :
    dispatchMsg (contract v) I.calldata = some (takeTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition])
    (post :=
      [tipTransition, upchostTransition v, vatTransition v, vowTransition, wardsTransition,
        yankTransition v])
    (ti := takeTransition v) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
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
    · cases hfalse
  · rw [selectorOf, takeSelectorBytes v]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
theorem clipperReachTakeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 22)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨912⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperTakeSelectorWord hsz hsel
  have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h162 := clipperSplitTaken (pc := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 3)
    (tgt := (⟨162⟩ : UInt256)) h43
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨162⟩ : UInt256) (by native_decide))
    (by simp)
  have h222 := clipperSplitTaken (pc := (⟨163⟩ : UInt256)) (pivot := clipperSelNat 13)
    (tgt := (⟨222⟩ : UInt256))
    (h162.jumpdest (by clipper_decode) (by simp))
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨222⟩ : UInt256) (by native_decide))
    (by simp)
  have h234 := clipperArmNotTaken (pc := (⟨223⟩ : UInt256))
    (next := (⟨234⟩ : UInt256)) (sel := clipperSelNat 20)
    (tgt := (⟨875⟩ : UInt256))
    (h222.jumpdest (by clipper_decode) (by simp))
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h245 := clipperArmNotTaken (pc := (⟨234⟩ : UInt256))
    (next := (⟨245⟩ : UInt256)) (sel := clipperSelNat 0)
    (tgt := (⟨883⟩ : UInt256)) h234
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h912 := clipperArmTaken (pc := (⟨245⟩ : UInt256)) (sel := clipperSelNat 22)
    (tgt := (⟨912⟩ : UInt256)) h245
    (by clipper_decode) (by clipper_decode) (by clipper_decode) (by decide)
    (by clipper_decode) (by clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨912⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h912⟩

theorem clipperTakeX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 164)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨912⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
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

theorem clipperTakeX_head_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz164 : 164 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨912⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
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
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
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
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat) :
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
    (hlenHuge : solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat) :
    UInt256.gt (clipperTakeDataLenWord I) (⟨4294967296⟩ : UInt256) = ⟨1⟩ := by
  exact ugt_one (by
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    simpa [solcMaxLen, solcMaxLenV1] using hlenHuge)

theorem clipperTakeDataLenGt_zero {I : ExecutionEnv}
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat) :
    UInt256.gt (clipperTakeDataLenWord I) (⟨4294967296⟩ : UInt256) = ⟨0⟩ := by
  exact ugt_zero (by
    have hle : (clipperTakeDataLenWord I).toNat ≤ 4294967296 := by
      exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hlenMax)
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    exact hle)

theorem clipperTakePayloadGt_one {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat)
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
theorem clipperTakeX_offsetPrefix {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨977⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem clipperTakeX_offset_huge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt : UInt256.gt (clipperTakeDataOffsetWord I) (⟨4294967296⟩ : UInt256) = ⟨1⟩)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd977⟩ := clipperTakeX_offsetPrefix v hpatch hreach
  have hd977 : decode code (⟨977⟩ : UInt256) =
      some (.Push .PUSH5, some ((⟨4294967296⟩ : UInt256), 5)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨977⟩ : UInt256) (by native_decide)]
    native_decide
  have rd983raw := rd977.pushConst (⟨4294967296⟩ : UInt256)
    (width := 5) (op := .PUSH5) (by decide) hd977 (by evm_ov)
  have rd983 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨983⟩ : UInt256)
      ((⟨4294967296⟩ : UInt256) :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd983raw⟩
  obtain ⟨_, _, rd983⟩ := rd983
  have hd983 : decode code (⟨983⟩ : UInt256) = some (.DUP2, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨983⟩ : UInt256) (by native_decide)]
    native_decide
  have rd984raw := rd983.dup2 hd983 (by evm_ov)
  have rd984 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨984⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: (⟨4294967296⟩ : UInt256) ::
        clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd984raw⟩
  obtain ⟨_, _, rd984⟩ := rd984
  have hd984 : decode code (⟨984⟩ : UInt256) = some (.GT, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨984⟩ : UInt256) (by native_decide)]
    native_decide
  have rd985raw := rd984.gt hd984 (by evm_ov)
  have rd985 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨985⟩ : UInt256)
      (⟨1⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hgt] using rd985raw⟩
  obtain ⟨_, _, rd985⟩ := rd985
  have hd985 : decode code (⟨985⟩ : UInt256) = some (.ISZERO, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨985⟩ : UInt256) (by native_decide)]
    native_decide
  have rd986raw := rd985.iszero hd985 (by evm_ov)
  have rd986 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨986⟩ : UInt256)
      (⟨0⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd986raw⟩
  obtain ⟨_, _, rd986⟩ := rd986
  have hd986 : decode code (⟨986⟩ : UInt256) =
      some (.Push .PUSH2, some ((⟨994⟩ : UInt256), 2)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨986⟩ : UInt256) (by native_decide)]
    native_decide
  have rd989raw := rd986.pushConst (⟨994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd986 (by evm_ov)
  have rd989 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨989⟩ : UInt256)
      ((⟨994⟩ : UInt256) :: ⟨0⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd989raw⟩
  obtain ⟨_, _, rd989⟩ := rd989
  have hd989 : decode code (⟨989⟩ : UInt256) = some (.JUMPI, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨989⟩ : UInt256) (by native_decide)]
    native_decide
  have rd990raw := rd989.jumpiNT hd989 rfl (by evm_ov)
  have rd990 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨990⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem clipperTakeX_offset_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt : UInt256.gt (clipperTakeDataOffsetWord I) (⟨4294967296⟩ : UInt256) = ⟨0⟩)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨934⟩ : UInt256)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨502⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨994⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd977⟩ := clipperTakeX_offsetPrefix v hpatch hreach
  have hd977 : decode code (⟨977⟩ : UInt256) =
      some (.Push .PUSH5, some ((⟨4294967296⟩ : UInt256), 5)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨977⟩ : UInt256) (by native_decide)]
    native_decide
  have rd983raw := rd977.pushConst (⟨4294967296⟩ : UInt256)
    (width := 5) (op := .PUSH5) (by decide) hd977 (by evm_ov)
  have rd983 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨983⟩ : UInt256)
      ((⟨4294967296⟩ : UInt256) :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd983raw⟩
  obtain ⟨_, _, rd983⟩ := rd983
  have hd983 : decode code (⟨983⟩ : UInt256) = some (.DUP2, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨983⟩ : UInt256) (by native_decide)]
    native_decide
  have rd984raw := rd983.dup2 hd983 (by evm_ov)
  have rd984 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨984⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: (⟨4294967296⟩ : UInt256) ::
        clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd984raw⟩
  obtain ⟨_, _, rd984⟩ := rd984
  have hd984 : decode code (⟨984⟩ : UInt256) = some (.GT, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨984⟩ : UInt256) (by native_decide)]
    native_decide
  have rd985raw := rd984.gt hd984 (by evm_ov)
  have rd985 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨985⟩ : UInt256)
      (⟨0⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hgt] using rd985raw⟩
  obtain ⟨_, _, rd985⟩ := rd985
  have hd985 : decode code (⟨985⟩ : UInt256) = some (.ISZERO, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨985⟩ : UInt256) (by native_decide)]
    native_decide
  have rd986raw := rd985.iszero hd985 (by evm_ov)
  have rd986 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨986⟩ : UInt256)
      (⟨1⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd986raw⟩
  obtain ⟨_, _, rd986⟩ := rd986
  have hd986 : decode code (⟨986⟩ : UInt256) =
      some (.Push .PUSH2, some ((⟨994⟩ : UInt256), 2)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨986⟩ : UInt256) (by native_decide)]
    native_decide
  have rd989raw := rd986.pushConst (⟨994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd986 (by evm_ov)
  have rd989 : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨989⟩ : UInt256)
      ((⟨994⟩ : UInt256) :: ⟨1⟩ :: clipperTakeDataOffsetWord I ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd989raw⟩
  obtain ⟨_, _, rd989⟩ := rd989
  have hd989 : decode code (⟨989⟩ : UInt256) = some (.JUMPI, .none) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨989⟩ : UInt256) (by native_decide)]
    native_decide
  exact ⟨_, _, rd989.jumpiT hd989 (by native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨994⟩ : UInt256) (by native_decide))
    (by evm_ov)⟩

theorem clipperTakeX_length_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt :
      UInt256.gt
        ((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256)))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨1⟩)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨994⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
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

theorem clipperTakeX_length_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hgt :
      UInt256.gt
        ((⟨4⟩ : UInt256) + (clipperTakeDataOffsetWord I + (⟨32⟩ : UInt256)))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨994⟩ : UInt256)
      (clipperTakeDataOffsetWord I :: ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) ::
        (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1012⟩ : UInt256)
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem clipperTakeX_length_huge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
    (hlenHuge : solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1012⟩ : UInt256)
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
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
theorem clipperTakeX_payload_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat)
    (hpayloadGt :
      UInt256.gt
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) +
          UInt256.mul (clipperTakeDataLenWord I) ⟨1⟩))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨1⟩)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1012⟩ : UInt256)
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
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

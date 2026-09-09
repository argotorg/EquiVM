import Benchmarks.Dss.Dog.FileIlkUint
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Dog

/-! ## `file(bytes32,bytes32,address)` -/

abbrev fileIlkClipIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileIlkClipWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev fileIlkClipIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileIlkClipWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileIlkClipClipWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fileIlkClipClipKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileIlkClipClipWord I)

abbrev fileIlkClipClip (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (fileIlkClipClipWord I).toNat

abbrev fileIlkClipIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (fileIlkClipIlkBytes I)

abbrev fileIlkClipIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (fileIlkClipIlkBytes I)

abbrev fileIlkClipLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (fileIlkClipIlkValue I)).insert "what"
    (.fixedBytes bytes32Width (fileIlkClipWhat I))).insert "clip"
    (.address (fileIlkClipClip I))

abbrev fileIlkClipLocalsClipIlk (I : ExecutionEnv) (clipIlk : Value) : Store :=
  (fileIlkClipLocals I).insert "clipIlk" clipIlk

abbrev fileIlkClipClipBytes : List UInt8 :=
  [99, 108, 105, 112] ++ zeroPad28

abbrev fileIlkClipSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkClipIlkKey I)

abbrev dogFileIlkClipLogTopic : UInt256 :=
  ⟨36161690779627032540159197106292867426318584669679834253171917206968282465821⟩

abbrev fileIlkClipIlkSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨3318622238⟩ ⟨224⟩

noncomputable abbrev fileIlkClipCallMem (mem : ByteArray) : ByteArray :=
  writeWord mem 128 fileIlkClipIlkSelectorWord

noncomputable abbrev fileIlkClipPostCallMem (mem out : ByteArray) : ByteArray :=
  out.write 0 (fileIlkClipCallMem mem) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

theorem fileIlkClipClipBytes_length : fileIlkClipClipBytes.length = 32 := by
  decide +native

theorem fileIlkClipCallMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (fileIlkClipCallMem mem).size = 160 := by
  rw [fileIlkClipCallMem,
    writeWord_size mem 128 fileIlkClipIlkSelectorWord (by rw [hmem]; decide +native),
    hmem]
  decide +native

theorem fileIlkClipCallMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (fileIlkClipCallMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [fileIlkClipCallMem,
    writeWord_read_preserved mem 128 64 fileIlkClipIlkSelectorWord
      (by rw [hmem]; decide +native)
      (Or.inl ⟨by norm_num, by rw [hmem]⟩)]
  exact hread64

theorem fileIlkClipIlkSelectorWord_extract :
    (UInt256.toByteArray fileIlkClipIlkSelectorWord).extract 0 4 = clipperIlkSelector := by
  decide +native

theorem fileIlkClipCallMem_read128_4 {mem : ByteArray} (hmem : mem.size = 96) :
    (fileIlkClipCallMem mem).readWithPadding 128 4 = clipperIlkSelector := by
  unfold fileIlkClipCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_window_of_gap fileIlkClipIlkSelectorWord mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; decide +native)]
  exact fileIlkClipIlkSelectorWord_extract

theorem fileIlkClipEncode_eq {v : DogImmutables} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (config v).externalABI.encode? "ilk" [] =
      some ((fileIlkClipCallMem mem).readWithPadding 128 4) := by
  rw [fileIlkClipCallMem_read128_4 hmem]
  simp [config, externalABI, clipperIlkSelector]

theorem fileIlkClipPostCallWrite_size_gt64 (out base : ByteArray) (L : Nat)
    (hbase : base.size = 160) (hLo : L ≤ out.size) :
    64 < (out.write 0 base 128 L).size := by
  rcases Nat.eq_zero_or_pos L with hzero | hpos
  · subst L
    rw [byteArray_write_len_zero, hbase]
    norm_num
  · by_cases hin : 128 + L ≤ base.size
    · rw [write_eq_gen out base 128 L (by omega) hLo hin, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract, hbase]
      omega
    · have hdest : 128 ≤ base.size := by
        rw [hbase]
        omega
      have hext : base.size < 128 + L := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 L (by omega) hLo hdest hext,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega

theorem fileIlkClipPostCallMem_size_gt64 {mem out : ByteArray}
    (hmem : mem.size = 96) (hshort : out.size < 32) (hout : out.size < UInt256.size) :
    64 < (fileIlkClipPostCallMem mem out).size := by
  unfold fileIlkClipPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hout
  rw [hlen]
  exact fileIlkClipPostCallWrite_size_gt64 out (fileIlkClipCallMem mem) out.size
    (fileIlkClipCallMem_size hmem) le_rfl

theorem fileIlkClipPostCallMem_read64_short {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 32) (hout : out.size < UInt256.size) :
    (fileIlkClipPostCallMem mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold fileIlkClipPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hout
  rw [hlen]
  change (out.write 0 (fileIlkClipCallMem mem) 128 out.size).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact fileIlkClipCallMem_read64 hmem hread64
  · rw [write_read_below_gen_extend out (fileIlkClipCallMem mem) 128 out.size 64
      hzero le_rfl (by rw [fileIlkClipCallMem_size hmem]; omega) (by omega)]
    exact fileIlkClipCallMem_read64 hmem hread64

theorem fileIlkClipPostCallMem_mload64_short {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 32) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (fileIlkClipPostCallMem mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((fileIlkClipPostCallMem mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := fileIlkClipPostCallMem_size_gt64 hmem hshort hout
      omega)
    (by decide)
    (fileIlkClipPostCallMem_read64_short hmem hread64 hshort hout)

theorem fileIlkClipPostCallMem_size_long {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (fileIlkClipPostCallMem mem out).size = 160 := by
  unfold fileIlkClipPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (fileIlkClipCallMem mem) 128 32).size = 160
  rw [write_eq_gen out (fileIlkClipCallMem mem) 128 32
    (by omega) hlo (by simpa [fileIlkClipCallMem_size hmem])]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, fileIlkClipCallMem_size hmem]
  omega

theorem fileIlkClipPostCallMem_read64_long {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (fileIlkClipPostCallMem mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold fileIlkClipPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (fileIlkClipCallMem mem) 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (fileIlkClipCallMem mem) 128 32 64
    (by omega) (by omega) (by rw [fileIlkClipCallMem_size hmem]; omega) (by omega)]
  exact fileIlkClipCallMem_read64 hmem hread64

theorem fileIlkClipPostCallMem_mload64_long {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (fileIlkClipPostCallMem mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((fileIlkClipPostCallMem mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [fileIlkClipPostCallMem_size_long hmem hlo hout]; decide)
    (by decide)
    (fileIlkClipPostCallMem_read64_long hmem hread64 hlo hout)

theorem fileIlkClipPostCallMem_read128_long {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (fileIlkClipPostCallMem mem out).readWithPadding 128 32 = out.extract 0 32 := by
  unfold fileIlkClipPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (fileIlkClipCallMem mem) 128 32).readWithPadding 128 32 =
    out.extract 0 32
  rw [write_eq_gen out (fileIlkClipCallMem mem) 128 32
    (by omega) hlo (by simpa [fileIlkClipCallMem_size hmem])]
  have hprefix : ((fileIlkClipCallMem mem).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, fileIlkClipCallMem_size hmem]
    omega
  have hsrc : (out.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((fileIlkClipCallMem mem).extract 0 128 ++ out.extract 0 32).size = 160 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hsuffix :
      ((fileIlkClipCallMem mem).extract (128 + 32) (fileIlkClipCallMem mem).size).size = 0 := by
    rw [ByteArray.size_extract, fileIlkClipCallMem_size hmem]
    norm_num
  have hreadIn :
      128 + 32 ≤
        (((fileIlkClipCallMem mem).extract 0 128 ++ out.extract 0 32) ++
          (fileIlkClipCallMem mem).extract (128 + 32) (fileIlkClipCallMem mem).size).size := by
    rw [ByteArray.size_append, hmemSize, hsuffix]
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [extract_append_left
    ((fileIlkClipCallMem mem).extract 0 128 ++ out.extract 0 32)
    ((fileIlkClipCallMem mem).extract (128 + 32) (fileIlkClipCallMem mem).size)
    128 160 (by rw [hmemSize])]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix])]
  rw [hprefix, show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  norm_num

theorem fileIlkClipPostCallMem_mload128_long {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (fileIlkClipPostCallMem mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((fileIlkClipPostCallMem mem out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      uInt256OfByteArray (out.extract 0 32) := by
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((fileIlkClipPostCallMem mem out).readWithPadding 128 32)) =
        uInt256OfByteArray (out.extract 0 32)
    rw [fileIlkClipPostCallMem_read128_long hmem hlo hout, uInt256OfByteArray_eq]
  · exact not_or.mpr
      ⟨by rw [fileIlkClipPostCallMem_size_long hmem hlo hout]; decide, by decide +native⟩

theorem fileIlkClipIlkBytes_len32 {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    (fileIlkClipIlkBytes I).length = 32 := by
  simp [fileIlkClipIlkBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileIlkClipWhat_length {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (fileIlkClipWhat I).length = 32 := by
  simp [fileIlkClipWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem keyValueToWord_fileIlkClipIlkKey {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    keyValueToWord (fileIlkClipIlkKey I) = fileIlkClipIlkWord I := by
  have hlen32 : (fileIlkClipIlkBytes I).length = 32 :=
    fileIlkClipIlkBytes_len32 (I := I) hsz100
  have hword : ABI.bytesToWord (fileIlkClipIlkBytes I) = fileIlkClipIlkWord I := by
    simpa [fileIlkClipIlkBytes, fileIlkClipIlkWord] using
      (decode_word_at_eq_any I.calldata 4 (by omega))
  have hbytes : fileIlkClipIlkBytes I = EVM.Word.toBytesBE (fileIlkClipIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkClipIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [fileIlkClipIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (fileIlkClipIlkWord I)

theorem fileIlkClipSlotFor_eq {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    fileIlkClipSlotFor I = solcMappingSlot ⟨1⟩ (fileIlkClipIlkWord I) := by
  unfold fileIlkClipSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkClipIlkKey hsz100]

theorem fileIlkClipWhatWord_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    ABI.bytesToWord (fileIlkClipWhat I) = fileIlkClipWhatWord I := by
  simpa [fileIlkClipWhat, fileIlkClipWhatWord] using
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)

theorem fileIlkClipWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hbs : fileIlkClipWhat I = bs) :
    fileIlkClipWhatWord I = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileIlkClipWhatWord_eq (I := I) hsz68).symm

theorem fileIlkClipWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hword : fileIlkClipWhatWord I = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileIlkClipWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkClipWhat I)
    (fileIlkClipWhat_length (I := I) hsz68)
  rw [fileIlkClipWhatWord_eq (I := I) hsz68, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileIlkClipWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hneq : fileIlkClipWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    fileIlkClipWhatWord I ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileIlkClipWhat_eq_of_word_eq hsz68 hword hbsLen)

theorem dogDecodeABIValues_bytes32_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .fixedBytes abiBytes32Width ((bytes.drop 32).take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  rw [if_pos hge32]
  simpa [readWord?, readBytes?, decodeABIWord?, hlen64, UInt256.toNat]

theorem dogDecodeABIValues_bytes32_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 = none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have hnot : ¬ 32 ≤ bytes.length - 32 := by omega
      simp [hnot]
    · have hge32 : 32 ≤ bytes.length - 32 := by omega
      rw [if_pos hge32]
      have hnot : ¬ 32 ≤ bytes.length - 64 := by omega
      simp [readWord?, readBytes?, hnot]

theorem dogDecodeCalldataWithMode_legacyBytes32_bytes32_address_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiBytes32, abiBytes32, abiAddress] cd =
        some ((((∅ : Solm.Store).insert x
          (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
          (.fixedBytes abiBytes32Width ((cd.toList.drop 36).take 32))).insert z
          (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))) := by
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
  have hword68 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) = calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by decide +native]
  simp only [bind, Option.bind]
  rw [dogDecodeABIValues_bytes32_bytes32_address_legacy_ok
    (bytes := cd.toList.drop 4) (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 96)]
  simp only [decodeCalldata.insertValues]
  rw [hword68]
  simp [List.drop_drop]

theorem dogDecodeCalldataWithMode_legacyBytes32_bytes32_address_none_short
    {cd : ByteArray} {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size)
    (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiBytes32, abiBytes32, abiAddress] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [dogDecodeABIValues_bytes32_bytes32_address_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem dogDecode_fileIlkClip_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (fileIlkClipTransition.params.map Param.name)
      (transitionSignature fileIlkClipTransition).paramTypes I.calldata =
        some (fileIlkClipLocals I) := by
  simpa [config, fileIlkClipTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress, fileIlkClipLocals, fileIlkClipIlkValue,
    fileIlkClipIlkBytes, fileIlkClipWhat, fileIlkClipClip] using
    dogDecodeCalldataWithMode_legacyBytes32_bytes32_address_ok (cd := I.calldata)
      (x := "ilk") (y := "what") (z := "clip") hsz100

theorem dogDecode_fileIlkClip_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (fileIlkClipTransition.params.map Param.name)
      (transitionSignature fileIlkClipTransition).paramTypes I.calldata = none := by
  simpa [config, fileIlkClipTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    dogDecodeCalldataWithMode_legacyBytes32_bytes32_address_none_short
      (cd := I.calldata) (x := "ilk") (y := "what") (z := "clip") hsz4 hshort

theorem fileIlkClipDecodeABIValues_bytes32_ok {bytes : List UInt8} {mode : DecodeMode}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeABIValues? [bytes32] bytes 0 0 32 32 mode =
      some ([.fixedBytes bytes32Width (bytes.take 32)], 32) := by
  have htake : (bytes.take 32).take 32 = bytes.take 32 := by
    simp
  cases mode <;>
    simp [decodeABIValues?, bytes32, bytes32Width, isDynamicABIType,
      staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0, htake]

theorem fileIlkClipDecodeABIValues_bytes32_none_short {bytes : List UInt8} {mode : DecodeMode}
    (hshort : bytes.length < 32) :
    decodeABIValues? [bytes32] bytes 0 0 32 32 mode = none := by
  have hnot : ¬ 32 ≤ bytes.length := by omega
  cases mode <;>
    simp [decodeABIValues?, bytes32, bytes32Width, isDynamicABIType,
      staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hnot]

theorem fileIlkClipDecodeReturnValue_bytes32_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 bytes32 returndata =
      some (.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (uInt256OfByteArray (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (returndata.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  have hword : ABI.bytesToWord (returndata.toList.take 32) =
      uInt256OfByteArray (returndata.extract 0 32) := by
    rw [hwordList, uInt256OfByteArray_eq]
  have hbytes :
      EVM.Word.toBytesBE (uInt256OfByteArray (returndata.extract 0 32)) =
        returndata.toList.take 32 := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length htake0
  rw [hbytes]
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [show ABI.abiTupleHeadSize? [bytes32] = some 32 by decide +native]
  simp only [bind, Option.bind]
  rw [fileIlkClipDecodeABIValues_bytes32_ok
    (bytes := returndata.toList) (mode := DecodeMode.legacySolc05) htake0]
  rfl

theorem fileIlkClipDecodeReturnValue_bytes32_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 bytes32 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [show ABI.abiTupleHeadSize? [bytes32] = some 32 by decide +native]
  simp only [bind, Option.bind]
  rw [fileIlkClipDecodeABIValues_bytes32_none_short
    (bytes := returndata.toList) (mode := DecodeMode.legacySolc05) (by rw [hlen]; omega)]
  rfl

theorem fileIlkClipDecode_ilk_return_ok {v : DogImmutables} {out : ByteArray}
    (ho32 : 32 ≤ out.size) :
    (config v).externalABI.decode? "ilk" out =
      some [.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32)))] := by
  change decodeReturn? bytes32 out =
    some [.fixedBytes bytes32Width
      (EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32)))]
  unfold decodeReturn?
  rw [fileIlkClipDecodeReturnValue_bytes32_ok ho32]
  rfl

theorem fileIlkClipDecode_ilk_return_none_short {v : DogImmutables} {out : ByteArray}
    (hshort : out.size < 32) :
    (config v).externalABI.decode? "ilk" out = none := by
  change decodeReturn? bytes32 out = none
  unfold decodeReturn?
  rw [fileIlkClipDecodeReturnValue_bytes32_none_short hshort]
  rfl

theorem fileIlkClipDecodedReturn_eq_ilkValue {I : ExecutionEnv} {out : ByteArray}
    (hsz100 : 100 ≤ I.calldata.size)
    (hword : uInt256OfByteArray (out.extract 0 32) = fileIlkClipIlkWord I) :
    (.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32))) : Value) =
      fileIlkClipIlkValue I := by
  have hlen32 : (fileIlkClipIlkBytes I).length = 32 :=
    fileIlkClipIlkBytes_len32 (I := I) hsz100
  have hwordI : ABI.bytesToWord (fileIlkClipIlkBytes I) = fileIlkClipIlkWord I := by
    simpa [fileIlkClipIlkBytes, fileIlkClipIlkWord, calldataWord] using
      decode_word_at_eq_any I.calldata 4 (by omega)
  have hbytes : fileIlkClipIlkBytes I = EVM.Word.toBytesBE (fileIlkClipIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkClipIlkBytes I) hlen32
    rw [hwordI] at hto
    exact hto.symm
  rw [hword, ← hbytes]

theorem fileIlkClipDecodedReturn_ne_ilkValue {I : ExecutionEnv} {out : ByteArray}
    (hsz100 : 100 ≤ I.calldata.size)
    (hneq : uInt256OfByteArray (out.extract 0 32) ≠ fileIlkClipIlkWord I) :
    (fileIlkClipIlkValue I : Value) ≠
      .fixedBytes bytes32Width
        (EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32))) := by
  intro hval
  apply hneq
  have hlen32 : (fileIlkClipIlkBytes I).length = 32 :=
    fileIlkClipIlkBytes_len32 (I := I) hsz100
  have hwordI : ABI.bytesToWord (fileIlkClipIlkBytes I) = fileIlkClipIlkWord I := by
    simpa [fileIlkClipIlkBytes, fileIlkClipIlkWord, calldataWord] using
      decode_word_at_eq_any I.calldata 4 (by omega)
  have hbytes : fileIlkClipIlkBytes I =
      EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32)) := by
    injection hval with _ hbs
  rw [← hwordI, hbytes]
  exact (bytesToWord_toBytesBE (uInt256OfByteArray (out.extract 0 32))).symm

theorem fileIlkClipLocals_get_ilk (I : ExecutionEnv) :
    (fileIlkClipLocals I).get? "ilk" =
      some (fileIlkClipIlkValue I) := by
  rw [fileIlkClipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem fileIlkClipLocals_get_what (I : ExecutionEnv) :
    (fileIlkClipLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkClipWhat I)) := by
  rw [fileIlkClipLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileIlkClipLocals_get_clip (I : ExecutionEnv) :
    (fileIlkClipLocals I).get? "clip" =
      some (.address (fileIlkClipClip I)) := by
  rw [fileIlkClipLocals, store_get_self]

theorem fileIlkClipLocals_get_ilks (I : ExecutionEnv) :
    (fileIlkClipLocals I).get? "ilks" = none := by
  rw [fileIlkClipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem fileIlkClipLocalsClipIlk_get_ilk (I : ExecutionEnv) (clipIlk : Value) :
    (fileIlkClipLocalsClipIlk I clipIlk).get? "ilk" =
      some (fileIlkClipIlkValue I) := by
  rw [fileIlkClipLocalsClipIlk, store_get_ne _ _ (by decide), fileIlkClipLocals_get_ilk]

theorem fileIlkClipLocalsClipIlk_get_clip (I : ExecutionEnv) (clipIlk : Value) :
    (fileIlkClipLocalsClipIlk I clipIlk).get? "clip" =
      some (.address (fileIlkClipClip I)) := by
  rw [fileIlkClipLocalsClipIlk, store_get_ne _ _ (by decide), fileIlkClipLocals_get_clip]

theorem fileIlkClipLocalsClipIlk_get_ilks (I : ExecutionEnv) (clipIlk : Value) :
    (fileIlkClipLocalsClipIlk I clipIlk).get? "ilks" = none := by
  rw [fileIlkClipLocalsClipIlk, store_get_ne _ _ (by decide), fileIlkClipLocals_get_ilks]

theorem fileIlkClipLocalsClipIlk_get_clipIlk (I : ExecutionEnv) (clipIlk : Value) :
    (fileIlkClipLocalsClipIlk I clipIlk).get? "clipIlk" = some clipIlk := by
  rw [fileIlkClipLocalsClipIlk, store_get_self]

theorem evalExpr_fileIlkClipWhatEq_true {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkClipWhat I)))
    (hwhat : fileIlkClipWhat I = bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkClipWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkClipWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileIlkClipWhatEq_false {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkClipWhat I)))
    (hwhat : fileIlkClipWhat I ≠ bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkClipWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkClipWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileIlkClipIlk {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hget : locals.get? "ilk" = some (fileIlkClipIlkValue I)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "ilk") =
      .ok (fileIlkClipIlkValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
    .ok (fileIlkClipIlkValue I)
  rw [hget]
  rfl

theorem evalExpr_fileIlkClipClip {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hget : locals.get? "clip" = some (.address (fileIlkClipClip I))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "clip") =
      .ok (.address (fileIlkClipClip I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "clip") =
    .ok (.address (fileIlkClipClip I))
  rw [hget]
  rfl

theorem evalExpr_fileIlkClipClipIlk {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {clipIlk : Value}
    (hget : locals.get? "clipIlk" = some clipIlk) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "clipIlk") =
      .ok clipIlk := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "clipIlk") =
    .ok clipIlk
  rw [hget]
  rfl

theorem evalExpr_fileIlkClipIlkEqClipIlk_true {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hilk : locals.get? "ilk" = some (fileIlkClipIlkValue I))
    (hclipIlk : locals.get? "clipIlk" = some (fileIlkClipIlkValue I)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "ilk") (.var "clipIlk")) = .ok (.bool true) := by
  have hilkEval := evalExpr_fileIlkClipIlk (v := v) (evm := evm) (I := I)
    (locals := locals) hilk
  have hclipEval := evalExpr_fileIlkClipClipIlk (v := v) (evm := evm)
    (locals := locals) hclipIlk
  rw [evalExpr?]
  simp only [hilkEval, hclipEval, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  all_goals intro h; cases h

theorem evalExpr_fileIlkClipIlkEqClipIlk_false {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {clipIlkBytes : List UInt8}
    (hilk : locals.get? "ilk" = some (fileIlkClipIlkValue I))
    (hclipIlk : locals.get? "clipIlk" =
      some (.fixedBytes bytes32Width clipIlkBytes))
    (hneq :
      (fileIlkClipIlkValue I : Value) ≠ .fixedBytes bytes32Width clipIlkBytes) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "ilk") (.var "clipIlk")) = .ok (.bool false) := by
  have hilkEval := evalExpr_fileIlkClipIlk (v := v) (evm := evm) (I := I)
    (locals := locals) hilk
  have hclipEval := evalExpr_fileIlkClipClipIlk (v := v) (evm := evm)
    (locals := locals) hclipIlk
  rw [evalExpr?]
  simp only [hilkEval, hclipEval, EvalResult.bind, bind]
  simp [fileIlkClipIlkValue, evalBinaryOp?, hneq]
  all_goals intro h; cases h

theorem evalExprs_fileIlkClipEmptyArgs {v : DogImmutables} {evm : EVM.State}
    {locals : Store} :
    evalExprs? (config v) { contract := contract v, locals := locals } evm [] = .ok [] := by
  rfl

theorem evalExpr_fileIlkClipCodeGuard_true {v : DogImmutables}
    {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "clip") =
        .ok (.address (fileIlkClipClip I)))
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_fileIlkClipCodeGuard_false {v : DogImmutables}
    {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "clip") =
        .ok (.address (fileIlkClipClip I)))
    (hcode :
      (UInt256.ofNat
        ((evm.lookupAccount (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem fileIlkClipClip_value_masked (I : ExecutionEnv) :
    (.address (fileIlkClipClip I) : Value) =
      .address (AccountAddress.ofNat (fileIlkClipClipKey I).toNat) := by
  simpa [fileIlkClipClip, fileIlkClipClipKey, fileIlkClipClipWord] using
    (solcAddressValue_masked (calldataWord I.calldata 68))

theorem fileIlkClipClip_eq_clipKey (I : ExecutionEnv) :
    fileIlkClipClip I = AccountAddress.ofUInt256 (fileIlkClipClipKey I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact Value.address.inj (fileIlkClipClip_value_masked I)

theorem fileIlkClipCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (fileIlkClipClipKey I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (fileIlkClipClipKey I)
  rw [← hsame]
  exact hzero

theorem fileIlkClipCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (fileIlkClipClipKey I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (fileIlkClipClipKey I)
  rw [hsame]
  exact hzero

theorem fileIlkClipCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  rw [fileIlkClipClip_eq_clipKey I]
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 (fileIlkClipClipKey I)) with
  | none =>
      simpa [initState, State.lookupAccount, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by decide +native)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [initState, State.lookupAccount, hacc] using hword

theorem fileIlkClipCode_pos_of_codeSize_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat := by
  rw [fileIlkClipClip_eq_clipKey I]
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 (fileIlkClipClipKey I)) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [initState, State.lookupAccount, hacc] using Nat.pos_of_ne_zero htoNatNe

theorem fileIlkClipClipKey_canonical (I : ExecutionEnv) :
    (fileIlkClipClipKey I).toNat < EVM.addressModulus := by
  rw [fileIlkClipClipKey, u256_land_comm solcAddrMask (fileIlkClipClipWord I)]
  exact solcAddrMask_result_canonical (fileIlkClipClipWord I)

theorem assign_fileIlkClipClipStorage (v : DogImmutables) (evm : EVM.State)
    {locals : Store} (I : ExecutionEnv) (hsz100 : 100 ≤ I.calldata.size)
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (fileIlkClipIlkValue I)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileIlkClipSlotFor I)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fileIlkClipSlotFor I))
        (fileIlkClipClipKey I))
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage (ilksF (.var "ilk") "clip") (.address (fileIlkClipClip I)) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  rw [fileIlkClipClip_value_masked I]
  have hkeyLen : (fileIlkClipIlkBytes I).length = bytes32Width.val + 1 := by
    simpa [bytes32Width] using fileIlkClipIlkBytes_len32 (I := I) hsz100
  have her :
      evalStorageRef (config v) { contract := contract v, locals := locals } evm
          (ilksF (.var "ilk") "clip") =
        .ok (fileIlkClipIlkKey I |> fun k => { base := "ilks", steps := [.mindex k, .field "clip"] }) := by
    have hilk :
        evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "ilk") =
          .ok (fileIlkClipIlkValue I) :=
      evalExpr_fileIlkClipIlk (I := I) hilk
    simp [ilksF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hilk,
      valueToKey?, fileIlkClipIlkKey, fileIlkClipIlkValue, hkeyLen, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (addrLoc (fileIlkClipSlotFor I))
          (.address (AccountAddress.ofNat (fileIlkClipClipKey I).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm (fileIlkClipSlotFor I) (fileIlkClipClipKey I)
        (fileIlkClipClipKey_canonical I)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc (fileIlkClipSlotFor I))
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy,
      addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hscalar := by trivial)
    (hstore := hstore)

theorem fileIlkClipSuccessSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkClipWhat I = fileIlkClipClipBytes)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (true, evmCall, out) false)
    (hdec : (config v).externalABI.decode? "ilk" out = some [fileIlkClipIlkValue I]) :
    let locals := fileIlkClipLocals I
    let locals1 := fileIlkClipLocalsClipIlk I (fileIlkClipIlkValue I)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
      (fileIlkClipSlotFor I)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner (fileIlkClipSlotFor I))
        (fileIlkClipClipKey I))
    ExecTransitionBody (config v) (contract v) evm0 locals fileIlkClipTransition.body
      (.returned { contract := contract v, locals := locals1 } evm1 none) := by
  intro locals locals1 evm0 evm1
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkClipLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") clipParamLit) = .ok (.bool true) := by
    simpa [clipParamLit, fileIlkClipClipBytes] using
      (evalExpr_fileIlkClipWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkClipClipBytes)
        (by simpa [locals] using fileIlkClipLocals_get_what I) hwhat)
  have hclip :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "clip") =
        .ok (.address (fileIlkClipClip I)) := by
    simpa [locals] using
      (evalExpr_fileIlkClipClip (v := v) (evm := evm0) (I := I)
        (locals := locals) (by simp [locals, fileIlkClipLocals]))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileIlkClipCodeGuard_true (v := v) (locals := locals) (I := I)
      hclip (by simpa [evm0] using hcodePos)
  have hcall' :
      typedCallViaEVM (config v) evm0 (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (true, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false))
        (.ok { contract := contract v, locals := locals1 } evmCall) := by
    simpa [locals1, fileIlkClipLocalsClipIlk, collapseReturns] using
      (ExecStmt.externalCallSuccess (cfg := config v)
        (solm := { contract := contract v, locals := locals }) (evm := evm0)
        (receiver := .var "clip") (name := "ilk") (eth := .intLit 0) (args := [])
        (retVar := "clipIlk") (perm := false) hclip (by simp [evalExpr?, pure])
        (evalExprs_fileIlkClipEmptyArgs (v := v) (evm := evm0) (locals := locals))
        hcall' hdec)
  have heq :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmCall
        (.binary .eq (.var "ilk") (.var "clipIlk")) = .ok (.bool true) := by
    exact evalExpr_fileIlkClipIlkEqClipIlk_true (v := v) (evm := evmCall) (I := I)
      (locals := locals1)
      (by simpa [locals1] using
        fileIlkClipLocalsClipIlk_get_ilk I (fileIlkClipIlkValue I))
      (by simpa [locals1] using
        fileIlkClipLocalsClipIlk_get_clipIlk I (fileIlkClipIlkValue I))
  have hclipPost :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmCall (.var "clip") =
        .ok (.address (fileIlkClipClip I)) := by
    exact evalExpr_fileIlkClipClip (v := v) (evm := evmCall) (I := I)
      (locals := locals1)
      (by simpa [locals1] using
        fileIlkClipLocalsClipIlk_get_clip I (fileIlkClipIlkValue I))
  have hassign :
      assignStorageRef? (config v) { contract := contract v, locals := locals1 } evmCall
        .storage (ilksF (.var "ilk") "clip") (.address (fileIlkClipClip I)) =
          .ok ({ contract := contract v, locals := locals1 }, evm1) := by
    simpa [evm1] using
      (assign_fileIlkClipClipStorage v evmCall (I := I) (locals := locals1)
        hsz100
        (by simpa [locals1] using
          fileIlkClipLocalsClipIlk_get_ilks I (fileIlkClipIlkValue I))
        (by simpa [locals1] using
          fileIlkClipLocalsClipIlk_get_ilk I (fileIlkClipIlkValue I)))
  have hthenRaw :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)),
          .externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false),
          .require (.binary .eq (.var "ilk") (.var "clipIlk")),
          .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ]
        (.ok { contract := contract v, locals := locals1 } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue heq) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hclipPost hassign) ExecBlock.nil
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (checkedExternalCallStmts (.var "clip") "ilk" (.intLit 0) [] "clipIlk"
          (perm := false) ++
          [ .require (.binary .eq (.var "ilk") (.var "clipIlk")),
            .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ])
        (.ok { contract := contract v, locals := locals1 } evm1) := by
    simpa [checkedExternalCallStmts] using hthenRaw
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileIlkClipTransition.body (.ok { contract := contract v, locals := locals1 } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, locals1] using
    ExecFuncBody.execBlockOK hblock

theorem fileIlkClipCallFailureSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkClipWhat I = fileIlkClipClipBytes)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (false, evmCall, out) false) :
    let locals := fileIlkClipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileIlkClipTransition.body
      .reverted := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkClipLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") clipParamLit) = .ok (.bool true) := by
    simpa [clipParamLit, fileIlkClipClipBytes] using
      (evalExpr_fileIlkClipWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkClipClipBytes)
        (by simpa [locals] using fileIlkClipLocals_get_what I) hwhat)
  have hclip :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "clip") =
        .ok (.address (fileIlkClipClip I)) := by
    simpa [locals] using
      (evalExpr_fileIlkClipClip (v := v) (evm := evm0) (I := I)
        (locals := locals) (by simp [locals, fileIlkClipLocals]))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileIlkClipCodeGuard_true (v := v) (locals := locals) (I := I)
      hclip (by simpa [evm0] using hcodePos)
  have hcall' :
      typedCallViaEVM (config v) evm0 (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (false, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hclip (by simp [evalExpr?, pure])
      (evalExprs_fileIlkClipEmptyArgs (v := v) (evm := evm0) (locals := locals))
      hcall'
  have hthenRaw :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)),
          .externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false),
          .require (.binary .eq (.var "ilk") (.var "clipIlk")),
          .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ]
        .reverted := by
    exact ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard)
      (ExecBlock.consRevert hcallStmt)
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (checkedExternalCallStmts (.var "clip") "ilk" (.intLit 0) [] "clipIlk"
          (perm := false) ++
          [ .require (.binary .eq (.var "ilk") (.var "clipIlk")),
            .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ])
        .reverted := by
    simpa [checkedExternalCallStmts] using hthenRaw
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileIlkClipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hcond hthen)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkClipDecodeRevertSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkClipWhat I = fileIlkClipClipBytes)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (true, evmCall, out) false)
    (hdec : (config v).externalABI.decode? "ilk" out = none) :
    let locals := fileIlkClipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileIlkClipTransition.body
      .reverted := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkClipLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") clipParamLit) = .ok (.bool true) := by
    simpa [clipParamLit, fileIlkClipClipBytes] using
      (evalExpr_fileIlkClipWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkClipClipBytes)
        (by simpa [locals] using fileIlkClipLocals_get_what I) hwhat)
  have hclip :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "clip") =
        .ok (.address (fileIlkClipClip I)) := by
    simpa [locals] using
      (evalExpr_fileIlkClipClip (v := v) (evm := evm0) (I := I)
        (locals := locals) (by simp [locals, fileIlkClipLocals]))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileIlkClipCodeGuard_true (v := v) (locals := locals) (I := I)
      hclip (by simpa [evm0] using hcodePos)
  have hcall' :
      typedCallViaEVM (config v) evm0 (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (true, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hclip (by simp [evalExpr?, pure])
      (evalExprs_fileIlkClipEmptyArgs (v := v) (evm := evm0) (locals := locals))
      hcall' hdec
  have hthenRaw :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)),
          .externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false),
          .require (.binary .eq (.var "ilk") (.var "clipIlk")),
          .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ]
        .reverted := by
    exact ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard)
      (ExecBlock.consRevert hcallStmt)
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (checkedExternalCallStmts (.var "clip") "ilk" (.intLit 0) [] "clipIlk"
          (perm := false) ++
          [ .require (.binary .eq (.var "ilk") (.var "clipIlk")),
            .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ])
        .reverted := by
    simpa [checkedExternalCallStmts] using hthenRaw
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileIlkClipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hcond hthen)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkClipNoCodeSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkClipWhat I = fileIlkClipClipBytes)
    (hcodeZero :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := fileIlkClipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileIlkClipTransition.body
      .reverted := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkClipLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") clipParamLit) = .ok (.bool true) := by
    simpa [clipParamLit, fileIlkClipClipBytes] using
      (evalExpr_fileIlkClipWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkClipClipBytes)
        (by simpa [locals] using fileIlkClipLocals_get_what I) hwhat)
  have hclip :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "clip") =
        .ok (.address (fileIlkClipClip I)) := by
    simpa [locals] using
      (evalExpr_fileIlkClipClip (v := v) (evm := evm0) (I := I)
        (locals := locals) (by simp [locals, fileIlkClipLocals]))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_fileIlkClipCodeGuard_false (v := v) (locals := locals) (I := I)
      hclip (by simpa [evm0] using hcodeZero)
  have hthenRaw :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)),
          .externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false),
          .require (.binary .eq (.var "ilk") (.var "clipIlk")),
          .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hcodeGuard)
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (checkedExternalCallStmts (.var "clip") "ilk" (.intLit 0) [] "clipIlk"
          (perm := false) ++
          [ .require (.binary .eq (.var "ilk") (.var "clipIlk")),
            .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ])
        .reverted := by
    simpa [checkedExternalCallStmts] using hthenRaw
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileIlkClipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hcond hthen)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkClipMismatchSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmCall : EVM.State} {out : ByteArray} {clipIlkBytes : List UInt8}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkClipWhat I = fileIlkClipClipBytes)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (true, evmCall, out) false)
    (hdec :
      (config v).externalABI.decode? "ilk" out =
        some [.fixedBytes bytes32Width clipIlkBytes])
    (hneq :
      (fileIlkClipIlkValue I : Value) ≠ .fixedBytes bytes32Width clipIlkBytes) :
    let locals := fileIlkClipLocals I
    let locals1 := fileIlkClipLocalsClipIlk I (.fixedBytes bytes32Width clipIlkBytes)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileIlkClipTransition.body
      .reverted := by
  intro locals locals1 evm0
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkClipLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") clipParamLit) = .ok (.bool true) := by
    simpa [clipParamLit, fileIlkClipClipBytes] using
      (evalExpr_fileIlkClipWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkClipClipBytes)
        (by simpa [locals] using fileIlkClipLocals_get_what I) hwhat)
  have hclip :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "clip") =
        .ok (.address (fileIlkClipClip I)) := by
    simpa [locals] using
      (evalExpr_fileIlkClipClip (v := v) (evm := evm0) (I := I)
        (locals := locals) (by simp [locals, fileIlkClipLocals]))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileIlkClipCodeGuard_true (v := v) (locals := locals) (I := I)
      hclip (by simpa [evm0] using hcodePos)
  have hcall' :
      typedCallViaEVM (config v) evm0 (EVM.address (fileIlkClipClip I)) "ilk" 0 []
        (true, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false))
        (.ok { contract := contract v, locals := locals1 } evmCall) := by
    simpa [locals1, fileIlkClipLocalsClipIlk, collapseReturns] using
      (ExecStmt.externalCallSuccess (cfg := config v)
        (solm := { contract := contract v, locals := locals }) (evm := evm0)
        (receiver := .var "clip") (name := "ilk") (eth := .intLit 0) (args := [])
        (retVar := "clipIlk") (perm := false) hclip (by simp [evalExpr?, pure])
        (evalExprs_fileIlkClipEmptyArgs (v := v) (evm := evm0) (locals := locals))
        hcall' hdec)
  have heq :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmCall
        (.binary .eq (.var "ilk") (.var "clipIlk")) = .ok (.bool false) := by
    exact evalExpr_fileIlkClipIlkEqClipIlk_false (v := v) (evm := evmCall) (I := I)
      (locals := locals1)
      (by simpa [locals1] using
        fileIlkClipLocalsClipIlk_get_ilk I (.fixedBytes bytes32Width clipIlkBytes))
      (by simpa [locals1] using
        fileIlkClipLocalsClipIlk_get_clipIlk I (.fixedBytes bytes32Width clipIlkBytes))
      hneq
  have hthenRaw :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)),
          .externalCall (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false),
          .require (.binary .eq (.var "ilk") (.var "clipIlk")),
          .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ]
        .reverted := by
    exact ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard)
      (ExecBlock.consNormal hcallStmt
        (ExecBlock.consRevert (ExecStmt.requireFalse heq)))
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (checkedExternalCallStmts (.var "clip") "ilk" (.intLit 0) [] "clipIlk"
          (perm := false) ++
          [ .require (.binary .eq (.var "ilk") (.var "clipIlk")),
            .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ])
        .reverted := by
    simpa [checkedExternalCallStmts] using hthenRaw
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileIlkClipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hcond hthen)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkClipUnrecognizedSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotClip : fileIlkClipWhat I ≠ fileIlkClipClipBytes) :
    let locals := fileIlkClipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileIlkClipTransition.body
      .reverted := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkClipLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") clipParamLit) = .ok (.bool false) := by
    simpa [clipParamLit, fileIlkClipClipBytes] using
      (evalExpr_fileIlkClipWhatEq_false (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkClipClipBytes)
        (by simpa [locals] using fileIlkClipLocals_get_what I) hnotClip)
  have hreqFalse :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileIlkClipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem dogReachFileIlkClipBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 10)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨735⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xebecb39d⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xeb 0xec 0xb3 0x9d ⟨0xebecb39d⟩
      (by decide +native) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hhighWidth : armTgtWidth code (⟨43⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h54 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [selArmNextPc, hhighWidth] using
      RD.selectorSplitNotTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh (by simp)
  have hchop : UInt256.eq (dogSelectorWord 4) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hilks : UInt256.eq (dogSelectorWord 11) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hfileIlkClip : UInt256.eq (dogSelectorWord 10) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have h65 := by
    simpa [selArmNextPc] using
      h54.selectorArmNotTaken (selNat := dogSelectorWord 4) (tgt := (⟨629⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hchop
        (by simp)
  have h76 := by
    simpa [selArmNextPc] using
      h65.selectorArmNotTaken (selNat := dogSelectorWord 11) (tgt := (⟨658⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hilks
        (by simp)
  have h735 := by
    simpa using
      h76.selectorArmTaken (selNat := dogSelectorWord 10) (tgt := (⟨735⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hfileIlkClip
        (dogPatchedDJumpPrefix1405 ⟨735⟩ hpatch (by decide +native))
        (by simp)
  exact ⟨_, _, h735⟩

theorem RD.dogFileIlkClipDecodeToRoutine {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret de sel : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨757⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J code 0).contains ⟨2417⟩ = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2417⟩
      (fileIlkClipClipKey ee :: fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd758 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd759 := rd758.pop
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd760 := rd759.dup1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd761 := rd760.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd762 := rd761.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd764 := rd762.push1 ⟨32⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd765 := rd764.dup2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd766 := rd765.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd767 := rd766.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd768 := rd767.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd770 := rd768.push1 ⟨64⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd771 := rd770.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd772 := rd771.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  have rd781 := evm_run rd772 with [
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov),
    raw and
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
      (by evm_ov)]
  have rd784 := rd781.push2 ⟨2417⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [fileIlkClipClipKey, fileIlkClipClipWord, fileIlkClipWhatWord,
      fileIlkClipIlkWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (UInt256.add (⟨32⟩ : UInt256) ⟨4⟩).toNat = 36 from by decide,
      show (UInt256.add (⟨64⟩ : UInt256) ⟨4⟩).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd784.jump
        (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
        hroutine (by evm_ov)⟩

theorem RD.dogFileIlkClipToSwitch {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨735⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2506⟩
      (fileIlkClipClipKey I :: fileIlkClipWhatWord I :: fileIlkClipIlkWord I :: ⟨313⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := ⟨735⟩) (ret := ⟨313⟩)
    (decoded := ⟨757⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (dogPatchedDJumpPrefix1405 ⟨757⟩ hpatch (by decide +native))
    (by
      exact solcDecodeLenCheckOkUnsigned
        (sz := I.calldata.size) (head := ⟨4⟩) (need := ⟨96⟩)
        (by change 100 ≤ I.calldata.size; exact hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.dogFileIlkClipDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by decide +native)) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.dogAuthCheckOk
    (code := code) (pc := ⟨2417⟩) (okPc := ⟨2506⟩)
    (key := fileIlkClipClipKey I) (ret := fileIlkClipWhatWord I)
    (R := [fileIlkClipIlkWord I, ⟨313⟩, sel])
    (by simpa [fileIlkClipClipKey, fileIlkClipWhatWord, fileIlkClipIlkWord] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
          decide +native)
    hauth (dogPatchedJumpDest hpatch (by decide +native)) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.dogFileIlkClipAuthRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨735⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := ⟨735⟩) (ret := ⟨313⟩)
    (decoded := ⟨757⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (dogPatchedDJumpPrefix1405 ⟨757⟩ hpatch (by decide +native))
    (by
      exact solcDecodeLenCheckOkUnsigned
        (sz := I.calldata.size) (head := ⟨4⟩) (need := ⟨96⟩)
        (by change 100 ≤ I.calldata.size; exact hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.dogFileIlkClipDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by decide +native)) (by simp)
  exact RD.dogAuthCheckRevert
    (code := code) (pc := ⟨2417⟩) (okPc := ⟨2506⟩)
    (key := fileIlkClipClipKey I) (ret := fileIlkClipWhatWord I)
    (R := [fileIlkClipIlkWord I, ⟨313⟩, sel])
    (by simpa [fileIlkClipClipKey, fileIlkClipWhatWord, fileIlkClipIlkWord] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
          decide +native)
    (by
      unfold solcErrorStringRevertTailWf dogAuthTailPc dogNotAuthorizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
          decide +native)
    hauth (by simp)

theorem RD.dogFileIlkClipUnrecognizedRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {clip what ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2506⟩ (clip :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileIlkClipClipBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev code g s0 := by
  have rd2507 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd2516 := evm_run rd2507 with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push4 ⟨104253079⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨228⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov)]
  have hconst : UInt256.shiftLeft ⟨104253079⟩ ⟨228⟩ =
      ABI.bytesToWord fileIlkClipClipBytes := by
    decide +native
  rw [hconst] at rd2516
  have rd2517 := rd2516.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileIlkClipClipBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2517
  have rd2518 := rd2517.iszero
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2518
  have rd2521 := rd2518.push2 ⟨1099⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd1099 := rd2521.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    one_ne_zero_uint (dogPatchedDJumpPrefix1405 ⟨1099⟩ hpatch (by decide +native))
    (by evm_ov)
  have rd1100 := rd1099.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
      decide +native)
    (by evm_ov)
  exact RD.dogErrorStringRevertTailDirect
    (pc := ⟨1100⟩) (len := ⟨27⟩) (word := dogFileUnrecognizedRawWord)
    (op := .PUSH32) (width := 32) rd1100
    (by
      unfold dogErrorStringRevertTailDirectWf dogFileUnrecognizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
    (by decide) hmem hread64 (by simp only [List.length_cons]; omega)

theorem RD.dogFileIlkClipSwitchMatched {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2506⟩
      (fileIlkClipClipKey ee :: fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmatch : fileIlkClipWhatWord ee = ABI.bytesToWord fileIlkClipClipBytes)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2522⟩
      (fileIlkClipClipKey ee :: fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
  have rd2507 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd2516 := evm_run rd2507 with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push4 ⟨104253079⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨228⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov)]
  have hconstClip : UInt256.shiftLeft ⟨104253079⟩ ⟨228⟩ =
      ABI.bytesToWord fileIlkClipClipBytes := by
    decide +native
  have heq1 :
      UInt256.eq (UInt256.shiftLeft ⟨104253079⟩ ⟨228⟩)
          (fileIlkClipWhatWord ee) = ⟨1⟩ := by
    rw [hmatch, hconstClip, uInt256_eq_self]
  have rd2517raw := rd2516.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd2517 := by
    simpa [heq1] using rd2517raw
  have rd2518 := rd2517.iszero
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd2518' := by
    simpa [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] using rd2518
  have rd2522pre := rd2518'.push2 ⟨1099⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  exact ⟨_, _, rd2522pre.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)⟩

theorem RD.dogFileIlkClipToCallMload {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2522⟩
      (fileIlkClipClipKey ee :: fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2540⟩
      (⟨128⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
  have hclipCleanR :
      UInt256.land (fileIlkClipClipKey ee) solcAddrMask = fileIlkClipClipKey ee :=
    solcAddrMask_clean (fileIlkClipClipKey_canonical ee)
  have hclipCleanL :
      UInt256.land solcAddrMask (fileIlkClipClipKey ee) = fileIlkClipClipKey ee :=
    solcAddrMask_clean_left (fileIlkClipClipKey_canonical ee)
  have rd2539raw := evm_run h with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push4 ⟨3318622238⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov)]
  obtain ⟨_, _, rd2539⟩ : ∃ k' C', RD code ee g s0 ⟨2539⟩
      (⟨64⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
    exact ⟨_, _, by
      simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, hclipCleanR, hclipCleanL] using rd2539raw⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  exact ⟨_, _, rd2539.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    mem_cost hmload64 (by decide +native) (by evm_ov)⟩

theorem RD.dogFileIlkClipWriteCallSelector {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2540⟩
      (⟨128⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2552⟩
      (⟨128⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      (fileIlkClipCallMem mem) (UInt256.ofNat 5) rdata acc k' C' := by
  have rd2551prefix := evm_run h with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push4 ⟨4294967295⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨224⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov)]
  exact ⟨_, _, by
    simpa [fileIlkClipCallMem, fileIlkClipIlkSelectorWord] using
      rd2551prefix.mstore 6 (fileIlkClipCallMem mem) (UInt256.ofNat 5)
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
          decide +native)
        mem_cost (by rfl) (by decide +native) (by evm_ov)⟩

theorem RD.dogFileIlkClipCallArgsToExtcodesize {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2552⟩
      (⟨128⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      (fileIlkClipCallMem mem) (UInt256.ofNat 5) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2566⟩
      (fileIlkClipClipKey ee :: fileIlkClipClipKey ee :: ⟨128⟩ :: ⟨4⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      (fileIlkClipCallMem mem) (UInt256.ofNat 5) rdata acc k' C' := by
  have hcallSize : (fileIlkClipCallMem mem).size = 160 := by
    rw [fileIlkClipCallMem,
      writeWord_size mem 128 fileIlkClipIlkSelectorWord (by rw [hmem]; decide +native),
      hmem]
    decide +native
  have hcallRead64 :
      (fileIlkClipCallMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [fileIlkClipCallMem,
      writeWord_read_preserved mem 128 64 fileIlkClipIlkSelectorWord
        (by rw [hmem]; decide +native)
        (Or.inl ⟨by norm_num, by rw [hmem]⟩)]
    exact hread64
  have rd2559prefix := evm_run h with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by evm_ov)]
  have rd2560 := rd2559prefix.mload 0 ⟨128⟩ (UInt256.ofNat 5)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    mem_cost
    (mloadFreePtrValue (by rw [hcallSize]; decide) (by decide) hcallRead64)
    (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [
      show UInt256.add (⟨4⟩ : UInt256) ⟨128⟩ = ⟨132⟩ from by decide +native,
      show UInt256.sub (⟨132⟩ : UInt256) ⟨128⟩ = ⟨4⟩ from by decide +native] using
      evm_run rd2560 with [
        raw dup1
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
            decide +native)
          (by evm_ov),
        raw dup4
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
            decide +native)
          (by evm_ov),
        raw sub
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
            decide +native)
          (by evm_ov),
        raw dup2
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
            decide +native)
          (by evm_ov),
        raw dup7
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
            decide +native)
          (by evm_ov),
        raw dup1
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
            decide +native)
          (by evm_ov)]⟩

theorem RD.dogFileIlkClipToExtcodesize {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2506⟩
      (fileIlkClipClipKey ee :: fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmatch : fileIlkClipWhatWord ee = ABI.bytesToWord fileIlkClipClipBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2566⟩
      (fileIlkClipClipKey ee :: fileIlkClipClipKey ee :: ⟨128⟩ :: ⟨4⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      (fileIlkClipCallMem mem) (UInt256.ofNat 5) rdata acc k' C' := by
  obtain ⟨_, _, rd2522⟩ :=
    RD.dogFileIlkClipSwitchMatched hpatch h hmatch (by omega)
  obtain ⟨_, _, rd2540⟩ :=
    RD.dogFileIlkClipToCallMload hpatch rd2522 hmem hread64 (by omega)
  obtain ⟨_, _, rd2552⟩ :=
    RD.dogFileIlkClipWriteCallSelector hpatch rd2540 (by omega)
  exact RD.dogFileIlkClipCallArgsToExtcodesize hpatch rd2552 hmem hread64 hov

theorem RD.dogFileIlkClipNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2506⟩
      (fileIlkClipClipKey ee :: fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : fileIlkClipWhatWord ee = ABI.bytesToWord fileIlkClipClipBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey ee) = ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd2566⟩ :=
    RD.dogFileIlkClipToExtcodesize hpatch h hmatch hmem hread64 hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2566⟩) (okPc := ⟨2578⟩)
    rd2566 hcodeSize
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by simp only [List.length_cons]; omega)

theorem RD.dogFileIlkClipToStaticcall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2506⟩
      (fileIlkClipClipKey ee :: fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : fileIlkClipWhatWord ee = ABI.bytesToWord fileIlkClipClipBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey ee) ≠ ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ gasWord k' C', RD code ee g s0 ⟨2581⟩
      (gasWord :: fileIlkClipClipKey ee :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨132⟩ :: ⟨3318622238⟩ :: fileIlkClipClipKey ee :: fileIlkClipClipKey ee ::
        fileIlkClipWhatWord ee :: fileIlkClipIlkWord ee :: ret :: sel :: R)
      (fileIlkClipCallMem mem) (UInt256.ofNat 5) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd2566⟩ :=
    RD.dogFileIlkClipToExtcodesize hpatch h hmatch hmem hread64 hov
  obtain ⟨gasWord, k', C', rd2581⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2566⟩) (okPc := ⟨2578⟩)
      rd2566 hcodeSize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (dogPatchedJumpDest hpatch (by decide +native))
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      (by simp only [List.length_cons]; omega)
  exact ⟨gasWord, k', C', by simpa using rd2581⟩

theorem RD.dogFileIlkClipPostStaticcall {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {ret sel : UInt256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2506⟩
      (fileIlkClipClipKey I :: fileIlkClipWhatWord I :: fileIlkClipIlkWord I ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : fileIlkClipWhatWord I = ABI.bytesToWord fileIlkClipClipBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 18 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2582⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: ⟨3318622238⟩ ::
          fileIlkClipClipKey I :: fileIlkClipClipKey I ::
          fileIlkClipWhatWord I :: fileIlkClipIlkWord I :: ret :: sel :: R)
        (fileIlkClipPostCallMem mem out) (UInt256.ofNat 5) out (cA', σ') k' C'
      ∧ typedCallViaEVM (config v) (initState cA gh bl σ σ₀ g A I)
          (EVM.address (fileIlkClipClip I)) "ilk" 0 []
          (z,
            { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' },
            out) false
      ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd2581⟩ :=
    RD.dogFileIlkClipToStaticcall hpatch h hmatch hmem hread64 hcodeSize hov
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘpack, rd2582raw, hosz⟩ :=
    RD.solcStaticcall rd2581
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k', C', ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          (⟨128⟩ : UInt256).toNat (⟨4⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 5 := by
      decide +native
    change RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2582⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey I :: fileIlkClipClipKey I ::
        fileIlkClipWhatWord I :: fileIlkClipIlkWord I :: ret :: sel :: R)
      (out.write 0 (fileIlkClipCallMem mem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      (UInt256.ofNat 5) out (cA', σ') k' C'
    exact haw ▸ rd2582raw
  · have hdepthNe : (initState cA gh bl σ σ₀ g A I).executionEnv.depth ≠ 1024 := by
      intro h
      exact absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide)
    have hΘ' :
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (fileIlkClipClipKey I))
            (toExecute σ (AccountAddress.ofUInt256 (fileIlkClipClipKey I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((fileIlkClipCallMem mem).readWithPadding 128 4) (I.depth + 1) I.header false := by
      simpa [initState] using hΘ
    have hΘcall :
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ A_in
            I.codeOwner I.sender (AccountAddress.ofUInt256 (fileIlkClipClipKey I))
            (toExecute σ (AccountAddress.ofUInt256 (fileIlkClipClipKey I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((fileIlkClipCallMem mem).readWithPadding 128 4) (I.depth + 1) I.header false := by
      simpa [accountAddress_roundtrip I.codeOwner] using hΘ'
    refine ⟨(fileIlkClipCallMem mem).readWithPadding 128 4,
      fileIlkClipEncode_eq (v := v) hmem, ?_⟩
    rw [fileIlkClipClip_eq_clipKey I]
    have htargetNorm :
        AccountAddress.ofUInt256 (fileIlkClipClipKey I) =
          EVM.address ↑(AccountAddress.ofUInt256 (fileIlkClipClipKey I)) := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact (Nat.mod_eq_of_lt (AccountAddress.ofUInt256 (fileIlkClipClipKey I)).isLt).symm
    exact callViaEVM.callMade (perm := false) wordOfInt_zero.symm
      ⟨callGas, A_in, by simpa [initState, ← htargetNorm] using hΘcall⟩ rfl
      (by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _)
      hdepthNe

theorem RD.dogFileIlkClipCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code ee g s0 ⟨2582⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2582⟩) (okPc := ⟨2598⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    hrdataSize hov

theorem RD.dogFileIlkClipStaticcallDepthLimitRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {ret sel : UInt256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2506⟩
      (fileIlkClipClipKey I :: fileIlkClipWhatWord I :: fileIlkClipIlkWord I ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : fileIlkClipWhatWord I = ABI.bytesToWord fileIlkClipClipBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileIlkClipClipKey I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 18 ≤ 1024) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd2581⟩ :=
    RD.dogFileIlkClipToStaticcall hpatch h hmatch hmem hread64 hcodeSize hov
  obtain ⟨_, _, rd2582raw⟩ :=
    RD.solcStaticcallDepthLimit rd2581
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
        decide +native)
      hdepth
      (by simp only [List.length_cons]; omega)
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  obtain ⟨_, _, rd2582⟩ : ∃ k' C',
      RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2582⟩
      (⟨0⟩ :: ⟨132⟩ :: ⟨3318622238⟩ ::
        fileIlkClipClipKey I :: fileIlkClipClipKey I ::
        fileIlkClipWhatWord I :: fileIlkClipIlkWord I :: ret :: sel :: R)
      (fileIlkClipCallMem mem) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          (⟨128⟩ : UInt256).toNat (⟨4⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 5 := by
      decide +native
    exact ⟨_, _, by simpa [hmin, byteArray_write_len_zero] using haw ▸ rd2582raw⟩
  exact RD.dogFileIlkClipCallFailure hpatch rd2582 (by decide +native)
    (by simp only [List.length_cons]; omega)

theorem RD.dogFileIlkClipCallSuccessToDecode {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code ee g s0 ⟨2582⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: ret :: sel :: R)
      mem aw out acc k C)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2600⟩
      (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: ret :: sel :: R)
      mem aw out acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨2582⟩) (okPc := ⟨2598⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (dogPatchedJumpDest hpatch (by decide +native))
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by simp only [List.length_cons]; omega)

theorem RD.dogFileIlkClipReturnDecodeShortReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    {d0 d1 d2 clipKey what ilk ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code ee g s0 ⟨2600⟩
      (d0 :: d1 :: d2 :: clipKey :: what :: ilk :: ret :: sel :: R)
      (fileIlkClipPostCallMem mem out) (UInt256.ofNat 5) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 32) (hout : out.size < UInt256.size)
    (hov : R.length + 11 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨2600⟩) (okPc := ⟨2620⟩)
    rd hshort hout mem_cost (by decide)
    (fileIlkClipPostCallMem_mload64_short hmem hread64 hshort hout)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by simp only [List.length_cons]; omega)

theorem RD.dogFileIlkClipReturnDecodeOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    {d0 d1 d2 clipKey what ilk ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code ee g s0 ⟨2600⟩
      (d0 :: d1 :: d2 :: clipKey :: what :: ilk :: ret :: sel :: R)
      (fileIlkClipPostCallMem mem out) (UInt256.ofNat 5) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2623⟩
      (uInt256OfByteArray (out.extract 0 32) :: clipKey :: what :: ilk :: ret :: sel :: R)
      (fileIlkClipPostCallMem mem out) (UInt256.ofNat 5) out acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨2600⟩) (okPc := ⟨2620⟩)
    rd hlo hout mem_cost (by decide)
    (fileIlkClipPostCallMem_mload64_long hmem hread64 hlo hout)
    (fileIlkClipPostCallMem_mload128_long hmem hlo hout)
    mem_cost (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (dogPatchedJumpDest hpatch (by decide +native))
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by simp only [List.length_cons]; omega)

abbrev dogFileIlkClipMismatchRawWord : UInt256 :=
  ⟨30954105885628950283352029347165118542796664119579042398819097392878058471424⟩

theorem solcErrorStringMem0_size_of_size160 {mem : ByteArray} (hmem : mem.size = 160) :
    (solcErrorStringMem0 mem).size = 160 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem, toByteArray_size]

theorem solcErrorStringMem1_size_of_size160 {mem : ByteArray} (hmem : mem.size = 160) :
    (solcErrorStringMem1 mem).size = 164 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem0_size_of_size160 hmem,
    toByteArray_size]

theorem solcErrorStringMem2_size_of_size160 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size160 hmem])]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem1_size_of_size160 hmem,
    toByteArray_size]

theorem solcErrorStringMem3_size_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size160 len hmem])]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem2_size_of_size160 len hmem,
    toByteArray_size]

theorem solcErrorStringMem3_read64_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size160 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size160 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size160 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size160 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size160 len word hmem]; decide)
    (by decide) (solcErrorStringMem3_read64_of_size160 len word hmem hread64)

theorem wordAt0Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt0Mem word mem).size = 160 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt32Mem word mem).size = 160 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem twoWordHashMem_size_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).size = 160 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_160 slot (wordAt0Mem_size_160 key hmem)

theorem twoWordHashMem_read0_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_read0_64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_160 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_160 key slot hmem]; omega),
      twoWordHashMem_read0_160 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_160 key slot hmem]; omega),
      twoWordHashMem_read32_160 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      simp]
  rw [hleft, hright]

theorem twoWordHashMem_solcMappingSlot_160 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_160 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem RD.dogErrorStringRevertTailDirectAw5Size160 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 5) rdata acc k C)
    (hwf : dogErrorStringRevertTailDirectWf code pc len word op width)
    (hpush : op ≠ .PUSH0)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size160 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem RD.dogFileIlkClipMismatchRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {retWord clipKey what ilk ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code ee g s0 ⟨2623⟩
      (retWord :: clipKey :: what :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 5) rdata acc k C)
    (hneq : retWord ≠ ilk)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 11 ≤ 1024) :
    RDrev code g s0 := by
  have rd2624 := rd.dup4
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd2625 := rd2624.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have heq0 : UInt256.eq ilk retWord = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2625
  have rd2628 := rd2625.push2 ⟨2705⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd2629 := rd2628.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.dogErrorStringRevertTailDirectAw5Size160
    (pc := ⟨2629⟩) (len := ⟨25⟩) (word := dogFileIlkClipMismatchRawWord)
    (op := .PUSH32) (width := 32) rd2629
    (by
      unfold dogErrorStringRevertTailDirectWf dogFileIlkClipMismatchRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
          decide +native)
    (by decide) hmem hread64 (by simp only [List.length_cons]; omega)

theorem RD.dogFileIlkClipLogTail {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {clipKey what ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2745⟩ (clipKey :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 5) rdata acc k C)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (sel :: R)
      (writeWord mem 128 (UInt256.land clipKey solcAddrMask)) (UInt256.ofNat 5) rdata
      acc k' C' := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5)
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup4
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw and
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdMstore := rdMload.mstore 0 (writeWord mem 128 (UInt256.land clipKey solcAddrMask))
    (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    mem_cost (by rfl) (by decide +native) (by evm_ov)
  have hread64' :
      (writeWord mem 128 (UInt256.land clipKey solcAddrMask)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    rw [writeWord_read_preserved mem 128 64 (UInt256.land clipKey solcAddrMask)
      (by rw [hmem]; decide +native)
      (Or.inl ⟨by norm_num, by rw [hmem]; omega⟩)]
    exact hread64
  have rdMload2Prefix := rdMstore.swap1
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    (by evm_ov)
  have rdMload2 := rdMload2Prefix.mload 0 ⟨128⟩ (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    mem_cost
    (mloadFreePtrValue
      (by
        have hsz := writeWord_size mem 128 (UInt256.land clipKey solcAddrMask)
          (by rw [hmem]; decide +native)
        rw [hsz, hmem]
        decide)
      (by decide) hread64')
    (by decide +native) (by evm_ov)
  have rdTopicStack := evm_run rdMload2 with [
    raw dup4
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup6
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdTopic := rdTopicStack.pushConst dogFileIlkClipLogTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    (by simp only [List.length_cons]; omega)
  have rdLogStack := evm_run rdTopic with [
    raw swap2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw add
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdLog := RD.log3 0 (UInt256.ofNat 5) rdLogStack
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    hperm mem_cost (by decide +native) (by simp only [List.length_cons]; omega)
  have rdPop := evm_run rdLog with [
    raw pop
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw pop
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw pop
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  exact ⟨_, _, rdPop.jump
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    hret (by evm_ov)⟩

theorem RD.dogFileIlkClipStoreLog {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {clipKey what ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2705⟩ (clipKey :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (sel :: R)
      (writeWord (twoWordHashMem ilk ⟨1⟩ mem) 128 (UInt256.land clipKey solcAddrMask))
      (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk)
        (setAddressOffset0Word (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk)) clipKey))
      k' C' := by
  have rd2706 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    (by evm_ov)
  have rdMstore0Prefix := evm_run rd2706 with [
    raw push1 ⟨0⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup4
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem ilk mem)
    (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem ilk ⟨1⟩ mem)
    (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    mem_cost (by rfl) (by decide +native) (by evm_ov)
  have hhashSize : (twoWordHashMem ilk ⟨1⟩ mem).size = 160 :=
    twoWordHashMem_size_160 ilk ⟨1⟩ hmem
  have hhashRead64 :
      (twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64_160 ilk ⟨1⟩ hmem hread64
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ ilk :=
    twoWordHashMem_solcMappingSlot_160 ⟨1⟩ ilk hmem
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨1⟩ ilk)
    (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    mem_cost hslot (by decide +native) (by evm_ov)
  have rdBeforeLoad := rdSlot.dup1
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    (by evm_ov)
  obtain ⟨_, _, rdAfterLoad⟩ := rdBeforeLoad.sload
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    (by evm_ov)
  have rdBeforeStore := evm_run rdAfterLoad with [
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw not
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw and
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw dup4
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw and
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw or
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
      (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rdBeforeStore.sstore hperm
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]; decide +native)
    (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land clipKey solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk))) =
        setAddressOffset0Word (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk)) clipKey := by
    calc
      UInt256.lor (UInt256.land clipKey solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk))) =
          UInt256.lor (UInt256.land clipKey solcAddrMask)
            (UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk))
              (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask)
              (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk))]
      _ = UInt256.lor
            (UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk))
              (UInt256.lnot solcAddrMask))
            (UInt256.land clipKey solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk)) clipKey := by
            rfl
  obtain ⟨_, _, rdStore'⟩ : ∃ k' C',
      RD code ee g s0 ⟨2745⟩ (clipKey :: what :: ilk :: ret :: sel :: R)
      (twoWordHashMem ilk ⟨1⟩ mem) (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk)
        (setAddressOffset0Word (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk)) clipKey))
      k' C' := by
    exact ⟨_, _, by
      simpa [solcSlotWord, setAddressOffset0Word, hword,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide] using rdStore⟩
  exact RD.dogFileIlkClipLogTail hpatch rdStore' hret hperm hhashSize hhashRead64 hov

theorem RD.dogFileIlkClipSuccessToRet {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {mem rdata : ByteArray} {k C : ℕ}
    {retWord clipKey what ilk ret sel : UInt256} {R : List UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code ee g s0 ⟨2623⟩
      (retWord :: clipKey :: what :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hmatch : retWord = ilk)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (sel :: R)
      (writeWord (twoWordHashMem ilk ⟨1⟩ mem) 128 (UInt256.land clipKey solcAddrMask))
      (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk)
        (setAddressOffset0Word (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk)) clipKey))
      k' C' := by
  have rd2624 := rd.dup4
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  rw [hmatch] at rd2624
  have rd2625 := rd2624.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  rw [uInt256_eq_self] at rd2625
  have rd2628 := rd2625.push2 ⟨2705⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    (by evm_ov)
  have rd2705pre := rd2628.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
      decide +native)
    one_ne_zero_uint (dogPatchedJumpDest hpatch (by decide +native))
    (by evm_ov)
  exact RD.dogFileIlkClipStoreLog hpatch rd2705pre hret hperm hmem hread64 hov

theorem RD.dogFileIlkClipSuccessStop {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {mem rdata : ByteArray} {k C : ℕ}
    {retWord clipKey what ilk sel : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code ee g s0 ⟨2623⟩
      (retWord :: clipKey :: what :: ilk :: ⟨313⟩ :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hmatch : retWord = ilk)
    (hperm : ee.perm = true)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk)
        (setAddressOffset0Word (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ ilk)) clipKey))
      ByteArray.empty := by
  obtain ⟨_, _, hretPc⟩ := RD.dogFileIlkClipSuccessToRet hpatch rd hmatch
    (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by decide +native))
    hperm hmem hread64 (by simp)
  have hretPc' := hretPc.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
      decide +native)
    (by evm_ov)
  exact RD.stop hretPc'
    (by
      change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
      rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
      decide +native)
    (by simp only [List.length_singleton]; omega)

theorem dogFileIlkClipBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg (contract v) I.calldata = some fileIlkClipTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨735⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨735⟩) (ret := ⟨313⟩)
    (decoded := ⟨757⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_fileIlkClip_none_short (v := v) hsz4 hshort)

theorem dogFileIlkClipBodyCoreOk {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some fileIlkClipTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
        (fileIlkClipTransition.params.map Param.name)
        (transitionSignature fileIlkClipTransition).paramTypes I.calldata =
          some (fileIlkClipLocals I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨735⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := dogCallerWardsSlot I
  let locals := fileIlkClipLocals I
  have hcallerWord : dogSlotWord callerSlot σ_evm I = dogSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have henc : returnEquiv ByteArray.empty none fileIlkClipTransition.returnType := by
    rw [show fileIlkClipTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  by_cases hauthEvm : dogSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : dogSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    have hmemAuth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
      twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    have hread64Auth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
      twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        solcFreePtrMem_read64
    obtain ⟨_, _, hswitch⟩ :=
      RD.dogFileIlkClipToSwitch hpatch hreach hsz100 hsize hauthSolc
    by_cases hwhatClip : fileIlkClipWhat I = fileIlkClipClipBytes
    · have hwordClip :
          fileIlkClipWhatWord I = ABI.bytesToWord fileIlkClipClipBytes :=
        fileIlkClipWhatWord_eq_of_bytes_eq (by omega) hwhatClip
      by_cases hcodeSize :
          Reasoning.Theory.extCodeSizeWord σ_evm (fileIlkClipClipKey I) = ⟨0⟩
      · have hrev := RD.dogFileIlkClipNoCodeRevert
          (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
          hpatch hswitch hwordClip hmemAuth hread64Auth hcodeSize (by simp)
        have hcodeSizeSolm :
            Reasoning.Theory.extCodeSizeWord σ_solm (fileIlkClipClipKey I) = ⟨0⟩ :=
          fileIlkClipCodeSize_zero_accountMapEquiv hAccounts hcodeSize
        have hclipNoCode :
            (UInt256.ofNat
              (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
          fileIlkClipCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody (config v) (contract v) evm0 locals
              fileIlkClipTransition.body .reverted := by
          simpa [evm0, locals] using
            (fileIlkClipNoCodeSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hwhatClip hclipNoCode)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hcodeSizeNe :
            Reasoning.Theory.extCodeSizeWord σ_evm (fileIlkClipClipKey I) ≠
              ⟨0⟩ :=
          hcodeSize
        have hcodeSizeSolmNe :
            Reasoning.Theory.extCodeSizeWord σ_solm (fileIlkClipClipKey I) ≠
              ⟨0⟩ :=
          fileIlkClipCodeSize_ne_accountMapEquiv hAccounts hcodeSizeNe
        have hclipCode :
            0 < (UInt256.ofNat
              (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (fileIlkClipClip I)).option 0 (fun acc => acc.code.size))).toNat :=
          fileIlkClipCode_pos_of_codeSize_ne (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolmNe
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨cA', σ', z, out, A', _k', _C', rd2582, hcallEvmRaw, hosz⟩ :=
            RD.dogFileIlkClipPostStaticcall
              (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
              hpatch hswitch hwordClip hmemAuth hread64Auth hcodeSizeNe hdepthLt
              (by simp)
          let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evmPostEvm :=
            { evmEvm with accountMap := σ', substate := A', createdAccounts := cA' }
          have hcallEvm :
              typedCallViaEVM (config v) evmEvm (EVM.address (fileIlkClipClip I))
                "ilk" 0 [] (z, evmPostEvm, out) false := by
            simpa [evmEvm, evmPostEvm] using hcallEvmRaw
          obtain ⟨σSolmPost, ASolmPost, hcallSolmRaw, hStateCallRaw⟩ :=
            typedCallViaEVM_initState_EVMStateEquiv hcallEvm
              (by simp [evmEvm, evmSolm, evmPostEvm, initState]) hAccounts
          let evmPostSolm :=
            { evmSolm with
              accountMap := σSolmPost, substate := ASolmPost, createdAccounts := cA' }
          have hcallSolm :
              typedCallViaEVM (config v) evmSolm (EVM.address (fileIlkClipClip I))
                "ilk" 0 [] (z, evmPostSolm, out) false := by
            simpa [evmPostSolm] using hcallSolmRaw
          have hStateCall : EVMStateEquiv evmPostEvm evmPostSolm := by
            simpa [evmPostEvm, evmPostSolm] using hStateCallRaw
          cases z
          · simp only [Bool.false_eq_true, if_false] at rd2582 hcallSolm
            have hrev := RD.dogFileIlkClipCallFailure hpatch rd2582 hosz (by simp)
            have hbody :
                ExecTransitionBody (config v) (contract v) evmSolm locals
                  fileIlkClipTransition.body .reverted := by
              simpa [evmSolm, locals] using
                (fileIlkClipCallFailureSourceBody (v := v) (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) (evmCall := evmPostSolm) (out := out)
                  hwv hauthSolm hwhatClip hclipCode hcallSolm)
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · simp only [Bool.true_eq_false, if_true] at rd2582 hcallSolm
            obtain ⟨_, _, rd2600⟩ :=
              RD.dogFileIlkClipCallSuccessToDecode hpatch rd2582 (by simp)
            by_cases hlo : 32 ≤ out.size
            · have hpostMemSize :
                  (fileIlkClipPostCallMem
                    (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem) out).size =
                    160 :=
                fileIlkClipPostCallMem_size_long hmemAuth hlo hosz
              have hpostRead64 :
                  (fileIlkClipPostCallMem
                    (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem) out).readWithPadding
                      64 32 =
                    UInt256.toByteArray ⟨128⟩ :=
                fileIlkClipPostCallMem_read64_long hmemAuth hread64Auth hlo hosz
              obtain ⟨_, _, rd2623⟩ :=
                RD.dogFileIlkClipReturnDecodeOk hpatch rd2600 hmemAuth hread64Auth
                  hlo hosz (by simp)
              by_cases hretMatch :
                  uInt256OfByteArray (out.extract 0 32) = fileIlkClipIlkWord I
              · have hrdret := RD.dogFileIlkClipSuccessStop hpatch rd2623 hretMatch
                  hperm hpostMemSize hpostRead64
                have hdecRet :
                    (config v).externalABI.decode? "ilk" out =
                      some [fileIlkClipIlkValue I] := by
                  have hdecRaw := fileIlkClipDecode_ilk_return_ok (v := v) hlo
                  simpa [fileIlkClipDecodedReturn_eq_ilkValue (I := I) (out := out)
                    hsz100 hretMatch] using hdecRaw
                let actualSlot := solcMappingSlot ⟨1⟩ (fileIlkClipIlkWord I)
                let sourceSlot := fileIlkClipSlotFor I
                let evm1 := Solm.EVM.storageStore evmPostSolm
                  evmPostSolm.executionEnv.codeOwner sourceSlot
                  (setAddressOffset0Word
                    (Solm.EVM.storageLoad evmPostSolm evmPostSolm.executionEnv.codeOwner
                      sourceSlot)
                    (fileIlkClipClipKey I))
                have hslotEq : actualSlot = sourceSlot := by
                  simpa [actualSlot, sourceSlot] using
                    (fileIlkClipSlotFor_eq (I := I) hsz100).symm
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm locals
                      fileIlkClipTransition.body
                      (.returned
                        { contract := contract v,
                          locals := fileIlkClipLocalsClipIlk I (fileIlkClipIlkValue I) }
                        evm1 none) := by
                  simpa [evmSolm, locals, evm1] using
                    (fileIlkClipSuccessSourceBody (v := v) (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) (evmCall := evmPostSolm) (out := out)
                      hwv hsz100 hauthSolm hwhatClip hclipCode hcallSolm hdecRet)
                let evmPostStoreEvm := Solm.EVM.storageStore evmPostEvm
                  evmPostEvm.executionEnv.codeOwner actualSlot
                  (setAddressOffset0Word
                    (Solm.EVM.storageLoad evmPostEvm evmPostEvm.executionEnv.codeOwner
                      actualSlot)
                    (fileIlkClipClipKey I))
                have hloadEq :=
                  hStateCall.storageLoad_codeOwner actualSlot
                have hvalueEq :
                    setAddressOffset0Word
                        (Solm.EVM.storageLoad evmPostEvm
                          evmPostEvm.executionEnv.codeOwner actualSlot)
                        (fileIlkClipClipKey I) =
                      setAddressOffset0Word
                        (Solm.EVM.storageLoad evmPostSolm
                          evmPostSolm.executionEnv.codeOwner actualSlot)
                        (fileIlkClipClipKey I) := by
                  rw [hloadEq]
                have hStateStore : EVMStateEquiv evmPostStoreEvm evm1 := by
                  simpa [evmPostStoreEvm, evm1, actualSlot, sourceSlot, hslotEq] using
                    hStateCall.storageStore_codeOwner actualSlot hvalueEq
                have hcreated :
                    (cA', sstoreAccountMap I.codeOwner σ' actualSlot
                      (setAddressOffset0Word (solcSlotWord σ' I actualSlot)
                        (fileIlkClipClipKey I))).1 = evm1.createdAccounts := by
                  simp [evm1, evmPostSolm, storageStore_createdAccounts]
                have haccounts :
                    accountMapEquiv
                      (sstoreAccountMap I.codeOwner σ' actualSlot
                        (setAddressOffset0Word (solcSlotWord σ' I actualSlot)
                          (fileIlkClipClipKey I)))
                      evm1.accountMap := by
                  have hacc := hStateStore.accountMap
                  simpa [evmPostStoreEvm, evmPostEvm, evm1, actualSlot, sourceSlot,
                    hslotEq, storageStore_accountMap, solcSlotWord, Solm.EVM.storageLoad,
                    State.lookupAccount, Account.lookupStorage, initState] using hacc
                exact hrdret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode
                  hbody hcreated haccounts henc
              · have hrev := RD.dogFileIlkClipMismatchRevert hpatch rd2623 hretMatch
                  hpostMemSize hpostRead64 (by simp)
                have hdecRet :
                    (config v).externalABI.decode? "ilk" out =
                      some [.fixedBytes bytes32Width
                        (EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32)))] :=
                  fileIlkClipDecode_ilk_return_ok (v := v) hlo
                have hneqValue :
                    (fileIlkClipIlkValue I : Value) ≠
                      .fixedBytes bytes32Width
                        (EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32))) :=
                  fileIlkClipDecodedReturn_ne_ilkValue hsz100 hretMatch
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm locals
                      fileIlkClipTransition.body .reverted := by
                  simpa [evmSolm, locals] using
                    (fileIlkClipMismatchSourceBody (v := v) (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) (evmCall := evmPostSolm) (out := out)
                      (clipIlkBytes :=
                        EVM.Word.toBytesBE (uInt256OfByteArray (out.extract 0 32)))
                      hwv hauthSolm hwhatClip hclipCode hcallSolm hdecRet hneqValue)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hshortRet : out.size < 32 := Nat.lt_of_not_ge hlo
              have hrev := RD.dogFileIlkClipReturnDecodeShortReverts hpatch rd2600
                hmemAuth hread64Auth hshortRet hosz (by simp)
              have hdecRet : (config v).externalABI.decode? "ilk" out = none :=
                fileIlkClipDecode_ilk_return_none_short (v := v) hshortRet
              have hbody :
                  ExecTransitionBody (config v) (contract v) evmSolm locals
                    fileIlkClipTransition.body .reverted := by
                simpa [evmSolm, locals] using
                  (fileIlkClipDecodeRevertSourceBody (v := v) (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) (evmCall := evmPostSolm) (out := out)
                    hwv hauthSolm hwhatClip hclipCode hcallSolm hdecRet)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdepth1024 : I.depth = 1024 := by
            apply Fin.ext
            have hlt := I.depth.isLt
            rw [not_lt] at hdepthLt
            omega
          have hrev := RD.dogFileIlkClipStaticcallDepthLimitRevert
            (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
            hpatch hswitch hwordClip hmemAuth hread64Auth hcodeSizeNe hdepth1024
            (by simp)
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evmCall :=
            { evm0 with
              substate := (evm0.addAccessedAccount (EVM.address (fileIlkClipClip I))).substate }
          have hcallDepth :
              typedCallViaEVM (config v) evm0 (EVM.address (fileIlkClipClip I))
                "ilk" 0 [] (false, evmCall, ByteArray.empty) false := by
            simpa [evm0, evmCall, initState] using
              (callNotMade_depthLimit (cfg := config v) (evm := evm0)
                (tgt := EVM.address (fileIlkClipClip I)) (name := "ilk")
                (args := []) (callPerm := false)
                (fileIlkClipEncode_eq (v := v) hmemAuth)
                (by simpa [evm0, initState] using hdepth1024))
          have hbody :
              ExecTransitionBody (config v) (contract v) evm0 locals
                fileIlkClipTransition.body .reverted := by
            simpa [evm0, locals] using
              (fileIlkClipCallFailureSourceBody (v := v) (cA := cA) (gh := gh)
                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) (evmCall := evmCall) (out := ByteArray.empty)
                hwv hauthSolm hwhatClip hclipCode hcallDepth)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hnotClipWord :
          fileIlkClipWhatWord I ≠ ABI.bytesToWord fileIlkClipClipBytes :=
        fileIlkClipWhatWord_ne_of_bytes_ne (by omega) hwhatClip
          fileIlkClipClipBytes_length
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evm0 locals
            fileIlkClipTransition.body .reverted := by
        simpa [evm0, locals] using
          (fileIlkClipUnrecognizedSourceBody (v := v) (cA := cA) (gh := gh)
            (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hwhatClip)
      have hrev := RD.dogFileIlkClipUnrecognizedRevert
        (v := v) (code := code) (clip := fileIlkClipClipKey I)
        (what := fileIlkClipWhatWord I) (ilk := fileIlkClipIlkWord I)
        (ret := ⟨313⟩) (sel := sel) (R := [])
        hpatch hswitch hnotClipWord hmemAuth hread64Auth (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : dogSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody :
        ExecTransitionBody (config v) (contract v) evm0 locals fileIlkClipTransition.body
          .reverted := by
      have hguard := dogAuthGuardEval_false (v := v) (cA := cA) (gh := gh)
        (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fileIlkClipLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config v) (solm := { contract := contract v, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .ite (.binary .eq (.var "what") clipParamLit)
            (checkedExternalCallStmts (.var "clip") "ilk" (.intLit 0) [] "clipIlk"
              (perm := false) ++
              [ .require (.binary .eq (.var "ilk") (.var "clipIlk")),
                .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ])
            [ .require (.boolLit false) ] ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, fileIlkClipTransition, nonpayable, auth, evm0, locals]
        using ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    have hrev := RD.dogFileIlkClipAuthRevert hpatch hreach hsz100 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem dogFileIlkClipBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 10) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some fileIlkClipTransition :=
    dogDispatchFileIlkClip hsel
  have hreach := dogReachFileIlkClipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · exact dogFileIlkClipBodyCoreOk hpatch hcode hwv hperm hsz100 hsize hdispatch
      (dogDecode_fileIlkClip_ok (v := v) hsz100) hreach hAccounts
  · exact dogFileIlkClipBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog

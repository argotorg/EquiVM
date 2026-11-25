import Benchmarks.Midnight.ScalarDecode

/-! Two-scalar calldata decoding for Midnight's nested mapping getters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the static two-word ABI head with solc's signed size check.
theorem decodeSolcPair_none_check {cd : ByteArray} (table : List (Nat × List CalldataPlan))
    (name0 name1 : Ident) (ty0 ty1 : ElemType) (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 64 = true) :
    decodeCalldataWithMode (.solc08Calldata table) [name0, name1] [.elem ty0, .elem ty1] cd =
      none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, hcheck, if_true]

theorem decodeSolcPair_eq {cd : ByteArray} (table : List (Nat × List CalldataPlan))
    (name0 name1 : Ident) (ty0 ty1 : ElemType) (h68 : 68 ≤ cd.size)
    (hdefer0 : (((table.find? (fun entry ↦ entry.1 ==
      (ABI.bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] |>.headD
        {}).deferErrors.contains [] = false)
    (hdefer1 : (((table.find? (fun entry ↦ entry.1 ==
      (ABI.bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] |>.tail.headD
        {}).deferErrors.contains [] = false)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 64 = false) :
    decodeCalldataWithMode (.solc08Calldata table) [name0, name1] [.elem ty0, .elem ty1] cd =
      (do
        let v0 ← decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0
        let v1 ← decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0
        pure (((∅ : Store).insert name0 v0.1).insert name1 v1.1)) := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (off : Nat) (hoff : off + 32 ≤ cd.size) :
      ((cd.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  have hread0 : ABI.Solc08Calldata.solcReadBytes cd.toList 4 32 =
      (cd.toList.drop 4).take 32 := by
    simp only [ABI.Solc08Calldata.solcReadBytes,
      show 4 % EVM.wordModulus = 4 from rfl, htake 4 (by omega), Nat.sub_self,
      List.replicate_zero, List.append_nil]
  have hread1 : ABI.Solc08Calldata.solcReadBytes cd.toList 36 32 =
      (cd.toList.drop 36).take 32 := by
    simp only [ABI.Solc08Calldata.solcReadBytes,
      show 36 % EVM.wordModulus = 36 from rfl, htake 36 h68, Nat.sub_self,
      List.replicate_zero, List.append_nil]
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, hcheck,
    ABI.Solc08Calldata.decodeFields?, ABI.Solc08Calldata.stride?]
  simp only [ABI.Solc08Calldata.retainFailure, hdefer0, hdefer1, Bool.false_eq_true, if_false,
    ABI.Solc08Calldata.decodeValue?,
    show ABI.Solc08Calldata.solcAdd 4 0 = 4 from rfl,
    show ABI.Solc08Calldata.solcAdd 4 32 = 36 from rfl, hread0, hread1]
  cases decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 <;>
    cases decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0 <;> rfl

theorem midnightPlans_noNextDefer (selector : Nat) :
    ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == selector)).map Prod.snd |>.getD [] |>.tail.headD
        {}).deferErrors.contains [] = false := by
  cases h : (0xac9650d8 == selector) <;> simp [List.find?, h]

theorem midnightDecodePair_none_check {cd : ByteArray} (name0 name1 : Ident)
    (ty0 ty1 : ElemType) (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 64 = true) :
    config.externalABI.decodeCalldata? [name0, name1] [.elem ty0, .elem ty1] cd = none := by
  change Model.decodeCalldata [name0, name1] [.elem ty0, .elem ty1] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcPair_none_check _ name0 name1 ty0 ty1 h4 hcheck]
  rfl

theorem midnightDecodePair_none_short {cd : ByteArray} (name0 name1 : Ident)
    (ty0 ty1 : ElemType) (h4 : 4 ≤ cd.size) (hshort : cd.size < 68)
    (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name0, name1] [.elem ty0, .elem ty1] cd = none :=
  midnightDecodePair_none_check name0 name1 ty0 ty1 h4
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := true)
      (solcDecodeLenCheckShort_4_64 h4 hshort hsize))

theorem midnightDecodePair_none_huge {cd : ByteArray} (name0 name1 : Ident)
    (ty0 ty1 : ElemType) (hbig : 2^255 + 4 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name0, name1] [.elem ty0, .elem ty1] cd = none :=
  midnightDecodePair_none_check name0 name1 ty0 ty1 (by omega)
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := true)
      (solcDecodeLenCheckHuge_4_64 hbig hsize))

theorem midnightDecodePair_some {cd : ByteArray} {name0 name1 : Ident}
    {ty0 ty1 : ElemType} {value0 value1 : Value}
    (hn0m : name0 ≠ "market") (hn0o : name0 ≠ "offer")
    (hn1m : name1 ≠ "market") (hn1o : name1 ≠ "offer")
    (hdecode : decodeCalldataWithMode Model.calldataMode [name0, name1] [.elem ty0, .elem ty1]
      cd = some (((∅ : Store).insert name0 value0).insert name1 value1)) :
    config.externalABI.decodeCalldata? [name0, name1] [.elem ty0, .elem ty1] cd =
      some (((∅ : Store).insert name0 value0).insert name1 value1) := by
  change Model.decodeCalldata [name0, name1] [.elem ty0, .elem ty1] cd = _
  unfold Model.decodeCalldata
  rw [hdecode]
  simp [Model.inputSizesFit, hn0m, hn0o, hn1m, hn1o]

-- LIBRARY CANDIDATE: decode a present bytes32 word at any calldata offset.
theorem decodeBytes32Word {cd : ByteArray} {off : Nat} (hlen : off + 32 ≤ cd.size) :
    decodeABIValue? abiBytes32 ((cd.toList.drop off).take 32) 0 =
      some (wordBytes32Value (calldataWord cd off), 32) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  rw [decodeABIValue_bytes32_ok
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake)]
  have hw := toBytesBE_bytesToWord_of_length htake
  rw [decode_word_at_eq_any cd off hlen] at hw
  simp only [List.drop_zero, List.take_take, Nat.min_self, wordBytes32Value, hw]

-- LIBRARY CANDIDATE: decode a canonical address word at any calldata offset.
theorem decodeAddressWord {cd : ByteArray} {off : Nat} (hlen : off + 32 ≤ cd.size)
    (hcanon : (calldataWord cd off).toNat < EVM.addressModulus) :
    decodeABIValue? (.elem .address) ((cd.toList.drop off).take 32) 0 =
      some (.address (AccountAddress.ofNat (calldataWord cd off).toNat), 32) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeABIValue_address_ok (by
    simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlist]; omega) (by
    simpa only [List.drop_zero, List.take_take, Nat.min_self,
      decode_word_at_eq_any cd off hlen] using hcanon)]
  simp only [List.drop_zero, List.take_take, Nat.min_self, decode_word_at_eq_any cd off hlen]

-- LIBRARY CANDIDATE: decode a present uint256 at any calldata offset.
theorem decodeUint256Word {cd : ByteArray} {off : Nat} (hlen : off + 32 ≤ cd.size) :
    decodeABIValue? abiUInt256 ((cd.toList.drop off).take 32) 0 =
      some (.int (Int.ofNat (calldataWord cd off).toNat), 32) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeABIValue_uint256_ok (by
    simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlist]; omega)]
  simp only [List.drop_zero, List.take_take, Nat.min_self, decode_word_at_eq_any cd off hlen]

theorem decodeAddressWord_none {cd : ByteArray} {off : Nat} (hlen : off + 32 ≤ cd.size)
    (hnc : ¬ (calldataWord cd off).toNat < EVM.addressModulus) :
    decodeABIValue? (.elem .address) ((cd.toList.drop off).take 32) 0 = none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  apply decodeABIValue_address_none_noncanon
  · simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlist]; omega
  · simpa only [List.drop_zero, List.take_take, Nat.min_self,
      decode_word_at_eq_any cd off hlen] using hnc

theorem midnightDecodeBytes32Address {cd : ByteArray} (name0 name1 : Ident)
    (hn0m : name0 ≠ "market") (hn0o : name0 ≠ "offer")
    (hn1m : name1 ≠ "market") (hn1o : name1 ≠ "offer")
    (h68 : 68 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (hcanon : (calldataWord cd 36).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [name0, name1] [abiBytes32, .elem .address] cd =
      some (((∅ : Store).insert name0 (wordBytes32Value (calldataWord cd 4))).insert name1
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  apply midnightDecodePair_some hn0m hn0o hn1m hn1o
  unfold Model.calldataMode
  rw [decodeSolcPair_eq _ name0 name1 (.bytes abiBytes32Width) .address h68
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _)
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := false)
      (solcDecodeLenCheckOk_4_64 h68 hhi hsize))]
  rw [decodeBytes32Word (by omega), decodeAddressWord h68 hcanon]
  rfl

theorem midnightDecodeBytes32Address_none_noncanon {cd : ByteArray} (name0 name1 : Ident)
    (h68 : 68 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (hnc : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [name0, name1] [abiBytes32, .elem .address] cd = none := by
  change Model.decodeCalldata [name0, name1] [abiBytes32, .elem .address] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcPair_eq _ name0 name1 (.bytes abiBytes32Width) .address h68
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _)
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := false)
      (solcDecodeLenCheckOk_4_64 h68 hhi hsize))]
  rw [decodeBytes32Word (by omega), decodeAddressWord_none h68 hnc]
  rfl

theorem midnightDecodePair_ok {cd : ByteArray} (name0 name1 : Ident)
    {ty0 ty1 : ElemType} {value0 value1 : Value}
    (hn0m : name0 ≠ "market") (hn0o : name0 ≠ "offer")
    (hn1m : name1 ≠ "market") (hn1o : name1 ≠ "offer")
    (h68 : 68 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (h0 : decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 = some (value0, 32))
    (h1 : decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0 = some (value1, 32)) :
    config.externalABI.decodeCalldata? [name0, name1] [.elem ty0, .elem ty1] cd =
      some (((∅ : Store).insert name0 value0).insert name1 value1) := by
  apply midnightDecodePair_some hn0m hn0o hn1m hn1o
  unfold Model.calldataMode
  rw [decodeSolcPair_eq _ name0 name1 ty0 ty1 h68
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _)
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := false)
      (solcDecodeLenCheckOk_4_64 h68 hhi hsize)), h0, h1]
  rfl

theorem midnightDecodePair_none_left {cd : ByteArray} (name0 name1 : Ident)
    (ty0 ty1 : ElemType)
    (h68 : 68 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (h0 : decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 = none) :
    config.externalABI.decodeCalldata? [name0, name1] [.elem ty0, .elem ty1] cd = none := by
  change Model.decodeCalldata [name0, name1] [.elem ty0, .elem ty1] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcPair_eq _ name0 name1 ty0 ty1 h68
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _)
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := false)
      (solcDecodeLenCheckOk_4_64 h68 hhi hsize)), h0]
  rfl

theorem midnightDecodePair_none_right {cd : ByteArray} (name0 name1 : Ident)
    (ty0 ty1 : ElemType)
    (h68 : 68 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (h1 : decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0 = none) :
    config.externalABI.decodeCalldata? [name0, name1] [.elem ty0, .elem ty1] cd = none := by
  change Model.decodeCalldata [name0, name1] [.elem ty0, .elem ty1] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcPair_eq _ name0 name1 ty0 ty1 h68
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _)
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := false)
      (solcDecodeLenCheckOk_4_64 h68 hhi hsize)), h1]
  cases decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 <;> rfl

end Benchmarks.Midnight

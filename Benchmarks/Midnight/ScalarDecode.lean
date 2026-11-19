import Benchmarks.Midnight.Entry

/-! Scalar ABI decoding, shared by the mapping getters and configuration entry points. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the two EVM signed-comparison presentations agree.
theorem sltBool_signed (a b : UInt256) :
    UInt256.sltBool a b = decide (EVM.signed a < EVM.signed b) := by
  have haBound := a.val.isLt
  have hbBound := b.val.isLt
  change a.toNat < 2^256 at haBound
  change b.toNat < 2^256 at hbBound
  change (if 2^255 ≤ a.toNat then
      (if 2^255 ≤ b.toNat then decide (a.toNat < b.toNat) else true)
    else (if 2^255 ≤ b.toNat then false else decide (a.toNat < b.toNat))) =
    decide ((if a.toNat < 2^255 then (a.toNat : Int) else (a.toNat : Int) - 2^256) <
      (if b.toNat < 2^255 then (b.toNat : Int) else (b.toNat : Int) - 2^256))
  by_cases ha : a.toNat < 2^255 <;> by_cases hb : b.toNat < 2^255
  · simp only [ha, hb, not_le_of_gt ha, not_le_of_gt hb, if_pos, if_false]
    congr 1
    apply propext
    omega
  · simp only [ha, hb, not_le_of_gt ha, Nat.le_of_not_gt hb, if_pos, if_false]
    rw [decide_eq_false (by omega)]
  · simp only [ha, hb, Nat.le_of_not_gt ha, not_le_of_gt hb, if_pos, if_false]
    rw [decide_eq_true (by omega)]
  · simp only [ha, hb, Nat.le_of_not_gt ha, Nat.le_of_not_gt hb, if_pos, if_false]
    congr 1
    apply propext
    omega

-- LIBRARY CANDIDATE: translate an EVM comparison into the calldata decoder's Boolean.
theorem solcSLT_of_check {a b : UInt256} {bit : Bool}
    (h : UInt256.slt a b = UInt256.fromBool bit) :
    ABI.Solc08Calldata.solcSLT a.toNat b.toNat = bit := by
  unfold ABI.Solc08Calldata.solcSLT
  change decide (EVM.signed (UInt256.ofNat a.toNat) <
    EVM.signed (UInt256.ofNat b.toNat)) = bit
  rw [u256_ofNat_toNat, u256_ofNat_toNat, ← sltBool_signed]
  change UInt256.fromBool _ = UInt256.fromBool bit at h
  cases hc : UInt256.sltBool a b <;> cases bit <;>
    simp_all [UInt256.fromBool, Bool.toUInt256]
  all_goals first
    | exact (by decide : (UInt256.ofNat 0 : UInt256) ≠ UInt256.ofNat 1) h
    | exact (by decide : (UInt256.ofNat 1 : UInt256) ≠ UInt256.ofNat 0) h

theorem solcSLT_sub4_of_check {size : Nat} {need : UInt256} {bit : Bool}
    (h : UInt256.slt (UInt256.sub (UInt256.ofNat size) ⟨4⟩) need = UInt256.fromBool bit) :
    ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub size 4) need.toNat = bit :=
  solcSLT_of_check h

-- LIBRARY CANDIDATE: scalar decode failure for any solc 0.8 calldata plan table.
theorem decodeSolcScalar_none_check {cd : ByteArray} (table : List (Nat × List CalldataPlan)) (name : Ident) (ty : ElemType)
    (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 32 = true) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.elem ty] cd = none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and,
    ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    Bool.false_eq_true, abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind,
    hcheck, if_true]

-- LIBRARY CANDIDATE: scalar decoding only depends on the top-level error policy.
theorem decodeSolcScalar_eq {cd : ByteArray} (table : List (Nat × List CalldataPlan)) (name : Ident) (ty : ElemType)
    (h36 : 36 ≤ cd.size)
    (hdefer : (((table.find? (fun entry ↦ entry.1 ==
      (ABI.bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] |>.headD
        {}).deferErrors.contains [] = false)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 32 = false) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.elem ty] cd =
      (decodeABIValue? (.elem ty) ((cd.toList.drop 4).take 32) 0).map
        (fun value ↦ (∅ : Store).insert name value.1) := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  have hread : ABI.Solc08Calldata.solcReadBytes cd.toList 4 32 = (cd.toList.drop 4).take 32 := by
    simp only [ABI.Solc08Calldata.solcReadBytes,
      show 4 % EVM.wordModulus = 4 from rfl, htake, Nat.sub_self, List.replicate_zero, List.append_nil]
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and,
    ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, hcheck,
    ABI.Solc08Calldata.decodeFields?, ABI.Solc08Calldata.stride?]
  simp only [ABI.Solc08Calldata.retainFailure]
  rw [hdefer]
  simp only [Bool.false_eq_true, if_false, ABI.Solc08Calldata.decodeValue?,
    show ABI.Solc08Calldata.solcAdd 4 0 = 4 from rfl, hread]
  cases decodeABIValue? (.elem ty) ((cd.toList.drop 4).take 32) 0 <;> rfl


theorem midnightPlans_noTopDefer (selector : Nat) :
    ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == selector)).map Prod.snd |>.getD [] |>.headD
        {}).deferErrors.contains [] = false := by
  cases h : (0xac9650d8 == selector) <;> simp [List.find?, h]

theorem midnightDecodeScalar_some {cd : ByteArray} {name : Ident} {ty : ElemType} {value : Value}
    (hmarket : name ≠ "market") (hoffer : name ≠ "offer")
    (hdecode : decodeCalldataWithMode Model.calldataMode [name] [.elem ty] cd =
      some ((∅ : Store).insert name value)) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd =
      some ((∅ : Store).insert name value) := by
  change Model.decodeCalldata [name] [.elem ty] cd = _
  unfold Model.decodeCalldata
  rw [hdecode]
  simp [Model.inputSizesFit, hmarket, hoffer]

theorem midnightDecodeScalar_none_check {cd : ByteArray} (name : Ident) (ty : ElemType)
    (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 32 = true) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd = none := by
  change Model.decodeCalldata [name] [.elem ty] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcScalar_none_check _ name ty h4 hcheck]
  rfl

theorem midnightDecodeScalar_none_short {cd : ByteArray} (name : Ident) (ty : ElemType)
    (h4 : 4 ≤ cd.size) (hshort : cd.size < 36) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd = none :=
  midnightDecodeScalar_none_check name ty h4
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true)
      (solcDecodeLenCheckShort_4_32 h4 hshort hsize))

theorem midnightDecodeScalar_none_huge {cd : ByteArray} (name : Ident) (ty : ElemType)
    (hbig : 2^255 + 4 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd = none :=
  midnightDecodeScalar_none_check name ty (by omega)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true)
      (solcDecodeLenCheckHuge_4_32 hbig hsize))

theorem midnightDecodeUint256 {cd : ByteArray} (name : Ident)
    (hmarket : name ≠ "market") (hoffer : name ≠ "offer")
    (h36 : 36 ≤ cd.size) (hbig : cd.size < calldataLimit) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name] [abiUInt256] cd =
      some ((∅ : Store).insert name (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  apply midnightDecodeScalar_some hmarket hoffer
  unfold Model.calldataMode
  rw [decodeSolcScalar_eq _ name (.int (.uint ⟨256, by decide⟩)) h36
    (midnightPlans_noTopDefer _)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false)
      (solcDecodeLenCheckOk_4_32 h36 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  rw [decodeABIValue_uint256_ok
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake)]
  simp only [Option.map, List.drop_zero, List.take_take, Nat.min_self,
    decode_word_at_eq_any cd 4 h36]

theorem midnightDecodeBytes32 {cd : ByteArray} (name : Ident)
    (hmarket : name ≠ "market") (hoffer : name ≠ "offer")
    (h36 : 36 ≤ cd.size) (hbig : cd.size < calldataLimit) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name] [abiBytes32] cd =
      some ((∅ : Store).insert name
        (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (calldataWord cd 4)))) := by
  apply midnightDecodeScalar_some hmarket hoffer
  unfold Model.calldataMode
  rw [decodeSolcScalar_eq _ name (.bytes abiBytes32Width) h36
    (midnightPlans_noTopDefer _)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false)
      (solcDecodeLenCheckOk_4_32 h36 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  rw [decodeABIValue_bytes32_ok
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake)]
  have hw := toBytesBE_bytesToWord_of_length htake
  rw [decode_word_at_eq_any cd 4 h36] at hw
  simp only [Option.map, List.drop_zero, List.take_take, Nat.min_self, hw]

theorem midnightDecodeAddress {cd : ByteArray} (name : Ident)
    (hmarket : name ≠ "market") (hoffer : name ≠ "offer")
    (h36 : 36 ≤ cd.size) (hbig : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [name] [.elem .address] cd =
      some ((∅ : Store).insert name
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  apply midnightDecodeScalar_some hmarket hoffer
  unfold Model.calldataMode
  rw [decodeSolcScalar_eq _ name .address h36 (midnightPlans_noTopDefer _)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false)
      (solcDecodeLenCheckOk_4_32 h36 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (((cd.toList.drop 4).take 32).drop 0 |>.take 32).length = 32 := by
    simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlen]; omega
  rw [decodeABIValue_address_ok htake (by
    simpa only [List.drop_zero, List.take_take, Nat.min_self,
      decode_word_at_eq_any cd 4 h36] using hcanon)]
  simp only [Option.map, List.drop_zero, List.take_take, Nat.min_self,
    decode_word_at_eq_any cd 4 h36]

theorem midnightDecodeAddress_none_noncanon {cd : ByteArray} (name : Ident)
    (h36 : 36 ≤ cd.size) (hbig : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [name] [.elem .address] cd = none := by
  change Model.decodeCalldata [name] [.elem .address] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcScalar_eq _ name .address h36 (midnightPlans_noTopDefer _)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false)
      (solcDecodeLenCheckOk_4_32 h36 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (((cd.toList.drop 4).take 32).drop 0 |>.take 32).length = 32 := by
    simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlen]; omega
  rw [decodeABIValue_address_none_noncanon htake (by
    simpa only [List.drop_zero, List.take_take, Nat.min_self,
      decode_word_at_eq_any cd 4 h36] using hnc)]
  rfl

end Benchmarks.Midnight

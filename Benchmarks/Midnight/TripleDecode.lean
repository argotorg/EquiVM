import Benchmarks.Midnight.PairDecode

/-! Three-scalar calldata decoding with solc's signed head-size guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the static three-word ABI head with solc's signed size check.
theorem decodeSolcTriple_none_check {cd : ByteArray} (table : List (Nat × List CalldataPlan))
    (name0 name1 name2 : Ident) (ty0 ty1 ty2 : ElemType) (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 96 = true) :
    decodeCalldataWithMode (.solc08Calldata table) [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, hcheck, if_true]

theorem decodeSolcTriple_eq {cd : ByteArray} (table : List (Nat × List CalldataPlan))
    (name0 name1 name2 : Ident) (ty0 ty1 ty2 : ElemType) (h100 : 100 ≤ cd.size)
    (hdefer0 : (((table.find? (fun entry ↦ entry.1 ==
      (ABI.bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] |>.headD
        {}).deferErrors.contains [] = false)
    (hdefer1 : (((table.find? (fun entry ↦ entry.1 ==
      (ABI.bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] |>.tail.headD
        {}).deferErrors.contains [] = false)
    (hdefer2 : (((table.find? (fun entry ↦ entry.1 ==
      (ABI.bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] |>.tail.tail.headD
        {}).deferErrors.contains [] = false)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 96 = false) :
    decodeCalldataWithMode (.solc08Calldata table) [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      (do
        let v0 ← decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0
        let v1 ← decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0
        let v2 ← decodeABIValue? (.elem ty2) ((cd.toList.drop 68).take 32) 0
        pure ((((∅ : Store).insert name0 v0.1).insert name1 v1.1).insert name2 v2.1)) := by
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
      show 36 % EVM.wordModulus = 36 from rfl, htake 36 (by omega), Nat.sub_self,
      List.replicate_zero, List.append_nil]
  have hread2 : ABI.Solc08Calldata.solcReadBytes cd.toList 68 32 =
      (cd.toList.drop 68).take 32 := by
    simp only [ABI.Solc08Calldata.solcReadBytes,
      show 68 % EVM.wordModulus = 68 from rfl, htake 68 h100, Nat.sub_self,
      List.replicate_zero, List.append_nil]
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, hcheck,
    ABI.Solc08Calldata.decodeFields?, ABI.Solc08Calldata.stride?]
  simp only [ABI.Solc08Calldata.retainFailure, hdefer0, hdefer1, hdefer2, Bool.false_eq_true, if_false,
    ABI.Solc08Calldata.decodeValue?,
    show ABI.Solc08Calldata.solcAdd 4 0 = 4 from rfl,
    show ABI.Solc08Calldata.solcAdd 4 32 = 36 from rfl,
    show ABI.Solc08Calldata.solcAdd 4 64 = 68 from rfl, hread0, hread1, hread2]
  cases decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 <;>
    cases decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0 <;>
    cases decodeABIValue? (.elem ty2) ((cd.toList.drop 68).take 32) 0 <;> rfl

theorem midnightPlans_noThirdDefer (selector : Nat) :
    ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == selector)).map Prod.snd |>.getD [] |>.tail.tail.headD
        {}).deferErrors.contains [] = false := by
  cases h : (0xac9650d8 == selector) <;> simp [List.find?, h]

theorem midnightDecodeTriple_none_check {cd : ByteArray} (name0 name1 name2 : Ident)
    (ty0 ty1 ty2 : ElemType) (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 96 = true) :
    config.externalABI.decodeCalldata? [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      none := by
  change Model.decodeCalldata [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcTriple_none_check _ name0 name1 name2 ty0 ty1 ty2 h4 hcheck]
  rfl

theorem midnightDecodeTriple_none_short {cd : ByteArray} (name0 name1 name2 : Ident)
    (ty0 ty1 ty2 : ElemType) (h4 : 4 ≤ cd.size) (hshort : cd.size < 100)
    (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      none :=
  midnightDecodeTriple_none_check name0 name1 name2 ty0 ty1 ty2 h4
    (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := true)
      (entrySizeCheck_short h4 hshort (by decide) hsize))

theorem midnightDecodeTriple_none_huge {cd : ByteArray} (name0 name1 name2 : Ident)
    (ty0 ty1 ty2 : ElemType) (hbig : calldataLimit ≤ cd.size) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      none :=
  midnightDecodeTriple_none_check name0 name1 name2 ty0 ty1 ty2 (by
    have hc : 4 ≤ calldataLimit := by decide
    omega)
    (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := true)
      (entrySizeCheck_huge hbig hsize (by decide)))

theorem midnightDecodeTriple_ok {cd : ByteArray} (name0 name1 name2 : Ident)
    {ty0 ty1 ty2 : ElemType} {value0 value1 value2 : Value}
    (hn0m : name0 ≠ "market") (hn0o : name0 ≠ "offer")
    (hn1m : name1 ≠ "market") (hn1o : name1 ≠ "offer")
    (hn2m : name2 ≠ "market") (hn2o : name2 ≠ "offer")
    (h100 : 100 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (h0 : decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 = some (value0, 32))
    (h1 : decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0 = some (value1, 32))
    (h2 : decodeABIValue? (.elem ty2) ((cd.toList.drop 68).take 32) 0 = some (value2, 32)) :
    config.externalABI.decodeCalldata? [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      some ((((∅ : Store).insert name0 value0).insert name1 value1).insert name2 value2) := by
  change Model.decodeCalldata [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcTriple_eq _ name0 name1 name2 ty0 ty1 ty2 h100
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _) (midnightPlans_noThirdDefer _)
    (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := false)
      (entrySizeCheck_ok h100 hhi hsize)), h0, h1, h2]
  simp [Model.inputSizesFit, hn0m, hn0o, hn1m, hn1o, hn2m, hn2o]

theorem midnightDecodeTriple_none_middle {cd : ByteArray} (name0 name1 name2 : Ident)
    (ty0 ty1 ty2 : ElemType) {value0 : Value}
    (h100 : 100 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (h0 : decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 = some (value0, 32))
    (h1 : decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0 = none) :
    config.externalABI.decodeCalldata? [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      none := by
  change Model.decodeCalldata [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcTriple_eq _ name0 name1 name2 ty0 ty1 ty2 h100
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _) (midnightPlans_noThirdDefer _)
    (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := false)
      (entrySizeCheck_ok h100 hhi hsize)), h0, h1]
  rfl

theorem midnightDecodeTriple_none_left {cd : ByteArray} (name0 name1 name2 : Ident)
    (ty0 ty1 ty2 : ElemType)
    (h100 : 100 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (h0 : decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 = none) :
    config.externalABI.decodeCalldata? [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      none := by
  change Model.decodeCalldata [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcTriple_eq _ name0 name1 name2 ty0 ty1 ty2 h100
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _) (midnightPlans_noThirdDefer _)
    (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := false)
      (entrySizeCheck_ok h100 hhi hsize)), h0]
  rfl

theorem midnightDecodeTriple_none_right {cd : ByteArray} (name0 name1 name2 : Ident)
    (ty0 ty1 ty2 : ElemType) {v0 v1 : Value}
    (h100 : 100 ≤ cd.size) (hhi : cd.size < calldataLimit) (hsize : cd.size < UInt256.size)
    (h0 : decodeABIValue? (.elem ty0) ((cd.toList.drop 4).take 32) 0 = some (v0, 32))
    (h1 : decodeABIValue? (.elem ty1) ((cd.toList.drop 36).take 32) 0 = some (v1, 32))
    (h2 : decodeABIValue? (.elem ty2) ((cd.toList.drop 68).take 32) 0 = none) :
    config.externalABI.decodeCalldata? [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd =
      none := by
  change Model.decodeCalldata [name0, name1, name2] [.elem ty0, .elem ty1, .elem ty2] cd = _
  unfold Model.decodeCalldata Model.calldataMode
  rw [decodeSolcTriple_eq _ name0 name1 name2 ty0 ty1 ty2 h100
    (midnightPlans_noTopDefer _) (midnightPlans_noNextDefer _) (midnightPlans_noThirdDefer _)
    (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := false)
      (entrySizeCheck_ok h100 hhi hsize)), h0, h1, h2]
  rfl

end Benchmarks.Midnight

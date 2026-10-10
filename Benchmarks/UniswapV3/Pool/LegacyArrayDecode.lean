import Benchmarks.UniswapV3.Pool.Calldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATES: legacy dynamic integer arrays, including dirty scalar words.
def calldataWordList (cd : ByteArray) (start : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => calldataWord cd start :: calldataWordList cd (start + 32) n

@[simp] theorem calldataWordList_length (cd : ByteArray) (start n : Nat) :
    (calldataWordList cd start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [calldataWordList, List.length_cons, ih]

theorem calldataWordList_getElem (cd : ByteArray) (start n i : Nat) (hi : i < n) :
    (calldataWordList cd start n)[i]'(by simpa using hi) =
      calldataWord cd (start + 32 * i) := by
  induction n generalizing start i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp only [calldataWordList, List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
      | succ i =>
          simp only [calldataWordList, List.getElem_cons_succ]
          rw [ih (start + 32) i (by omega)]
          congr 1
          omega

theorem decodeABIArrayStaticElems_legacyInt_ok (ty : ABI.IntType) (cd : ByteArray)
    (start n : Nat) (hlen : 4 + start + 32 * n ≤ cd.size) :
    decodeABIArrayStaticElems? (.elem (.int ty)) n 32 (cd.toList.drop 4) start
      .legacySolc05 =
      some ((calldataWordList cd (4 + start) n).map
        (fun w ↦ .int (normalizeInt ty (Int.ofNat w.toNat))), start + 32 * n) := by
  induction n generalizing start with
  | zero => simp only [decodeABIArrayStaticElems?, calldataWordList, List.map_nil,
      Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
      have hread : decodeABIValue? (.elem (.int ty)) (cd.toList.drop 4) start .legacySolc05 =
          some (.int (normalizeInt ty (Int.ofNat (calldataWord cd (4 + start)).toNat)),
            start + 32) := by
        have ht : (((cd.toList.drop 4).drop start).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, List.length_drop, byteArray_toList_eq,
            Array.length_toList]
          change min 32 (cd.size - 4 - start) = 32
          omega
        have h := decodeScalarWord_legacyInt_ok ty ht
        have hw := decode_word_at_eq_any cd (4 + start) (by omega)
        rw [← List.drop_drop] at hw
        rw [hw] at h
        rw [decodeABIValue_scalarWordWithMode_eq (by cases ty <;> rfl)]
        exact h
      rw [decodeABIArrayStaticElems?, hread]
      simp only [bind, Option.bind]
      rw [ih (start + 32) (by omega)]
      simp only [calldataWordList, List.map_cons, Nat.add_assoc, Nat.mul_add, Nat.mul_one,
        if_true, Nat.add_comm 32 (32 * n)]

theorem decodeABIArrayStaticElems_legacyInt_none_short (ty : ABI.IntType)
    (bytes : List UInt8) (start n : Nat) (hstart : start ≤ bytes.length)
    (hshort : bytes.length < start + 32 * n) :
    decodeABIArrayStaticElems? (.elem (.int ty)) n 32 bytes start .legacySolc05 = none := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
      by_cases hh : start + 32 ≤ bytes.length
      · have ht : ((bytes.drop start).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]; omega
        have h := decodeScalarWord_legacyInt_ok ty ht
        have he := (decodeABIValue_scalarWordWithMode_eq
          (mode := .legacySolc05) (bytes := bytes) (start := start)
          (ty := .elem (.int ty)) (by cases ty <;> rfl)).trans h
        rw [decodeABIArrayStaticElems?, he]
        simp only [bind, Option.bind]
        rw [ih (start + 32) hh (by omega)]
        rfl
      · have ht : ¬ ((bytes.drop start).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]; omega
        have h := decodeScalarWord_legacyInt_none_short ty ht
        have he := (decodeABIValue_scalarWordWithMode_eq
          (mode := .legacySolc05) (bytes := bytes) (start := start)
          (ty := .elem (.int ty)) (by cases ty <;> rfl)).trans h
        rw [decodeABIArrayStaticElems?, he]
        rfl

theorem decodeCalldata_legacyIntArray_head (ty : ABI.IntType) (cd : ByteArray) (name : Ident) :
    decodeCalldataWithMode .legacySolc05 [name] [.dynamicArray (.elem (.int ty))] cd =
      if cd.size < 36 then none else
      if 2 ^ 32 < (calldataWord cd 4).toNat then none else
      match decodeABIValue? (.dynamicArray (.elem (.int ty))) (cd.toList.drop 4)
          (calldataWord cd 4).toNat .legacySolc05 with
      | none => none
      | some (value, _) => some ((∅ : Store).insert name value) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead : abiTupleHeadSize? [.dynamicArray (.elem (.int ty))] = some 32 := by
    simp only [abiTupleHeadSize?, isDynamicABIType, if_true, bind, Option.bind]
  simp only [decodeCalldataWithMode, decodeCalldata, ite_self, htlen,
    decodeCalldata.decodeArgs, hhead, bind, Option.bind, List.length_drop]
  by_cases h4 : cd.size < 4
  · simp only [if_pos h4, if_pos (by omega : cd.size < 36)]
  · rw [if_neg h4]
    by_cases h36 : cd.size < 36
    · simp only [if_pos h36, if_pos (by omega : cd.size - 4 < 32)]
    · rw [if_neg h36, if_neg (by omega : ¬ cd.size - 4 < 32)]
      simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add]
      rw [readNat_drop4_zero_eq_calldataWord (by omega)]
      simp only [bind, Option.bind, solcMaxLen, solcMaxLenV1,
        show (4294967296 : Nat) = 2 ^ 32 from rfl]
      by_cases hoff : 2 ^ 32 < (calldataWord cd 4).toNat
      · simp only [if_pos hoff]
      · simp only [if_neg hoff]
        cases decodeABIValue? (.dynamicArray (.elem (.int ty))) (cd.toList.drop 4)
          (calldataWord cd 4).toNat .legacySolc05 with
        | none => rfl
        | some result => rcases result with ⟨value, stop⟩; rfl

def legacyIntArrayValues (ty : ABI.IntType) (cd : ByteArray) (start n : Nat) : List Value :=
  (calldataWordList cd start n).map (fun w ↦ .int (normalizeInt ty (Int.ofNat w.toNat)))

theorem decodeCalldata_legacyIntArray_eq (ty : ABI.IntType) (cd : ByteArray) (name : Ident) :
    decodeCalldataWithMode .legacySolc05 [name] [.dynamicArray (.elem (.int ty))] cd =
      let off := (calldataWord cd 4).toNat
      let n := (calldataWord cd (4 + off)).toNat
      if cd.size < 36 then none else
      if 2 ^ 32 < off then none else
      if cd.size < 4 + off + 32 then none else
      if 2 ^ 32 < n then none else
      if cd.size < 4 + off + 32 + 32 * n then none else
      some ((∅ : Store).insert name (.array (legacyIntArrayValues ty cd (4 + off + 32) n))) := by
  rw [decodeCalldata_legacyIntArray_head]
  dsimp only
  by_cases hshort : cd.size < 36
  · simp only [if_pos hshort]
  simp only [if_neg hshort]
  by_cases hoff : 2 ^ 32 < (calldataWord cd 4).toNat
  · simp only [if_pos hoff]
  simp only [if_neg hoff]
  have htlen : (cd.toList.drop 4).length = cd.size - 4 := by
      rw [List.length_drop, byteArray_toList_eq, Array.length_toList]; rfl
  by_cases hlen : cd.size < 4 + (calldataWord cd 4).toNat + 32
  · have hread : readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat = none := by
        unfold readNat? readWord? readBytes?
        rw [if_neg (by rw [List.length_take, List.length_drop, htlen]; omega)]
        rfl
    rw [if_pos hlen, decodeABIValue?, hread]
    rfl
  · rw [if_neg hlen, decodeABIValue?, readNat_drop4_dynamic_eq_calldataWord (by omega)]
    simp only [bind, Option.bind, solcMaxLen, solcMaxLenV1,
      show (4294967296 : Nat) = 2 ^ 32 from rfl]
    by_cases hcount : 2 ^ 32 < (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
    · rw [if_pos hcount, if_pos hcount]
    · rw [if_neg hcount, if_neg hcount]
      have hs : staticABIEncodedSize? (.elem (.int ty)) = some 32 := by cases ty <;> rfl
      simp only [isDynamicABIType, Bool.false_eq_true, if_false, hs]
      split_ifs with hpayload
      · rw [decodeABIArrayStaticElems_legacyInt_none_short ty _ _ _
            (by rw [htlen]; omega) (by rw [htlen]; omega)]
      · rw [decodeABIArrayStaticElems_legacyInt_ok ty cd _ _ (by omega)]
        simp only [legacyIntArrayValues, Nat.add_assoc]

end Benchmarks.UniswapV3.Pool

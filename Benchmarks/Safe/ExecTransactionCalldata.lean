import Benchmarks.Safe.ExecTransactionInput
import Benchmarks.Safe.BoundedCalldataBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execTransactionCalldataTail (cd : ByteArray) : Option Store := do
  if ¬(calldataWord cd 4).toNat < EVM.addressModulus then none else
  if solcMaxU64 < (calldataWord cd 68).toNat then none else
  let data ← boundedCalldataBytes cd (calldataWord cd 68).toNat
  if ¬(calldataWord cd 100).toNat < 256 then none else
  if ¬(calldataWord cd 228).toNat < EVM.addressModulus then none else
  if ¬(calldataWord cd 260).toNat < EVM.addressModulus then none else
  if solcMaxU64 < (calldataWord cd 292).toNat then none else
  let signatures ← boundedCalldataBytes cd (calldataWord cd 292).toNat
  some (execTransactionInput cd data signatures).args

set_option maxRecDepth 100000 in
theorem decodeExecTransactionCore {cd : ByteArray} (hh : 324 ≤ cd.size)
    (hs : cd.size < 2 ^ 255) :
    decodeCalldata execTransactionNames execTransactionTypes cd =
      execTransactionCalldataTail cd := by
  unfold execTransactionTypes
  rw [decodeDynamicCalldata (headSize := 320) (by omega) (by decide +kernel)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]),
    if_neg (by omega), if_neg (by omega)]
  rw [decodeABIValues?]
  simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
  rw [decodeAddressCalldata (cd := cd) 0 (by omega)]
  simp only [Nat.reduceAdd]
  unfold execTransactionCalldataTail
  by_cases ht : (calldataWord cd 4).toNat < EVM.addressModulus
  swap
  · rw [if_neg ht, if_pos ht]
  rw [if_pos ht, if_neg (not_not_intro ht)]
  dsimp only [bind, Option.bind]
  rw [decodeABIValues?]
  simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
  rw [decodeUint256Calldata (cd := cd) 32 (by omega)]
  simp only [Nat.reduceAdd, ↓reduceIte]
  rw [decodeABIValues?]
  simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
  rw [readNat_drop4_at_eq_calldataWord (cd := cd) 64 (by omega)]
  simp only [Nat.reduceAdd, solcMaxLen_modern]
  by_cases hd : solcMaxU64 < (calldataWord cd 68).toNat
  · simp only [hd, if_true]
  simp only [hd, if_false]
  rw [decodeBoundedCalldataBytes]
  cases hp : boundedCalldataBytes cd (calldataWord cd 68).toNat with
  | none => rfl
  | some payload =>
      dsimp only [bind, Option.bind]
      rw [decodeABIValues?]
      simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
        Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
      rw [decodeUint8Calldata (cd := cd) 96 (by omega)]
      simp only [Nat.reduceAdd]
      by_cases ho : (calldataWord cd 100).toNat < 256
      swap
      · rw [if_neg ho, if_pos ho]
      rw [if_pos ho, if_neg (not_not_intro ho)]
      dsimp only [bind, Option.bind]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [decodeABIValues?]
      simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
        Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
      rw [decodeUint256Calldata (cd := cd) 128 (by omega)]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [decodeABIValues?]
      simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
        Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
      rw [decodeUint256Calldata (cd := cd) 160 (by omega)]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [decodeABIValues?]
      simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
        Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
      rw [decodeUint256Calldata (cd := cd) 192 (by omega)]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [decodeABIValues?]
      simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
        Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
      rw [decodeAddressCalldata (cd := cd) 224 (by omega)]
      simp only [Nat.reduceAdd]
      by_cases hk : (calldataWord cd 228).toNat < EVM.addressModulus
      swap
      · rw [if_neg hk, if_pos hk]
      rw [if_pos hk, if_neg (not_not_intro hk)]
      dsimp only [bind, Option.bind]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [decodeABIValues?]
      simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
        Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
      rw [decodeAddressCalldata (cd := cd) 256 (by omega)]
      simp only [Nat.reduceAdd]
      by_cases hr : (calldataWord cd 260).toNat < EVM.addressModulus
      swap
      · rw [if_neg hr, if_pos hr]
      rw [if_pos hr, if_neg (not_not_intro hr)]
      dsimp only [bind, Option.bind]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [decodeABIValues?]
      simp only [isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
        Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
      rw [readNat_drop4_at_eq_calldataWord (cd := cd) 288 (by omega)]
      simp only [Nat.reduceAdd, solcMaxLen_modern]
      by_cases hso : solcMaxU64 < (calldataWord cd 292).toNat
      · simp only [hso, if_true]
      simp only [hso, if_false]
      rw [decodeBoundedCalldataBytes]
      cases hsig : boundedCalldataBytes cd (calldataWord cd 292).toNat with
      | none => rfl
      | some signatures =>
          simp only [decodeABIValues?, bind, Option.bind]
          rfl

end Benchmarks.Safe

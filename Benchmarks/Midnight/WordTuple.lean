import Benchmarks.Midnight.WordArray

/-! ABI returns consisting of unsigned words with possibly different widths. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def uintWordTupleTypes (entries : List (BitWidth × UInt256)) : List ABIType :=
  entries.map (fun entry ↦ .elem (.int (.uint entry.1)))

theorem uintWordTupleHeadSize (entries : List (BitWidth × UInt256)) :
    abiTupleHeadSize? (uintWordTupleTypes entries) = some (32 * entries.length) := by
  induction entries with
  | nil => simp [uintWordTupleTypes, abiTupleHeadSize?]
  | cons entry rest ih =>
    simp only [uintWordTupleTypes, List.map_cons, abiTupleHeadSize?,
      isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false,
      bind, Option.bind] at *
    rw [ih]
    simp only [List.length_cons]
    congr 1
    omega

theorem encodeUIntWordTupleFrom (entries : List (BitWidth × UInt256))
    (hlt : ∀ entry ∈ entries, entry.2.toNat < EVM.twoPow entry.1.val)
    (headSize : Nat) (head tail : List UInt8) :
    encodeABIValuesFrom? (uintWordTupleTypes entries) (wordArrayValues (entries.map Prod.snd))
      headSize head tail =
        some (head ++ (wordArrayBytes (entries.map Prod.snd)).toList ++ tail) := by
  induction entries generalizing head with
  | nil => simp [uintWordTupleTypes, wordArrayValues, encodeABIValuesFrom?,
      wordArrayBytes, byteArray_toList_eq]
  | cons entry rest ih =>
    simp only [uintWordTupleTypes, wordArrayValues] at ih
    simp only [uintWordTupleTypes, wordArrayValues, List.map_cons, encodeABIValuesFrom?,
      encodeUIntWord entry.1 entry.2 (hlt entry List.mem_cons_self), bind, Option.bind,
      isDynamicABIType, Bool.false_eq_true, if_false]
    rw [ih (fun e he ↦ hlt e (List.mem_cons_of_mem _ he))]
    simp only [wordArrayBytes, byteArray_toList_append, word_toBytesBE_eq_toByteArray_toList,
      List.append_assoc]

-- LIBRARY CANDIDATE: ABI return encoding for a tuple of bounded unsigned words.
theorem uintWordTupleReturnEncoding (entries : List (BitWidth × UInt256))
    (hlt : ∀ entry ∈ entries, entry.2.toNat < EVM.twoPow entry.1.val) :
    encodeReturnValues? (uintWordTupleTypes entries) (wordArrayValues (entries.map Prod.snd)) =
      some (wordArrayBytes (entries.map Prod.snd)) := by
  simp only [encodeReturnValues?, encodeABIValues?, uintWordTupleHeadSize, bind, Option.bind,
    encodeUIntWordTupleFrom entries hlt, List.nil_append, List.append_nil]
  congr 1
  apply ByteArray.ext
  simp [byteArray_toList_eq]

end Benchmarks.Midnight

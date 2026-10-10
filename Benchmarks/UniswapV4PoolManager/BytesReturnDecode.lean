import Benchmarks.UniswapV4PoolManager.BytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a natural ABI word read from an arbitrary byte-array position.
theorem readNat_byteArray (out : ByteArray) (start : Nat) :
    readNat? out.toList start =
      if start+32 ≤ out.size then some (calldataWord out start).toNat else none := by
  have hsize : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold readNat? readWord? readBytes?
  by_cases hh : start+32 ≤ out.size
  · rw [if_pos hh, if_pos (by rw [List.length_take, List.length_drop, hsize]; omega)]
    simp only [bind, Option.bind]
    rw [decode_word_at_eq_any out start hh]
    rfl
  · rw [if_neg hh, if_neg (by rw [List.length_take, List.length_drop, hsize]; omega)]
    rfl

-- LIBRARY CANDIDATE: the tuple wrapper around one dynamic return value.
theorem decodeReturnValue_singleDynamic_eq (out : ByteArray) (ty : ABIType)
    (hdyn : isDynamicABIType ty = true) :
    decodeReturnValue? ty out =
      if out.size < 32 ∨ 2^255 ≤ out.size then none else
      if solcMaxU64 < (calldataWord out 0).toNat then none else
      (decodeABIValue? ty out.toList (calldataWord out 0).toNat).map Prod.fst := by
  have hsize : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeReturnValue? decodeReturnValues?
  simp only [List.isEmpty_cons, true_and, hsize]
  by_cases hh : 2^255 ≤ out.size
  · simp only [hh, or_true, if_true]
  · rw [if_neg hh]
    simp only [abiTupleHeadSize?, hdyn, if_true, bind, Option.bind, decodeABIValues?,
      Nat.zero_add, readNat_byteArray]
    by_cases hs : 32 ≤ out.size
    · simp only [show 0+32 ≤ out.size from hs, if_true, show ¬out.size < 32 by omega,
        hh, or_self, if_false, solcMaxLen]
      by_cases ho : solcMaxU64 < (calldataWord out 0).toNat
      · simp only [if_pos ho]
      · simp only [ho, if_false]
        cases hd : decodeABIValue? ty out.toList (calldataWord out 0).toNat with
        | none => rfl
        | some pair => cases pair; rfl
    · simp only [show ¬0+32 ≤ out.size from hs, if_false,
        show out.size < 32 from Nat.lt_of_not_ge hs, true_or, if_true]

def BytesReturnBounds (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ out.size < 2^255 ∧ (calldataWord out 0).toNat ≤ solcMaxU64 ∧
  (calldataWord out 0).toNat+32 ≤ out.size ∧
  (calldataWord out (calldataWord out 0).toNat).toNat ≤ solcMaxU64 ∧
  (calldataWord out 0).toNat+32+(calldataWord out (calldataWord out 0).toNat).toNat ≤ out.size

instance (out : ByteArray) : Decidable (BytesReturnBounds out) := by
  unfold BytesReturnBounds
  infer_instance

def bytesReturnPayload (out : ByteArray) : ByteArray :=
  out.extract ((calldataWord out 0).toNat+32)
    ((calldataWord out 0).toNat+32+(calldataWord out (calldataWord out 0).toNat).toNat)

theorem decodeBytesReturn_ok {out : ByteArray} (hb : BytesReturnBounds out) :
    decodeReturnValue? .bytes out = some (.bytes (bytesReturnPayload out)) := by
  rcases hb with ⟨hs, hh, ho, hw, hn, hp⟩
  have hsize : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeReturnValue_singleDynamic_eq out .bytes rfl, if_neg (by omega), if_neg (by omega),
    decodeABIValue_bytes_eq, readNat_byteArray, if_pos hw]
  simp only []
  rw [if_pos ⟨hn, by rw [hsize]; exact hp⟩]
  simp only [Option.map_some, bytesSlice_eq_extract, bytesReturnPayload]

theorem decodeBytesReturn_bounds {out : ByteArray} {value : Value}
    (h : decodeReturnValue? .bytes out = some value) : BytesReturnBounds out := by
  have hsize : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeReturnValue_singleDynamic_eq out .bytes rfl] at h
  split at h
  · contradiction
  rename_i hs
  split at h
  · contradiction
  rename_i ho
  rw [decodeABIValue_bytes_eq, readNat_byteArray] at h
  by_cases hw : (calldataWord out 0).toNat+32 ≤ out.size
  · rw [if_pos hw] at h
    simp only [] at h
    split at h
    · rename_i hp
      rw [hsize] at hp
      exact ⟨by omega, by omega, by omega, hw, hp⟩
    · cases h
  · rw [if_neg hw] at h
    cases h

theorem decodeBytesReturn_none {out : ByteArray} (hb : ¬BytesReturnBounds out) :
    decodeReturnValue? .bytes out = none := by
  cases hd : decodeReturnValue? .bytes out with
  | none => rfl
  | some value => exact (hb (decodeBytesReturn_bounds hd)).elim

end Benchmarks.UniswapV4PoolManager

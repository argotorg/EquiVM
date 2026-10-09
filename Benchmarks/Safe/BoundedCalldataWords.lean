import Benchmarks.Safe.CalldataWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: bounds checks for a dynamic array of calldata words.
def boundedCalldataWords (cd : ByteArray) (off : Nat) : Option (List UInt256) := do
  let len ← readNat? (cd.toList.drop 4) off
  if solcMaxU64 < len then none else
  if cd.size < 4 + off + 32 + 32 * len then none else
  some (calldataWords cd (4 + off + 32) len)

theorem decodeBoundedCalldataAddresses (cd : ByteArray) (off : Nat) :
    decodeABIValue? (.dynamicArray (.elem .address)) (cd.toList.drop 4) off = (do
      let words ← boundedCalldataWords cd off
      if ∀ w ∈ words, w.toNat < EVM.addressModulus then
        some (.array (words.map addressArrayValue), off + 32 + 32 * words.length)
      else none) := by
  unfold boundedCalldataWords
  simp only [decodeABIValue?, solcMaxLen_modern, bind, Option.bind]
  cases hr : readNat? (cd.toList.drop 4) off with
  | none => rfl
  | some len =>
      dsimp only
      by_cases hl : solcMaxU64 < len
      · simp only [hl, if_true, bind, Option.bind]
      rw [if_neg hl, if_neg hl]
      simp only [isDynamicABIType, Bool.false_eq_true, if_false, staticABIEncodedSize?,
        bind, Option.bind]
      by_cases hin : 4 + off + 32 + 32 * len ≤ cd.size
      · rw [if_neg (by omega), decodeAddressArrayElements (off + 32) len (by omega)]
        simp only [← Nat.add_assoc, bind, Option.bind, calldataWords_length]
        by_cases hc : ∀ w ∈ calldataWords cd (4 + off + 32) len,
            w.toNat < EVM.addressModulus
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
      · have hnone : decodeABIArrayStaticElems? (.elem .address) len 32
            (cd.toList.drop 4) (off + 32) = none := by
          cases hd : decodeABIArrayStaticElems? (.elem .address) len 32
              (cd.toList.drop 4) (off + 32) with
          | none => rfl
          | some p =>
              obtain ⟨he, hb, _⟩ :=
                decodeABIArrayStaticElems_elem32_facts (readNat?_some_length hr) hd
              have hlist : cd.toList.length = cd.size := by
                rw [byteArray_toList_eq, Array.length_toList]; rfl
              have hhead := readNat?_some_length hr
              simp only [List.length_drop, hlist] at hb hhead
              omega
        rw [if_pos (by omega), hnone]

theorem boundedCalldataWordsValid {cd : ByteArray} {off len : Nat}
    (hw : calldataWord cd (4 + off) = UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 1) (hin : 4 + off + 32 + 32 * len ≤ cd.size) :
    boundedCalldataWords cd off = some (calldataWords cd (4 + off + 32) len) := by
  have hr := readNat_drop4_at_eq_calldataWord (cd := cd) off (by omega)
  rw [hw, ulit_toNat' len (by change len < 2 ^ 256; omega)] at hr
  rw [boundedCalldataWords, hr]
  dsimp only [bind, Option.bind]
  rw [if_neg (show ¬solcMaxU64 < len by change ¬2 ^ 64 - 1 < len; omega), if_neg (by omega)]

theorem boundedCalldataWordsEvidence {cd : ByteArray} {off : Nat} {words : List UInt256}
    (hd : boundedCalldataWords cd off = some words) :
    ∃ len, calldataWord cd (4 + off) = UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 1 ∧
      4 + off + 32 + 32 * len ≤ cd.size ∧ words = calldataWords cd (4 + off + 32) len := by
  unfold boundedCalldataWords at hd
  cases hr : readNat? (cd.toList.drop 4) off with
  | none => rw [hr] at hd; cases hd
  | some len =>
      rw [hr] at hd
      dsimp only [bind, Option.bind] at hd
      by_cases hn : solcMaxU64 < len
      · rw [if_pos hn] at hd; cases hd
      rw [if_neg hn] at hd
      by_cases hin : cd.size < 4 + off + 32 + 32 * len
      · rw [if_pos hin] at hd; cases hd
      rw [if_neg hin, Option.some.injEq] at hd
      have hw := readNat_drop4_at_eq_calldataWord (cd := cd) off (by omega)
      rw [hr, Option.some.injEq] at hw
      refine ⟨len, ?_, ?_, by omega, hd.symm⟩
      · rw [hw]; exact (u256_ofNat_toNat _).symm
      · change len ≤ solcMaxU64; omega

end Benchmarks.Safe

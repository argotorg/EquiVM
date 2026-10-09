import Benchmarks.Safe.DynamicCalldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: the modern ABI length and payload checks for a dynamic bytes tail.
def boundedCalldataBytes (cd : ByteArray) (off : Nat) : Option ByteArray := do
  let len ← readNat? (cd.toList.drop 4) off
  if solcMaxU64 < len then none else
  let payload ← readBytes? (cd.toList.drop 4) (off + 32) len
  some ⟨payload.toArray⟩

theorem decodeBoundedCalldataBytes (cd : ByteArray) (off : Nat) :
    decodeABIValue? .bytes (cd.toList.drop 4) off = (do
      let payload ← boundedCalldataBytes cd off
      some (.bytes payload, off + 32 + ABI.paddedSize payload.size)) := by
  unfold boundedCalldataBytes
  simp only [decodeABIValue?, solcMaxLen_modern, bind, Option.bind]
  cases hn : readNat? (cd.toList.drop 4) off with
  | none => rfl
  | some len =>
    simp only []
    by_cases hlarge : solcMaxU64 < len
    · simp only [hlarge, if_true]
    simp only [hlarge, if_false]
    cases hp : readBytes? (cd.toList.drop 4) (off + 32) len with
    | none => rfl
    | some bytes =>
      have hlen : bytes.length = len := by
        unfold readBytes? at hp
        dsimp only at hp
        split at hp
        · have he := Option.some.inj hp
          rw [← he]; assumption
        · cases hp
      simp [ByteArray.size, hlen]

theorem boundedCalldataBytesValid {cd : ByteArray} {off len : Nat}
    (hw : calldataWord cd (4 + off) = UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 1) (hin : 4 + off + 32 + len ≤ cd.size) :
    boundedCalldataBytes cd off =
      some (cd.extract (4 + off + 32) (4 + off + 32 + len)) := by
  have hread := readNat_drop4_at_eq_calldataWord (cd := cd) off (by omega)
  rw [hw, ulit_toNat' len (by change len < 2 ^ 256; omega)] at hread
  rw [boundedCalldataBytes, hread]
  dsimp only [bind, Option.bind]
  rw [if_neg (show ¬solcMaxU64 < len by change ¬2 ^ 64 - 1 < len; omega),
    readBytesCalldata (by omega)]
  simp only [bind, Option.bind, byteArray_toList_eq, Array.toArray_toList, ← Nat.add_assoc]

theorem boundedCalldataBytesEvidence {cd payload : ByteArray} {off : Nat}
    (hlong : 4 ≤ cd.size) (hd : boundedCalldataBytes cd off = some payload) :
    ∃ len, calldataWord cd (4 + off) = UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 1 ∧
      4 + off + 32 + len ≤ cd.size ∧
      payload = cd.extract (4 + off + 32) (4 + off + 32 + len) := by
  unfold boundedCalldataBytes at hd
  cases hread : readNat? (cd.toList.drop 4) off with
  | none => rw [hread] at hd; cases hd
  | some len =>
    rw [hread] at hd
    dsimp only [bind, Option.bind] at hd
    by_cases hn : solcMaxU64 < len
    · rw [if_pos hn] at hd; cases hd
    rw [if_neg hn] at hd
    cases hp : readBytes? (cd.toList.drop 4) (off + 32) len with
    | none => rw [hp] at hd; cases hd
    | some bytes =>
      rw [hp] at hd
      obtain ⟨hw, hin, hb⟩ := readCalldataBytesEvidence hlong hread hp
      refine ⟨len, hw, ?_, hin, ?_⟩
      · change len ≤ solcMaxU64; omega
      · simp only [bind, Option.bind, Option.some.injEq] at hd
        rw [← hd, hb]
        simp only [byteArray_toList_eq, Array.toArray_toList]

end Benchmarks.Safe

import Benchmarks.Safe.DynamicCalldata
import Benchmarks.Safe.ModuleArguments

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

abbrev moduleCalldataTypes : List ABIType := [abiAddress, abiUInt256, .bytes, abiUInt8]

def moduleCalldataTail (cd : ByteArray) : Option Store := do
  if ¬(calldataWord cd 4).toNat < EVM.addressModulus then none else
  let off := (calldataWord cd 68).toNat
  if solcMaxU64 < off then none else
  let len ← readNat? (cd.toList.drop 4) off
  if solcMaxU64 < len then none else
  let payload ← readBytes? (cd.toList.drop 4) (off + 32) len
  if ¬(calldataWord cd 100).toNat < 256 then none else
  some (moduleArgs (AccountAddress.ofNat (calldataWord cd 4).toNat)
    (calldataWord cd 36) ⟨payload.toArray⟩ (calldataWord cd 100))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem decodeModuleCalldataCore {cd : ByteArray}
    (hh : 132 ≤ cd.size) (hs : cd.size < 2 ^ 255) :
    decodeCalldata ["to", "value", "data", "operation"] moduleCalldataTypes cd =
      moduleCalldataTail cd := by
  rw [decodeDynamicCalldata (headSize := 128) (by omega) (by decide)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]),
    if_neg (by omega), if_neg (by omega)]
  have hn64 := readNat_drop4_at_eq_calldataWord (cd := cd) 64 (by omega)
  have ha := decodeAddressCalldata (cd := cd) 0 (by omega)
  have hv := decodeUint256Calldata (cd := cd) 32 (by omega)
  have ho := decodeUint8Calldata (cd := cd) 96 hh
  simp only [decodeABIValues?, isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
  rw [ha]
  unfold moduleCalldataTail
  by_cases hc : (calldataWord cd 4).toNat < EVM.addressModulus
  swap
  · simp only [hc, not_false_eq_true, if_true, if_false]
  simp only [hc, not_true_eq_false, if_false, if_true, Nat.reduceAdd]
  rw [hv]
  simp only [↓reduceIte, Nat.reduceAdd]
  rw [hn64]
  simp only [Nat.reduceAdd, solcMaxLen_modern]
  by_cases hoff : solcMaxU64 < (calldataWord cd 68).toNat
  · simp only [hoff, if_true]
  simp only [hoff, if_false]
  rw [ho]
  simp only [decodeABIValue?, solcMaxLen_modern, bind, Option.bind]
  cases hn : readNat? (cd.toList.drop 4) (calldataWord cd 68).toNat with
  | none => rfl
  | some len =>
    simp only []
    by_cases hlen : solcMaxU64 < len
    · simp only [hlen, if_true]
    simp only [hlen, if_false]
    cases hp : readBytes? (cd.toList.drop 4) ((calldataWord cd 68).toNat + 32) len with
    | none => rfl
    | some payload =>
      by_cases hop : (calldataWord cd 100).toNat < 256 <;>
        simp only [hop, ↓reduceIte, not_true_eq_false, not_false_eq_true,
          bind, Option.bind, moduleArgs, decodeCalldata.insertValues]

theorem decodeModuleCalldataValid {cd : ByteArray} {len : Nat}
    (hh : 132 ≤ cd.size) (hs : cd.size < 2 ^ 255)
    (hc : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 1)
    (hin : 4 + (calldataWord cd 68).toNat + 32 + len ≤ cd.size)
    (ho : (calldataWord cd 100).toNat < 256) :
    decodeCalldata ["to", "value", "data", "operation"] moduleCalldataTypes cd =
      some (moduleArgs (AccountAddress.ofNat (calldataWord cd 4).toNat)
        (calldataWord cd 36)
        (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + len)) (calldataWord cd 100)) := by
  rw [decodeModuleCalldataCore hh hs]
  have hread := readNat_drop4_at_eq_calldataWord (cd := cd)
    (calldataWord cd 68).toNat (by omega)
  rw [hw, ulit_toNat' len (by change len < 2 ^ 256; omega)] at hread
  have hp := readBytesCalldata (cd := cd) (off := (calldataWord cd 68).toNat + 32)
    (len := len) (by omega)
  unfold moduleCalldataTail
  rw [if_neg (not_not_intro hc), if_neg (show ¬solcMaxU64 < (calldataWord cd 68).toNat by
    change ¬2 ^ 64 - 1 < _; omega), hread]
  dsimp only [bind, Option.bind]
  rw [if_neg (show ¬solcMaxU64 < len by change ¬2 ^ 64 - 1 < len; omega), hp]
  dsimp only [bind, Option.bind]
  rw [if_neg (not_not_intro ho)]
  simp only [byteArray_toList_eq, Array.toArray_toList, ← Nat.add_assoc]

set_option maxRecDepth 5000 in
theorem decodeModuleCalldataEvidence {cd : ByteArray} {args : Store} (hlong : 4 ≤ cd.size)
    (hd : decodeCalldata ["to", "value", "data", "operation"] moduleCalldataTypes cd =
      some args) :
    ∃ len, 132 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧
      (calldataWord cd 4).toNat < EVM.addressModulus ∧
      (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat len ∧
      len ≤ 2 ^ 64 - 1 ∧ 4 + (calldataWord cd 68).toNat + 32 + len ≤ cd.size ∧
      (calldataWord cd 100).toNat < 256 ∧
      args = moduleArgs (AccountAddress.ofNat (calldataWord cd 4).toNat)
        (calldataWord cd 36)
        (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + len)) (calldataWord cd 100) := by
  have hg := decodeDynamicCalldata (cd := cd)
    (names := ["to", "value", "data", "operation"])
    (ty := abiAddress) (types := [abiUInt256, .bytes, abiUInt8]) (headSize := 128)
    hlong (by decide)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind])
  have hs : cd.size < 2 ^ 255 := by
    by_contra hbad
    rw [hg, if_pos (by omega)] at hd
    cases hd
  have hh : 132 ≤ cd.size := by
    by_contra hbad
    rw [hg, if_neg (by omega), if_pos (by omega)] at hd
    cases hd
  rw [decodeModuleCalldataCore hh hs] at hd
  unfold moduleCalldataTail at hd
  by_cases hc : (calldataWord cd 4).toNat < EVM.addressModulus
  swap
  · rw [if_pos hc] at hd; cases hd
  rw [if_neg (not_not_intro hc)] at hd
  by_cases hoff : solcMaxU64 < (calldataWord cd 68).toNat
  · rw [if_pos hoff] at hd; cases hd
  rw [if_neg hoff] at hd
  cases hread : readNat? (cd.toList.drop 4) (calldataWord cd 68).toNat with
  | none => rw [hread] at hd; cases hd
  | some len =>
    rw [hread] at hd
    dsimp only [bind, Option.bind] at hd
    by_cases hn : solcMaxU64 < len
    · rw [if_pos hn] at hd; cases hd
    rw [if_neg hn] at hd
    cases hp : readBytes? (cd.toList.drop 4) ((calldataWord cd 68).toNat + 32) len with
    | none => rw [hp] at hd; cases hd
    | some payload =>
      rw [hp] at hd
      dsimp only [bind, Option.bind] at hd
      by_cases ho : (calldataWord cd 100).toNat < 256
      swap
      · rw [if_pos ho] at hd; cases hd
      rw [if_neg (not_not_intro ho), Option.some.injEq] at hd
      obtain ⟨hword, hin, hbytes⟩ := readCalldataBytesEvidence hlong hread hp
      refine ⟨len, hh, hs, hc, ?_, hword, ?_, hin, ho, ?_⟩
      · change _ ≤ solcMaxU64; omega
      · change len ≤ solcMaxU64; omega
      · rw [← hd, hbytes]
        simp only [byteArray_toList_eq, Array.toArray_toList, ← Nat.add_assoc]

end Benchmarks.Safe

import Benchmarks.Safe.DynamicCalldata
import Benchmarks.Safe.CheckSignaturesSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES decodeABIValue_bytes32_ok to a calldata word at any in-bounds offset.
theorem decodeBytes32Calldata {cd : ByteArray} (off : Nat) (hin : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? abiBytes32 (cd.toList.drop 4) off =
      some (wordBytes32Value (calldataWord cd (4 + off)), off + 32) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  have hbytes : EVM.Word.toBytesBE (calldataWord cd (4 + off)) =
      ((cd.toList.drop 4).drop off).take 32 := by
    have hword : ABI.bytesToWord ((cd.toList.drop (4 + off)).take 32) =
        calldataWord cd (4 + off) := decode_word_at_eq_any cd (4 + off) hin
    rw [List.drop_drop, ← hword]
    apply toBytesBE_bytesToWord_of_length
    simpa only [List.drop_drop] using htake
  rw [decodeABIValue_bytes32_ok htake]
  simp only [wordBytes32Value, hbytes]

def signatureAddressNames (counted : Bool) : List Ident :=
  ["executor", "dataHash", "signatures"] ++ if counted then ["requiredSignatures"] else []

def signatureAddressTypes (counted : Bool) : List ABIType :=
  abiAddress :: abiBytes32 :: .bytes :: if counted then [abiUInt256] else []

def signatureAddressHead (counted : Bool) : Nat := if counted then 128 else 96

def signatureAddressArgs (counted : Bool) (executor : EVM.Address) (hash : UInt256)
    (signatures : ByteArray) (required : UInt256) : Store :=
  let args := (((∅ : Store).insert "executor" (.address executor)).insert
    "dataHash" (wordBytes32Value hash)).insert "signatures" (.bytes signatures)
  if counted then args.insert "requiredSignatures" (uint256Value required) else args

def signatureAddressTail (counted : Bool) (cd : ByteArray) : Option Store := do
  if ¬(calldataWord cd 4).toNat < EVM.addressModulus then none else
  let off := (calldataWord cd 68).toNat
  if solcMaxU64 < off then none else
  let len ← readNat? (cd.toList.drop 4) off
  if solcMaxU64 < len then none else
  let payload ← readBytes? (cd.toList.drop 4) (off + 32) len
  some (signatureAddressArgs counted (AccountAddress.ofNat (calldataWord cd 4).toNat)
    (calldataWord cd 36) ⟨payload.toArray⟩ (calldataWord cd 100))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem decodeSignatureAddressCore {cd : ByteArray} (counted : Bool)
    (hh : 4 + signatureAddressHead counted ≤ cd.size) (hs : cd.size < 2 ^ 255) :
    decodeCalldata (signatureAddressNames counted) (signatureAddressTypes counted) cd =
      signatureAddressTail counted cd := by
  have hlo : 100 ≤ cd.size := by cases counted <;> simp [signatureAddressHead] at hh <;> omega
  unfold signatureAddressTypes
  rw [decodeDynamicCalldata (headSize := signatureAddressHead counted) (by omega)
    (by simp [signatureAddressTypes, isDynamicABIType])
    (by cases counted <;> simp [signatureAddressHead, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType, bind, Option.bind]), if_neg (by omega), if_neg (by omega)]
  have ha := decodeAddressCalldata (cd := cd) 0 (by omega)
  have hhsh := decodeBytes32Calldata (cd := cd) 32 (by omega)
  have hoff := readNat_drop4_at_eq_calldataWord (cd := cd) 64 (by omega)
  cases counted <;> simp only [signatureAddressHead, Bool.false_eq_true, if_false, if_true] at hh ⊢
  all_goals
    simp only [decodeABIValues?, isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
      Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
    rw [ha]
    unfold signatureAddressTail
    by_cases hc : (calldataWord cd 4).toNat < EVM.addressModulus
    swap
    · simp only [hc, not_false_eq_true, if_true, if_false]
    simp only [hc, not_true_eq_false, if_false, if_true, Nat.reduceAdd]
    rw [hhsh]
    simp only [↓reduceIte, Nat.reduceAdd]
    rw [hoff]
    simp only [Nat.reduceAdd, solcMaxLen_modern]
    by_cases ho : solcMaxU64 < (calldataWord cd 68).toNat
    · simp only [ho, if_true]
    simp only [ho, if_false]
    try rw [decodeUint256Calldata (cd := cd) 96 hh]
    simp only [decodeABIValue?, solcMaxLen_modern, bind, Option.bind]
    cases hl : readNat? (cd.toList.drop 4) (calldataWord cd 68).toNat with
    | none => rfl
    | some len =>
      simp only []
      by_cases hn : solcMaxU64 < len
      · simp only [hn, if_true]
      simp only [hn, if_false]
      cases hp : readBytes? (cd.toList.drop 4) ((calldataWord cd 68).toNat + 32) len with
      | none => rfl
      | some payload =>
        simp [signatureAddressNames, signatureAddressArgs, decodeCalldata.insertValues,
          uint256Value]

theorem decodeSignatureAddressValid {cd : ByteArray} (counted : Bool) {len : Nat}
    (hh : 4 + signatureAddressHead counted ≤ cd.size) (hs : cd.size < 2 ^ 255)
    (hc : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 1)
    (hin : 4 + (calldataWord cd 68).toNat + 32 + len ≤ cd.size) :
    decodeCalldata (signatureAddressNames counted) (signatureAddressTypes counted) cd =
      some (signatureAddressArgs counted (AccountAddress.ofNat (calldataWord cd 4).toNat)
        (calldataWord cd 36) (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + len)) (calldataWord cd 100)) := by
  rw [decodeSignatureAddressCore counted hh hs]
  have hread := readNat_drop4_at_eq_calldataWord (cd := cd)
    (calldataWord cd 68).toNat (by omega)
  rw [hw, ulit_toNat' len (by change len < 2 ^ 256; omega)] at hread
  have hp := readBytesCalldata (cd := cd) (off := (calldataWord cd 68).toNat + 32)
    (len := len) (by omega)
  unfold signatureAddressTail
  rw [if_neg (not_not_intro hc), if_neg (show ¬solcMaxU64 < (calldataWord cd 68).toNat by
    change ¬2 ^ 64 - 1 < _; omega), hread]
  dsimp only [bind, Option.bind]
  rw [if_neg (show ¬solcMaxU64 < len by change ¬2 ^ 64 - 1 < len; omega), hp]
  simp only [bind, Option.bind, byteArray_toList_eq, Array.toArray_toList, ← Nat.add_assoc]

set_option maxRecDepth 100000 in
theorem decodeSignatureAddressEvidence {cd : ByteArray} (counted : Bool) {args : Store}
    (hlong : 4 ≤ cd.size)
    (hd : decodeCalldata (signatureAddressNames counted) (signatureAddressTypes counted) cd =
      some args) :
    ∃ len, 4 + signatureAddressHead counted ≤ cd.size ∧ cd.size < 2 ^ 255 ∧
      (calldataWord cd 4).toNat < EVM.addressModulus ∧
      (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat len ∧
      len ≤ 2 ^ 64 - 1 ∧ 4 + (calldataWord cd 68).toNat + 32 + len ≤ cd.size ∧
      args = signatureAddressArgs counted (AccountAddress.ofNat (calldataWord cd 4).toNat)
        (calldataWord cd 36) (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + len)) (calldataWord cd 100) := by
  have hg := decodeDynamicCalldata (cd := cd) (names := signatureAddressNames counted)
    (ty := abiAddress) (types := abiBytes32 :: .bytes :: if counted then [abiUInt256] else [])
    (headSize := signatureAddressHead counted) hlong
    (by simp [isDynamicABIType])
    (by cases counted <;> simp [signatureAddressHead, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType, bind, Option.bind])
  change decodeCalldata (signatureAddressNames counted) (signatureAddressTypes counted) cd = _ at hg
  have hs : cd.size < 2 ^ 255 := by
    by_contra hbad
    rw [hg, if_pos (by omega)] at hd
    cases hd
  have hh : 4 + signatureAddressHead counted ≤ cd.size := by
    by_contra hbad
    rw [hg, if_neg (by omega), if_pos (by omega)] at hd
    cases hd
  rw [decodeSignatureAddressCore counted hh hs] at hd
  unfold signatureAddressTail at hd
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
      obtain ⟨hword, hin, hbytes⟩ := readCalldataBytesEvidence hlong hread hp
      refine ⟨len, hh, hs, hc, ?_, hword, ?_, hin, ?_⟩
      · change _ ≤ solcMaxU64; omega
      · change len ≤ solcMaxU64; omega
      · rw [Option.some.injEq] at hd
        rw [← hd, hbytes]
        simp only [byteArray_toList_eq, Array.toArray_toList, ← Nat.add_assoc]

end Benchmarks.Safe

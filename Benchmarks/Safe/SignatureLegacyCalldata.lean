import Benchmarks.Safe.SignatureAddressCalldata
import Benchmarks.Safe.BoundedCalldataBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def signatureLegacyNames (counted : Bool) : List Ident :=
  ["dataHash", "data", "signatures"] ++ if counted then ["requiredSignatures"] else []

def signatureLegacyTypes (counted : Bool) : List ABIType :=
  abiBytes32 :: .bytes :: .bytes :: if counted then [abiUInt256] else []

def signatureLegacyArgs (counted : Bool) (hash : UInt256) (data signatures : ByteArray)
    (required : UInt256) : Store :=
  let args := (((∅ : Store).insert "dataHash" (wordBytes32Value hash)).insert
    "data" (.bytes data)).insert "signatures" (.bytes signatures)
  if counted then args.insert "requiredSignatures" (uint256Value required) else args

def signatureLegacyTail (counted : Bool) (cd : ByteArray) : Option Store := do
  if solcMaxU64 < (calldataWord cd 36).toNat then none else
  let data ← boundedCalldataBytes cd (calldataWord cd 36).toNat
  if solcMaxU64 < (calldataWord cd 68).toNat then none else
  let signatures ← boundedCalldataBytes cd (calldataWord cd 68).toNat
  some (signatureLegacyArgs counted (calldataWord cd 4) data signatures (calldataWord cd 100))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem decodeSignatureLegacyCore {cd : ByteArray} (counted : Bool)
    (hh : 4 + signatureAddressHead counted ≤ cd.size) (hs : cd.size < 2 ^ 255) :
    decodeCalldata (signatureLegacyNames counted) (signatureLegacyTypes counted) cd =
      signatureLegacyTail counted cd := by
  have hlo : 100 ≤ cd.size := by cases counted <;> simp [signatureAddressHead] at hh <;> omega
  unfold signatureLegacyTypes
  rw [decodeDynamicCalldata (headSize := signatureAddressHead counted) (by omega)
    (by simp [isDynamicABIType])
    (by cases counted <;> simp [signatureAddressHead, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType, bind, Option.bind]), if_neg (by omega), if_neg (by omega)]
  have hhash := decodeBytes32Calldata (cd := cd) 0 (by omega)
  have hd := readNat_drop4_at_eq_calldataWord (cd := cd) 32 (by omega)
  have hs' := readNat_drop4_at_eq_calldataWord (cd := cd) 64 (by omega)
  cases counted <;> simp only [signatureAddressHead, Bool.false_eq_true, if_false, if_true] at hh ⊢
  all_goals
    simp only [decodeABIValues?, isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
      Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
    rw [hhash]
    simp only [↓reduceIte, Nat.reduceAdd]
    rw [hd]
    simp only [Nat.reduceAdd, solcMaxLen_modern]
    unfold signatureLegacyTail
    by_cases hdo : solcMaxU64 < (calldataWord cd 36).toNat
    · simp only [hdo, if_true]
    simp only [hdo, if_false]
    rw [decodeBoundedCalldataBytes]
    cases hdata : boundedCalldataBytes cd (calldataWord cd 36).toNat with
    | none => rfl
    | some data =>
      dsimp only [bind, Option.bind]
      rw [hs']
      simp only [Nat.reduceAdd, solcMaxLen_modern]
      by_cases hso : solcMaxU64 < (calldataWord cd 68).toNat
      · simp only [hso, if_true]
      simp only [hso, if_false]
      rw [decodeBoundedCalldataBytes]
      cases hsig : boundedCalldataBytes cd (calldataWord cd 68).toNat with
      | none => rfl
      | some signatures =>
        dsimp only [bind, Option.bind]
        try rw [decodeUint256Calldata (cd := cd) 96 hh]
        simp [signatureLegacyNames, signatureLegacyArgs, decodeCalldata.insertValues,
          uint256Value]

theorem decodeSignatureLegacyValid {cd : ByteArray} (counted : Bool) {dataLen sigLen : Nat}
    (hh : 4 + signatureAddressHead counted ≤ cd.size) (hs : cd.size < 2 ^ 255)
    (hdo : (calldataWord cd 36).toNat ≤ 2 ^ 64 - 1)
    (hdw : calldataWord cd (4 + (calldataWord cd 36).toNat) = UInt256.ofNat dataLen)
    (hdn : dataLen ≤ 2 ^ 64 - 1)
    (hdi : 4 + (calldataWord cd 36).toNat + 32 + dataLen ≤ cd.size)
    (hso : (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1)
    (hsw : calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat sigLen)
    (hsn : sigLen ≤ 2 ^ 64 - 1)
    (hsi : 4 + (calldataWord cd 68).toNat + 32 + sigLen ≤ cd.size) :
    decodeCalldata (signatureLegacyNames counted) (signatureLegacyTypes counted) cd =
      some (signatureLegacyArgs counted (calldataWord cd 4)
        (cd.extract (4 + (calldataWord cd 36).toNat + 32)
          (4 + (calldataWord cd 36).toNat + 32 + dataLen))
        (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + sigLen)) (calldataWord cd 100)) := by
  rw [decodeSignatureLegacyCore counted hh hs, signatureLegacyTail,
    if_neg (show ¬solcMaxU64 < (calldataWord cd 36).toNat by
      change ¬2 ^ 64 - 1 < _; omega), boundedCalldataBytesValid hdw hdn hdi]
  dsimp only [bind, Option.bind]
  rw [if_neg (show ¬solcMaxU64 < (calldataWord cd 68).toNat by
    change ¬2 ^ 64 - 1 < _; omega), boundedCalldataBytesValid hsw hsn hsi]

set_option maxRecDepth 100000 in
theorem decodeSignatureLegacyEvidence {cd : ByteArray} (counted : Bool) {args : Store}
    (hlong : 4 ≤ cd.size)
    (hd : decodeCalldata (signatureLegacyNames counted) (signatureLegacyTypes counted) cd =
      some args) :
    ∃ dataLen sigLen, 4 + signatureAddressHead counted ≤ cd.size ∧ cd.size < 2 ^ 255 ∧
      (calldataWord cd 36).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord cd (4 + (calldataWord cd 36).toNat) = UInt256.ofNat dataLen ∧
      dataLen ≤ 2 ^ 64 - 1 ∧ 4 + (calldataWord cd 36).toNat + 32 + dataLen ≤ cd.size ∧
      (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat sigLen ∧
      sigLen ≤ 2 ^ 64 - 1 ∧ 4 + (calldataWord cd 68).toNat + 32 + sigLen ≤ cd.size ∧
      args = signatureLegacyArgs counted (calldataWord cd 4)
        (cd.extract (4 + (calldataWord cd 36).toNat + 32)
          (4 + (calldataWord cd 36).toNat + 32 + dataLen))
        (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + sigLen)) (calldataWord cd 100) := by
  have hg := decodeDynamicCalldata (cd := cd) (names := signatureLegacyNames counted)
    (ty := abiBytes32) (types := .bytes :: .bytes :: if counted then [abiUInt256] else [])
    (headSize := signatureAddressHead counted) hlong
    (by simp [isDynamicABIType])
    (by cases counted <;> simp [signatureAddressHead, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType, bind, Option.bind])
  change decodeCalldata (signatureLegacyNames counted) (signatureLegacyTypes counted) cd = _ at hg
  have hs : cd.size < 2 ^ 255 := by
    by_contra hbad
    rw [hg, if_pos (by omega)] at hd
    cases hd
  have hh : 4 + signatureAddressHead counted ≤ cd.size := by
    by_contra hbad
    rw [hg, if_neg (by omega), if_pos (by omega)] at hd
    cases hd
  rw [decodeSignatureLegacyCore counted hh hs] at hd
  unfold signatureLegacyTail at hd
  by_cases hdo : solcMaxU64 < (calldataWord cd 36).toNat
  · rw [if_pos hdo] at hd; cases hd
  rw [if_neg hdo] at hd
  cases hdata : boundedCalldataBytes cd (calldataWord cd 36).toNat with
  | none => rw [hdata] at hd; cases hd
  | some data =>
    rw [hdata] at hd
    dsimp only [bind, Option.bind] at hd
    by_cases hso : solcMaxU64 < (calldataWord cd 68).toNat
    · rw [if_pos hso] at hd; cases hd
    rw [if_neg hso] at hd
    cases hsig : boundedCalldataBytes cd (calldataWord cd 68).toNat with
    | none => rw [hsig] at hd; cases hd
    | some signatures =>
      rw [hsig] at hd
      dsimp only [bind, Option.bind] at hd
      obtain ⟨dataLen, hdw, hdn, hdi, rfl⟩ := boundedCalldataBytesEvidence hlong hdata
      obtain ⟨sigLen, hsw, hsn, hsi, rfl⟩ := boundedCalldataBytesEvidence hlong hsig
      refine ⟨dataLen, sigLen, hh, hs, ?_, hdw, hdn, hdi, ?_, hsw, hsn, hsi, ?_⟩
      · change _ ≤ solcMaxU64; omega
      · change _ ≤ solcMaxU64; omega
      · exact (Option.some.inj hd).symm

end Benchmarks.Safe

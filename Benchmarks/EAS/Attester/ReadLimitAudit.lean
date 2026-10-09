import Benchmarks.EAS.Attester.Spec
import Benchmarks.EAS.Attester.Memory

/-!
Regression for outgoing calls larger than 2^64 bytes. The source ABI encoder admits these
requests, and the updated EVMLean read preserves them without a size precondition.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester.ReadLimitAudit

theorem oversizedPayloadPreserved (payload : ByteArray) (h : 2 ^ 64 ≤ payload.size) :
    payload.readWithPadding 0 payload.size = payload := by
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega), Nat.zero_add]
  exact byteArray_extract_self payload

def zeroSchema : Value := .fixedBytes ⟨31, by decide⟩ (List.replicate 32 0)

def zeroPair : Value := .tuple [zeroSchema, .int 0]

theorem zeroPairEncoded :
    encodeABIValue? revocationRequestDataTy zeroPair = some (List.replicate 64 0) := by
  simp only [revocationRequestDataTy, zeroPair, zeroSchema, bytes32, bytes32Width,
    uint256, uint256Int, encodeABIValue?, encodeABIValues?, abiTupleHeadSize?,
    isDynamicABIType, staticABIEncodedSize?, encodeABIValuesFrom?, encodeABIWord?]
  decide +kernel

theorem zeroPairsEncoded (n : Nat) :
    ∃ bs, encodeABIStaticArrayElems? revocationRequestDataTy (List.replicate n zeroPair) = some bs ∧
      bs.length = 64 * n := by
  induction n with
  | zero => exact ⟨[], by simp [encodeABIStaticArrayElems?], rfl⟩
  | succ n ih =>
      obtain ⟨bs, hb, hs⟩ := ih
      refine ⟨List.replicate 64 0 ++ bs, ?_, ?_⟩
      · simp only [List.replicate_succ, encodeABIStaticArrayElems?, zeroPairEncoded, hb,
          Option.bind_some]
        rfl
      · simp only [List.length_append, List.length_replicate, hs]; omega

def oneRequest (n : Nat) : Value :=
  .array [.tuple [zeroSchema, .array (List.replicate n zeroPair)]]

theorem oneRequestEncoded (n : Nat) :
    ∃ payload, encodeCallWithSelector? multiRevokeSelector [multiRevocationRequestArrayTy]
      [oneRequest n] = some payload ∧ payload.size = 196 + 64 * n := by
  obtain ⟨bs, hb, hs⟩ := zeroPairsEncoded n
  have hd : isDynamicABIType revocationRequestDataTy = false := rfl
  have hdata : encodeABIValue? (.dynamicArray revocationRequestDataTy)
      (.array (List.replicate n zeroPair)) = some (natBytes n ++ bs) := by
    simp only [encodeABIValue?, encodeABIArrayElems?, hd, Bool.false_eq_true, ↓reduceIte, hb,
      Option.bind_some, List.length_replicate]
    rfl
  have hz : encodeABIValue? bytes32 zeroSchema = some (List.replicate 32 0) := by
    simp [encodeABIValue?, bytes32, bytes32Width, zeroSchema, zeroBytes]
  let encoded := natBytes 32 ++ natBytes 1 ++ natBytes 32 ++ List.replicate 32 0 ++
    natBytes 64 ++ natBytes n ++ bs
  refine ⟨multiRevokeSelector ++ encoded.toByteArray, ?_, ?_⟩
  · simp only [encodeCallWithSelector?, multiRevocationRequestArrayTy, multiRevocationRequestTy,
      oneRequest, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType, isDynamicABITypeList,
      encodeABIValuesFrom?, encodeABIValue?, encodeABIArrayElems?,
      encodeABIDynamicArrayElemsFrom?, hz, hdata, Option.bind_some]
    simp only [bytes32, isDynamicABIType, staticABIEncodedSize?, Option.bind_some,
      ↓reduceIte, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero,
      Nat.reduceAdd, Nat.reduceMul, List.nil_append, List.append_nil]
    simp only [encoded, List.append_assoc]
    simp only [bind, Option.bind, pure, Bool.false_eq_true, Bool.or_false, Bool.false_or,
      ↓reduceIte, Nat.reduceAdd]
  · simp only [ByteArray.size_append, List.size_toByteArray, encoded, List.length_append,
      List.length_replicate, hs, natBytes, word_toBytesBE_length_32]
    change 4 + (32 + 32 + 32 + 32 + 32 + 32 + 64 * n) = _
    omega

theorem sizeBoundary :
    0 < (2 ^ 58 : Nat) ∧ 2 ^ 58 ≤ solcMaxU64 ∧
      228 + 32 * 2 ^ 58 < 2 ^ 64 ∧
      2 ^ 64 ≤ 196 + 64 * 2 ^ 58 ∧
      352 + 160 * 2 ^ 58 + (196 + 64 * 2 ^ 58) < UInt256.size := by
  decide +kernel

theorem outgoingRequestPreserved :
    ∃ payload, config.externalABI.encode? "multiRevoke" [oneRequest (2 ^ 58)] = some payload ∧
      payload.size = 2 ^ 64 + 196 ∧
      payload.readWithPadding 0 payload.size = payload := by
  obtain ⟨payload, henc, hs⟩ := oneRequestEncoded (2 ^ 58)
  refine ⟨payload, henc, ?_, ?_⟩
  · rw [hs]; decide +kernel
  · apply oversizedPayloadPreserved
    rw [hs]
    decide +kernel

end Benchmarks.EAS.Attester.ReadLimitAudit

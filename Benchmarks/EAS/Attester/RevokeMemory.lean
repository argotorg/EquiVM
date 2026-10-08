import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.Memory
import Benchmarks.EAS.Attester.RevokeSource
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def revokeMemory (schema uid : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem
    [(64, ⟨192⟩), (128, schema), (64, ⟨256⟩), (192, uid), (224, ⟨0⟩), (160, ⟨192⟩),
      (256, ⟨0x4692626700000000000000000000000000000000000000000000000000000000⟩),
      (260, schema), (292, uid), (324, ⟨0⟩)]

set_option maxHeartbeats 1000000 in
theorem revokeMemory_summary (schema uid : UInt256) :
    attesterRuntime_block_2187_memory (mem := solcFreePtrMem) (x0 := uid) (x1 := schema) =
      revokeMemory schema uid := by
  simp only [attesterRuntime_block_2187_memory]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint,
      show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  rfl

theorem revokeMemory_stack (schema uid : UInt256) (words : String → UInt256)
    (R : List UInt256) :
    attesterRuntime_block_2187_stack (immWords := words) (mem := solcFreePtrMem)
      (x0 := uid) (x1 := schema) (R := R) = words "_eas" :: ⟨256⟩ :: uid :: schema :: R := by
  simp only [attesterRuntime_block_2187_stack]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint,
      show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  rfl

theorem revokeMemory_size (schema uid : UInt256) : (revokeMemory schema uid).size = 356 := by
  simp only [revokeMemory, writeCascade, Reasoning.Theory.writeWord, wordWrite_size,
      solcFreePtrMem_size]
  rfl

theorem revokeMemory_freePtr (schema uid : UInt256) :
    memLoad (UInt256.ofNat 64) (revokeMemory schema uid) = ⟨256⟩ := by
  simp only [revokeMemory, writeCascade, Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]

theorem revokeMemory_read (schema uid : UInt256) :
    (revokeMemory schema uid).readWithPadding 256 100 =
      revokeSelector ++ schema.toByteArray ++ uid.toByteArray ++ (⟨0⟩ : UInt256).toByteArray := by
  let pre := writeCascade solcFreePtrMem
    [(64, ⟨192⟩), (128, schema), (64, ⟨256⟩), (192, uid), (224, ⟨0⟩), (160, ⟨192⟩)]
  have heq : revokeMemory schema uid = writeCascade pre
      [(256, ⟨0x4692626700000000000000000000000000000000000000000000000000000000⟩),
        (260, schema), (292, uid), (324, ⟨0⟩)] := by
    simp only [revokeMemory, pre, writeCascade]
  have h0 : (revokeMemory schema uid).readWithPadding 256 4 = revokeSelector := by
    rw [heq]
    change (writeCascade pre ((256,
      ⟨0x4692626700000000000000000000000000000000000000000000000000000000⟩) ::
        [(260, schema), (292, uid), (324, ⟨0⟩)])).readWithPadding (256 + 0) 4 = _
    rw [writeCascade_read_window_of_head]
    · native_decide
    · simp only [pre, writeCascade, Reasoning.Theory.writeWord, wordWrite_size,
        solcFreePtrMem_size]; native_decide
    · simp only [pre, writeCascade, Reasoning.Theory.writeWord, wordWrite_size, solcFreePtrMem_size,
        WindowDisjointFromWrites]; native_decide
    all_goals decide +kernel
  have h1 : (revokeMemory schema uid).readWithPadding 260 32 = schema.toByteArray := by
    rw [heq, writeCascade_cons]
    change (writeCascade (Reasoning.Theory.writeWord pre 256 _) [(260, schema), (292, uid), (324,
        ⟨0⟩)]).readWithPadding 260 32 = _
    apply sparseCascade_read_word
    simp
  have h2 : (revokeMemory schema uid).readWithPadding 292 32 = uid.toByteArray := by
    rw [heq, writeCascade_cons, writeCascade_cons]
    change (writeCascade (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord pre 256 _) 260
        schema) [(292, uid), (324, ⟨0⟩)]).readWithPadding 292 32 = _
    apply sparseCascade_read_word
    simp
  have h3 : (revokeMemory schema uid).readWithPadding 324 32 =
      (⟨0⟩ : UInt256).toByteArray := by
    exact writeWord_sparse_read_back _ _ _
  rw [show 100 = 4 + (32 + (32 + 32)) by rfl,
    byteArray_readWithPadding_split _ 256 4 96 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [revokeMemory_size]),
    byteArray_readWithPadding_split _ 260 32 64 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [revokeMemory_size]),
    byteArray_readWithPadding_split _ 292 32 32 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [revokeMemory_size]), h0, h1, h2, h3]
  simp only [ByteArray.append_assoc]

theorem revokeRequest_encoding (schema uid : UInt256) :
    config.externalABI.encode? "revoke" [revokeRequest schema uid] =
      some ((revokeMemory schema uid).readWithPadding 256 100) := by
  rw [revokeMemory_read]
  have ht (ts : List ABIType) (vs : List Value) :
      encodeABIValue? (.tuple ts) (.tuple vs) = encodeABIValues? ts vs := by
    simp only [encodeABIValue?]
  have hb (w : UInt256) : encodeABIValue? bytes32 (wordBytes32Value w) =
      some w.toByteArray.toList := encodeABIValue_bytes32_word w
  have hz : encodeABIValue? uint256 (.int 0) =
      some (⟨0⟩ : UInt256).toByteArray.toList := encodeABIValue_uint256_word ⟨0⟩
  have hd1 : isDynamicABIType bytes32 = false := rfl
  have hd2 : isDynamicABIType uint256 = false := rfl
  have hd3 : isDynamicABIType (.tuple [bytes32, uint256]) = false := rfl
  have hd4 : isDynamicABIType (.tuple [bytes32, .tuple [bytes32, uint256]]) = false := rfl
  have hh1 : abiTupleHeadSize? [bytes32, uint256] = some 64 := by native_decide
  have hh2 : abiTupleHeadSize? [bytes32, .tuple [bytes32, uint256]] = some 96 := by native_decide
  have hh3 : abiTupleHeadSize? [.tuple [bytes32, .tuple [bytes32, uint256]]] = some 96 := by
    native_decide
  change encodeCallWithSelector? revokeSelector [revocationRequestTy]
    [revokeRequest schema uid] = _
  simp only [encodeCallWithSelector?, revokeRequest, revocationRequestTy,
    revocationRequestDataTy, encodeABIValues?, encodeABIValuesFrom?, ht, hb, hz,
    hh1, hh2, hh3, hd1, hd2, hd3, hd4, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil, list_toByteArray_append, byteArray_toList_toByteArray,
    ByteArray.append_assoc]

end Benchmarks.EAS.Attester

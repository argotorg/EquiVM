import Benchmarks.UniswapV4PoolManager.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: deployment shape for a single address constructor parameter.
theorem addressConstructorDeploymentShape {name : Ident} {initcode code : ByteArray} {args : List Value}
    (h : genSolidityConstructorDeployment [⟨name, .elem .address⟩] initcode args = some code) :
    ∃ a : AccountAddress, args = [.address a] ∧ code = initcode ++ (UInt256.ofNat a.val).toByteArray := by
  cases args with
  | nil =>
    simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
      staticABIEncodedSize?, isDynamicABIType] at h
  | cons arg rest =>
    cases rest with
    | cons _ _ =>
      cases arg <;> simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
        staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
    | nil =>
      cases arg <;> simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
        staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      rename_i a
      refine ⟨a, rfl, ?_⟩
      rw [← h, word_toBytesBE_toByteArray_eq_toByteArray]
      rfl

-- LIBRARY CANDIDATE: relocating a word patch into the suffix of a byte array.
theorem writeWord_appendRight (pre base : ByteArray) (off : Nat) (word : UInt256)
    (hoff : off ≤ base.size) :
    writeWord (pre ++ base) (pre.size + off) word = pre ++ writeWord base off word := by
  unfold Reasoning.Theory.writeWord
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [ByteArray.size_append]; omega),
    write32_eq _ _ _ (by rw [toByteArray_size]) hoff]
  rw [extract_append_span _ _ _ _ (by omega) (by omega), byteArray_extract_self,
    extract_append_right_window _ _ _ _ (by omega), ByteArray.size_append]
  simp only [Nat.add_sub_cancel_left, Nat.add_assoc, ByteArray.append_assoc]


end Benchmarks.UniswapV4PoolManager

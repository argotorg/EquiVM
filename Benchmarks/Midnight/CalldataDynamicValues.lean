import Benchmarks.Midnight.CalldataArrayWords
import Benchmarks.Midnight.BytesCalldataDecode
import Benchmarks.Midnight.CalldataSliceBounds
import Benchmarks.Midnight.MarketCalldataFields

/-! Dynamic top-level calldata arguments, with scalar arrays retained as word lists. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

instance (isBytes : Bool) (bytes : ByteArray) (head : UInt256) :
    Decidable (CalldataSliceValid isBytes bytes head) := by
  unfold CalldataSliceValid
  infer_instance

def decodeCalldataArrayWords (bytes : ByteArray) (head : Nat) : Option (List UInt256) :=
  let off := (calldataWord bytes head).toNat
  if off < 2^64 then
    let start := 4 + off
    if CalldataSliceValid false bytes (UInt256.ofNat start) then
      some (calldataArrayWords bytes (calldataWord bytes start).toNat (start + 32))
    else none
  else none

def decodeCalldataAddressWords (bytes : ByteArray) (head : Nat) : Option (List UInt256) := do
  let words ← decodeCalldataArrayWords bytes head
  if CanonicalAddressWords words then some words else none

def decodeCalldataBytes (bytes : ByteArray) (head : Nat) : Option ByteArray :=
  let off := (calldataWord bytes head).toNat
  if off < 2^64 then
    let start := 4 + off
    if CalldataSliceValid true bytes (UInt256.ofNat start) then
      some (bytes.extract (start + 32) (start + 32 + (calldataWord bytes start).toNat))
    else none
  else none

theorem solcDecodeFields_u256Array {bytes : ByteArray} {types : List ABIType} {cursor : Nat}
    (hbound : 4 + cursor + 32 ≤ bytes.size) (hsize : bytes.size < UInt256.size) :
    decodeFields? (.dynamicArray Model.u256 :: types) bytes.toList 4 cursor [] true = (do
      let words ← decodeCalldataArrayWords bytes (4 + cursor)
      let rest ← decodeFields? types bytes.toList 4 (cursor + 32) [] true
      pure (.array (wordArrayValues words) :: rest)) := by
  rw [solcDecodeFields_dynamic _ rfl rfl hbound hsize (by decide)]
  simp only [List.tail_nil]
  unfold decodeCalldataArrayWords
  by_cases ho : (calldataWord bytes (4 + cursor)).toNat < 2^64
  · have hn : ¬ solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat := by
      change ¬ (2^64 - 1 < _); omega
    have hstart : 4 + (calldataWord bytes (4 + cursor)).toNat < 2^128 := by omega
    simp only [ho, hn, if_false, if_true]
    simp only [Model.u256]
    rw [solcScalarArrayValue (.int (.uint ⟨256, by decide⟩)) rfl (by decide) hsize hstart]
    simp only [CalldataSliceValid, show calldataSliceStride false = 32 from rfl,
      UInt256.toNat_ofNat_of_lt (lt_trans hstart (by decide : 2^128 < UInt256.size))]
    have hd := decodeCalldataWordElements_u256 bytes
      (calldataWord bytes (4 + (calldataWord bytes (4 + cursor)).toNat)).toNat
      (4 + (calldataWord bytes (4 + cursor)).toNat + 32)
    dsimp only [Model.u256] at hd
    rw [hd]
    split <;> rfl
  · have hn : solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat := by
      change 2^64 - 1 < _; omega
    simp only [ho, hn, if_false, if_true, bind, Option.bind]

theorem solcDecodeFields_addressArray {bytes : ByteArray} {types : List ABIType} {cursor : Nat}
    (hbound : 4 + cursor + 32 ≤ bytes.size) (hsize : bytes.size < UInt256.size) :
    decodeFields? (.dynamicArray Model.addr :: types) bytes.toList 4 cursor [] true = (do
      let words ← decodeCalldataAddressWords bytes (4 + cursor)
      let rest ← decodeFields? types bytes.toList 4 (cursor + 32) [] true
      pure (.array (addressWordArrayValues words) :: rest)) := by
  rw [solcDecodeFields_dynamic _ rfl rfl hbound hsize (by decide)]
  simp only [List.tail_nil]
  unfold decodeCalldataAddressWords decodeCalldataArrayWords
  by_cases ho : (calldataWord bytes (4 + cursor)).toNat < 2^64
  · have hn : ¬ solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat := by
      change ¬ (2^64 - 1 < _); omega
    have hstart : 4 + (calldataWord bytes (4 + cursor)).toNat < 2^128 := by omega
    simp only [ho, hn, if_false, if_true]
    simp only [Model.addr]
    rw [solcScalarArrayValue .address rfl (by decide) hsize hstart]
    simp only [CalldataSliceValid, show calldataSliceStride false = 32 from rfl,
      UInt256.toNat_ofNat_of_lt (lt_trans hstart (by decide : 2^128 < UInt256.size))]
    have hd := decodeCalldataWordElements_address bytes
      (calldataWord bytes (4 + (calldataWord bytes (4 + cursor)).toNat)).toNat
      (4 + (calldataWord bytes (4 + cursor)).toNat + 32)
    dsimp only [Model.addr] at hd
    rw [hd]
    split
    · by_cases hc : CanonicalAddressWords
          (calldataArrayWords bytes
            (calldataWord bytes (4 + (calldataWord bytes (4 + cursor)).toNat)).toNat
            (4 + (calldataWord bytes (4 + cursor)).toNat + 32)) <;>
        simp only [hc, if_true, if_false, Option.map, bind, Option.bind]
    · rfl
  · have hn : solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat := by
      change 2^64 - 1 < _; omega
    simp only [ho, hn, if_false, if_true, bind, Option.bind]

theorem solcDecodeFields_bytes {bytes : ByteArray} {types : List ABIType} {cursor : Nat}
    (hbound : 4 + cursor + 32 ≤ bytes.size) (hsize : bytes.size < UInt256.size) :
    decodeFields? (.bytes :: types) bytes.toList 4 cursor [] true = (do
      let data ← decodeCalldataBytes bytes (4 + cursor)
      let rest ← decodeFields? types bytes.toList 4 (cursor + 32) [] true
      pure (.bytes data :: rest)) := by
  rw [solcDecodeFields_dynamic _ rfl rfl hbound hsize (by decide)]
  simp only [List.tail_nil]
  unfold decodeCalldataBytes
  by_cases ho : (calldataWord bytes (4 + cursor)).toNat < 2^64
  · have hn : ¬ solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat := by
      change ¬ (2^64 - 1 < _); omega
    have hstart : 4 + (calldataWord bytes (4 + cursor)).toNat < 2^128 := by omega
    simp only [ho, hn, if_false, if_true, solcBytesValue hsize hstart,
      CalldataSliceValid, show calldataSliceStride true = 1 from rfl, Nat.one_mul,
      UInt256.toNat_ofNat_of_lt (lt_trans hstart (by decide : 2^128 < UInt256.size))]
    split <;> rfl
  · have hn : solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat := by
      change 2^64 - 1 < _; omega
    simp only [ho, hn, if_false, if_true, bind, Option.bind]

end Benchmarks.Midnight

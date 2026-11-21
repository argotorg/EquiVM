import Benchmarks.Midnight.CalldataDynamicValues

/-! Materialized byte strings at an arbitrary tuple base. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: materialized bytes with their signed extent and uint64 length checks.
def decodeBytesAt (bytes : ByteArray) (start : Nat) : Option ByteArray :=
  if bytes.size < 2^255 ∧ start + 32 ≤ bytes.size ∧
      (calldataWord bytes start).toNat < 2^64 ∧
      start + 32 + (calldataWord bytes start).toNat ≤ bytes.size then
    some (bytes.extract (start + 32) (start + 32 + (calldataWord bytes start).toNat))
  else none

-- LIBRARY CANDIDATE: a byte-string pointer relative to an arbitrary tuple base.
def decodeRelativeBytes (bytes : ByteArray) (base cursor : Nat) : Option ByteArray :=
  let relative := (calldataWord bytes (base + cursor)).toNat
  if relative < 2^64 then decodeBytesAt bytes (base + relative) else none

theorem decodeBytesAt_success {bytes data : ByteArray} {start : Nat}
    (h : decodeBytesAt bytes start = some data) :
    bytes.size < 2^255 ∧ start + 32 ≤ bytes.size ∧
      (calldataWord bytes start).toNat < 2^64 ∧
      start + 32 + (calldataWord bytes start).toNat ≤ bytes.size ∧
      data = bytes.extract (start + 32) (start + 32 + (calldataWord bytes start).toNat) ∧
      data.size = (calldataWord bytes start).toNat := by
  unfold decodeBytesAt at h
  split at h
  · rename_i hv
    cases h
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, rfl, by
      rw [ByteArray.size_extract]; omega⟩
  · cases h

theorem solcDecodeBytesAt {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < UInt256.size) (hstart : start < 2^128) :
    decodeValue? .bytes bytes.toList start {} = (decodeBytesAt bytes start).map Value.bytes := by
  rw [solcBytesValue hsize hstart]
  unfold decodeBytesAt
  split <;> rfl

-- GENERALIZES solcDecodeFields_bytes to nested tuple heads.
theorem solcDecodeFields_relativeBytes {bytes : ByteArray} {types : List ABIType}
    {base cursor : Nat} {plans : List CalldataPlan}
    (hplan : plans.headD {} = {}) (hbase : base < 2^127)
    (hbound : base + cursor + 32 ≤ bytes.size) (hsize : bytes.size < UInt256.size) :
    decodeFields? (.bytes :: types) bytes.toList base cursor plans true = (do
      let data ← decodeRelativeBytes bytes base cursor
      let rest ← decodeFields? types bytes.toList base (cursor + 32) plans.tail true
      pure (.bytes data :: rest)) := by
  rw [solcDecodeFields_dynamic _ rfl hplan hbound hsize
    (by change base + 2^64 < 2^256; omega)]
  unfold decodeRelativeBytes
  by_cases ho : (calldataWord bytes (base + cursor)).toNat < 2^64
  · have hn : ¬ solcMaxU64 < (calldataWord bytes (base + cursor)).toNat := by
      change ¬ (2^64 - 1 < _)
      omega
    simp only [ho, hn, if_false, if_true]
    rw [solcDecodeBytesAt (start := base + (calldataWord bytes (base + cursor)).toNat)
      hsize (by omega)]
    cases decodeBytesAt bytes (base + (calldataWord bytes (base + cursor)).toNat) <;> rfl
  · have hn : solcMaxU64 < (calldataWord bytes (base + cursor)).toNat := by
      change 2^64 - 1 < _
      omega
    simp only [ho, hn, if_false, if_true, bind, Option.bind]

end Benchmarks.Midnight

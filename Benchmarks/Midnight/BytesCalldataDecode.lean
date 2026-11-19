import Benchmarks.Midnight.CalldataExtent
import Benchmarks.Midnight.CollateralDecodeSlice

/-! Byte-slice values in the materialized Solidity calldata decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem solcBytesPayload {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < UInt256.size)
    (hcap : (calldataWord bytes start).toNat < 2^64)
    (hbound : start + 32 + (calldataWord bytes start).toNat ≤ bytes.size) :
    (decodeABIValue? .bytes
      (solcReadBytes bytes.toList start (32 + (calldataWord bytes start).toNat)) 0).map Prod.fst =
      some (.bytes (bytes.extract (start + 32)
        (start + 32 + (calldataWord bytes start).toNat))) := by
  let len := (calldataWord bytes start).toNat
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  rw [solcReadBytes_bounded (bytes := bytes.toList) (start := start)
    (len := 32 + len) (by rw [hl]; omega) (by rw [hl]; exact hsize)]
  have hhead : readNat? ((bytes.toList.drop start).take (32 + len)) 0 = some len := by
    have he : (bytes.toList.drop start).take (32 + len) =
        (bytes.extract start (start + 32 + len)).toList := by
      rw [extract_toList]
      congr 1
      omega
    rw [he, readNat_bytes (by rw [ByteArray.size_extract]; omega),
      calldataWord_extract (by omega) hbound]
    rfl
  have hp : readBytes? ((bytes.toList.drop start).take (32 + len)) 32 len =
      some ((bytes.toList.drop (start + 32)).take len) := by
    have hlen : ((bytes.toList.drop (start + 32)).take len).length = len := by
      simp only [List.length_take, List.length_drop, hl]
      omega
    simp only [readBytes?, List.drop_take, List.drop_drop,
      show 32 + len - 32 = len by omega, List.take_take, Nat.min_self, hlen, if_true]
  have hmax : ¬ solcMaxLen .modern < len := by
    change ¬ (2^64 - 1 < len)
    change len < 2^64 at hcap
    omega
  rw [decodeABIValue?, hhead]
  simp only [bind, Option.bind, hmax, if_false, hp, Option.map]
  congr 2
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have he : (bytes.extract (start + 32) (start + 32 + len)).toList =
      (bytes.toList.drop (start + 32)).take len := by
    rw [extract_toList, show start + 32 + len - (start + 32) = len by omega]
  simpa only [byteArray_toList_eq, List.toList_toArray] using he.symm

theorem solcBytesValue {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < UInt256.size) (hstart : start < 2^128) :
    decodeValue? .bytes bytes.toList start {} =
      if bytes.size < 2^255 ∧ start + 32 ≤ bytes.size ∧
          (calldataWord bytes start).toNat < 2^64 ∧
          start + 32 + (calldataWord bytes start).toNat ≤ bytes.size then
        some (.bytes (bytes.extract (start + 32)
          (start + 32 + (calldataWord bytes start).toNat)))
      else none := by
  rw [decodeValue?]
  by_cases hh : bytes.size < 2^255 ∧ start + 32 ≤ bytes.size
  · rw [solcReadNat_bounded hh.2 hsize]
    by_cases hn : solcMaxU64 < (calldataWord bytes start).toNat
    · have hcap : ¬ (calldataWord bytes start).toNat < 2^64 := by
        change 2^64 - 1 < _ at hn
        omega
      simp only [hn, decide_true, Bool.true_or, if_true, hcap, false_and, and_false,
        if_false]
    · have hcap : (calldataWord bytes start).toNat < 2^64 := by
        change ¬ (2^64 - 1 < _) at hn
        omega
      simp only [hn, decide_false, Bool.false_or, isMemory,
        show ({} : CalldataPlan).materialize.contains [] = true from rfl,
        solcMaterializedBadExtent hh.1 hstart hcap (by decide : 1 ≤ 128), Nat.one_mul]
      by_cases he : start + 32 + (calldataWord bytes start).toNat ≤ bytes.size
      · simp only [show ¬ bytes.size < start + 32 + (calldataWord bytes start).toNat
            from by omega, decide_false, Bool.false_eq_true, if_false,
          hh.1, hh.2, hcap, he, and_self, if_true]
        exact solcBytesPayload hsize hcap he
      · simp only [show bytes.size < start + 32 + (calldataWord bytes start).toNat
            from by omega, decide_true, if_true, he, and_false, if_false]
  · have hb := solcMaterializedHead_reject hsize hstart hh
      (solcReadNat bytes.toList start) 1
    change badExtent (isMemory {}) false bytes.toList start
      (solcReadNat bytes.toList start) 1 = true at hb
    rw [hb]
    simp only [Bool.or_true, if_true]
    rw [if_neg (fun h ↦ hh ⟨h.1, h.2.1⟩)]

end Benchmarks.Midnight

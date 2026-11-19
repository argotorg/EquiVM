import Benchmarks.Midnight.MulticallArrayDecode
import Benchmarks.Midnight.CalldataExtent

/-! The outer calldata-array header for multicall. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem solcMulticallArrayValue {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < UInt256.size) (hstart : start < 2^128) :
    decodeValue? (.dynamicArray .bytes) bytes.toList start { materialize := [] } =
      if bytes.size < 2^255 ∧ start + 32 ≤ bytes.size ∧
          (calldataWord bytes start).toNat < 2^64 ∧
          start + 32 + 32 * (calldataWord bytes start).toNat ≤ bytes.size then
        (decodeMulticallTails bytes (UInt256.ofNat (start + 32)) 0
          (calldataWord bytes start).toNat).map (fun vs ↦ .array (vs.map Value.bytes))
      else none := by
  rw [decodeValue?]
  simp only [stride?, isDynamicABIType, if_true,
    bind, Option.bind]
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
      simp only [hn, decide_false, Bool.false_or,
        show isMemory { materialize := [] } = false from rfl,
        show badExtent false false bytes.toList start (calldataWord bytes start).toNat 32 =
          badExtent true false bytes.toList start (calldataWord bytes start).toNat 32 from rfl,
        solcMaterializedBadExtent hh.1 hstart hcap (by decide : 32 ≤ 128)]
      by_cases he : start + 32 + 32 * (calldataWord bytes start).toNat ≤ bytes.size
      · have ha : solcAdd start 32 = start + 32 := Nat.mod_eq_of_lt (by
          change start + 32 < 2^256; omega)
        simp only [show ¬ bytes.size < start + 32 + 32 * (calldataWord bytes start).toNat
            from by omega, decide_false, Bool.false_eq_true, if_false,
          hh.1, hh.2, hcap, he, and_self, if_true, ha,
          Bool.not_true, Bool.false_and]
        have hp : (UInt256.ofNat (start + 32)).toNat = start + 32 :=
          UInt256.toNat_ofNat_of_lt (by change start + 32 < 2^256; omega)
        have hd := solcMulticallElements (base := UInt256.ofNat (start + 32))
          (start := 0) (count := (calldataWord bytes start).toNat) hh.1
          (by rw [hp]; simpa only [Nat.zero_add] using he)
        simp only [hp, Nat.mul_zero] at hd
        rw [hd]
        cases decodeMulticallTails bytes (UInt256.ofNat (start + 32)) 0
          (calldataWord bytes start).toNat <;> rfl
      · simp only [show bytes.size < start + 32 + 32 * (calldataWord bytes start).toNat
            from by omega, decide_true, if_true, he, and_false, if_false]
  · have hb := solcMaterializedHead_reject hsize hstart hh
      (solcReadNat bytes.toList start) 32
    change badExtent (isMemory { materialize := [] }) false bytes.toList start
      (solcReadNat bytes.toList start) 32 = true at hb
    rw [hb]
    simp only [Bool.or_true, if_true]
    rw [if_neg (fun h ↦ hh ⟨h.1, h.2.1⟩)]

end Benchmarks.Midnight

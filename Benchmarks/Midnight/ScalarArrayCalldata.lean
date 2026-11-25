import Benchmarks.Midnight.ScalarArrayDecode
import Benchmarks.Midnight.CalldataExtent

/-! Typed scalar arrays and their length/extent checks in Solidity calldata. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem solcScalarArrayValue (ty : ElemType) (hty : isABIScalarWordType (.elem ty) = true)
    (hbool : ty ≠ .bool)
    {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < UInt256.size) (hstart : start < 2^128) :
    decodeValue? (.dynamicArray (.elem ty)) bytes.toList start {} =
      if bytes.size < 2^255 ∧ start + 32 ≤ bytes.size ∧
          (calldataWord bytes start).toNat < 2^64 ∧
          start + 32 + 32 * (calldataWord bytes start).toNat ≤ bytes.size then
        (decodeCalldataWordElements (.elem ty) (calldataWord bytes start).toNat
          bytes (start + 32)).map Value.array
      else none := by
  rw [decodeValue?]
  simp only [stride?, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind]
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
        solcMaterializedBadExtent hh.1 hstart hcap (by decide : 32 ≤ 128)]
      by_cases he : start + 32 + 32 * (calldataWord bytes start).toNat ≤ bytes.size
      · have ha : solcAdd start 32 = start + 32 := Nat.mod_eq_of_lt (by
          change start + 32 < 2^256; omega)
        simp only [show ¬ bytes.size < start + 32 + 32 * (calldataWord bytes start).toNat
            from by omega, decide_false, Bool.false_eq_true, if_false,
          hh.1, hh.2, hcap, he, and_self, if_true, ha,
          show (child ({} : CalldataPlan) .element).deferErrors.isEmpty = true from rfl,
          Bool.not_false, Bool.true_and,
          show (calldataWord bytes start).toNat * 32 / 32 =
            (calldataWord bytes start).toNat by omega]
        cases ty with
        | bool => exact False.elim (hbool rfl)
        | bytes width => cases hty
        | function => cases hty
        | fixed fixedTy =>
          rw [decodeCalldataWords (ty := .elem (.fixed fixedTy)) rfl he hsize]
          cases decodeCalldataWordElements (.elem (.fixed fixedTy))
            (calldataWord bytes start).toNat bytes (start + 32) <;> rfl
        | address =>
          rw [decodeCalldataWords (ty := .elem .address) rfl he hsize]
          cases decodeCalldataWordElements (.elem .address) (calldataWord bytes start).toNat
            bytes (start + 32) <;> rfl
        | int bits =>
          rw [decodeCalldataWords (ty := .elem (.int bits)) rfl he hsize]
          cases decodeCalldataWordElements (.elem (.int bits)) (calldataWord bytes start).toNat
            bytes (start + 32) <;> rfl
      · simp only [show bytes.size < start + 32 + 32 * (calldataWord bytes start).toNat
            from by omega, decide_true, if_true, he, and_false, if_false]
  · have hb := solcMaterializedHead_reject hsize hstart hh
      (solcReadNat bytes.toList start) 32
    change badExtent (isMemory {}) false bytes.toList start
      (solcReadNat bytes.toList start) 32 = true at hb
    rw [hb]
    simp only [Bool.or_true, if_true]
    rw [if_neg (fun h ↦ hh ⟨h.1, h.2.1⟩)]

end Benchmarks.Midnight

import Reasoning.Initcode
import Solm.Refine

open Solm ABI Ethereum Reasoning.Theory

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: Reasoning.Immutables — extract typed immutable values without
-- repeating the Value constructor cases in each contract's valuation bridge.
theorem immutablesFit_address {C : ContractDecl} {imms : Store} {name : Ident}
    (hfit : immutablesFit C imms) (hdecl : ⟨name, .address⟩ ∈ C.immutables) :
    ∃ a : EVM.Address, imms.get? name = some (.address a) := by
  obtain ⟨value, hget, hvalue⟩ := hfit _ hdecl
  cases value <;> simp_all [elemValueFits]

-- LIBRARY CANDIDATE: Reasoning.Immutables — preserve the declared unsigned width
-- when turning an immutable's unbounded source integer into an EVM word.
theorem immutablesFit_uint {C : ContractDecl} {imms : Store} {name : Ident}
    {bits : ABI.BitWidth} (hfit : immutablesFit C imms)
    (hdecl : ⟨name, .int (.uint bits)⟩ ∈ C.immutables) :
    ∃ w : EVM.Word, imms.get? name = some (.int (Int.ofNat w.toNat)) ∧
      w.toNat < 2 ^ bits.val := by
  obtain ⟨value, hget, hvalue⟩ := hfit _ hdecl
  cases value <;> simp only [elemValueFits, Bool.false_eq_true] at hvalue
  rename_i i
  simp only [decide_eq_true_eq] at hvalue
  have hsize : i < Int.ofNat (EVM.twoPow 256) := by
    have hp : (2 : Int) ^ bits.val ≤ 2 ^ 256 :=
      pow_le_pow_right₀ (by decide) bits.property.2.1
    exact lt_of_lt_of_le hvalue.2 hp
  have hword := constructorUInt256Word_toNat i hvalue.1 hsize
  have hi : Int.ofNat i.toNat = i := Int.toNat_of_nonneg hvalue.1
  refine ⟨EVM.word i.toNat, ?_, ?_⟩
  · simpa only [hword, hi] using hget
  · rw [hword]
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_pow, Int.toNat_of_nonneg hvalue.1]
      using hvalue.2

end Benchmarks.CompoundIII.Comet

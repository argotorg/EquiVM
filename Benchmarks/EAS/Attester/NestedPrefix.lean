import Benchmarks.EAS.Attester.NestedBounds
import Benchmarks.EAS.Attester.Selectors

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: a nonzero selector suffix cannot be a uint64 length word.
theorem calldata_uint64_past_selector {cd sel : ByteArray} {off : Nat}
    (hsel : cd.extract 0 4 = sel)
    (hprefix : ∀ j : Fin 4, 0 < fromByteArrayBigEndian (sel.extract j.val 4))
    (hin : off + 32 ≤ cd.size) (hlen : (calldataWord cd off).toNat ≤ solcMaxU64) :
    4 ≤ off := by
  by_contra hoff
  have ho : off < 4 := by omega
  have hp : 0 < fromByteArrayBigEndian (cd.extract off 4) := by
    have he : cd.extract off 4 = (cd.extract 0 4).extract off 4 := by
      rw [ByteArray.extract_extract]
      simp only [Nat.zero_add, Nat.min_self]
    rw [he, hsel]
    exact hprefix ⟨off, ho⟩
  have ht : (cd.extract 4 (off + 32)).size = off + 28 := by
    rw [ByteArray.size_extract]
    omega
  have hs : cd.extract off (off + 32) = cd.extract off 4 ++ cd.extract 4 (off + 32) := by
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
  have hw : (calldataWord cd off).toNat =
      fromByteArrayBigEndian (cd.extract off 4) * 2 ^ (8 * (off + 28)) +
        fromByteArrayBigEndian (cd.extract 4 (off + 32)) := by
    rw [← fromByteArrayBigEndian_toByteArray (calldataWord cd off),
      calldataWord_bytes_at hin, hs, fromByteArrayBigEndian_append, ht]
  have hpow : 2 ^ 224 ≤ 2 ^ (8 * (off + 28)) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hprod : 2 ^ (8 * (off + 28)) ≤
      fromByteArrayBigEndian (cd.extract off 4) * 2 ^ (8 * (off + 28)) := by
    exact Nat.le_mul_of_pos_left _ hp
  change (calldataWord cd off).toNat ≤ 18446744073709551615 at hlen
  omega

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

theorem multiRevoke_uint64_past_selector {cd : ByteArray} {off : Nat}
    (hsel : cd.extract 0 4 = attesterMultiRevokeSelBytes)
    (hin : off + 32 ≤ cd.size) (hlen : (calldataWord cd off).toNat ≤ solcMaxU64) :
    4 ≤ off :=
  calldata_uint64_past_selector hsel (by decide +kernel) hin hlen

theorem multiAttest_uint64_past_selector {cd : ByteArray} {off : Nat}
    (hsel : cd.extract 0 4 = attesterMultiAttestSelBytes)
    (hin : off + 32 ≤ cd.size) (hlen : (calldataWord cd off).toNat ≤ solcMaxU64) :
    4 ≤ off :=
  calldata_uint64_past_selector hsel (by decide +kernel) hin hlen

end Benchmarks.EAS.Attester

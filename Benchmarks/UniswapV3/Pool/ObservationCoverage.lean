import Benchmarks.UniswapV3.Pool.OracleTransformMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem observationLoadExpansion {aw free ptr : UInt256} (ha : ActiveWords aw)
    (hb : free.toNat ≤ 2 ^ 200) (hend : ptr.toNat + 128 ≤ free.toNat)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) :
    M aw ptr ⟨32⟩ = aw ∧ M aw (ptr + UInt256.ofNat 32) ⟨32⟩ = aw ∧
      M aw (ptr + UInt256.ofNat 64) ⟨32⟩ = aw := by
  have hload (n : Nat) (hn : n ≤ 64) : M aw (ptr + UInt256.ofNat n) ⟨32⟩ = aw := by
    have hp : (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
      uadd_word_ofNat_toNat ptr n (by change _ < 2 ^ 256; omega)
    exact expandedWords32_eq_of_cover ha (by rw [hp]; omega) (by rw [hp]; omega)
  refine ⟨?_, hload 32 (by decide), hload 64 (by decide)⟩
  simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
    using hload 0 (by decide)

end Benchmarks.UniswapV3.Pool

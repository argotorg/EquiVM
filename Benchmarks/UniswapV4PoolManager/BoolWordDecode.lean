import Benchmarks.UniswapV4PoolManager.WordBoolean
import Benchmarks.UniswapV4PoolManager.PoolKeyABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the modern ABI accepts precisely the two canonical Boolean words.
theorem decodeBoolWord (w : UInt256) :
    decodeABIWord? (.elem .bool) w =
      if w = ⟨0⟩ ∨ w = ⟨1⟩ then some (.bool (decide (w ≠ ⟨0⟩))) else none := by
  by_cases hz : w = ⟨0⟩
  · subst w; decide
  by_cases ho : w = ⟨1⟩
  · subst w; decide
  have hn0 : w.toNat ≠ 0 := fun he => hz (uint256_toNat_eq_zero he)
  have hn1 : w.toNat ≠ 1 := fun he => ho (u256_inj he)
  change (if w.toNat = 0 then some (Value.bool false) else if w.toNat = 1 then some (Value.bool true) else none) = _
  rw [if_neg hn0, if_neg hn1, if_neg (fun hh => hh.elim hz ho)]

theorem canonicalBoolWord {w : UInt256} (h : w = ⟨0⟩ ∨ w = ⟨1⟩) :
    UInt256.fromBool (decide (w ≠ ⟨0⟩)) = w := by
  rcases h with rfl | rfl <;> decide

end Benchmarks.UniswapV4PoolManager

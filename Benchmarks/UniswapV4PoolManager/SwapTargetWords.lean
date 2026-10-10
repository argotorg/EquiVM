import Benchmarks.UniswapV4PoolManager.WordXorSelect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapTargetWord (zeroForOne : Bool) (next limit : UInt256) : UInt256 :=
  if zeroForOne then if next.toNat < limit.toNat then limit else next
  else if limit.toNat < next.toNat then limit else next

def swapTargetCompiled (zeroForOne : Bool) (next limit : UInt256) : UInt256 :=
  UInt256.xor (UInt256.mul (UInt256.xor next limit)
    (UInt256.xor (UInt256.lt next limit) (if zeroForOne then ⟨1⟩ else ⟨0⟩))) limit

theorem swapTargetWord_canonical {zeroForOne : Bool} {next limit : UInt256}
    (hn : next.toNat < 2^160) (hl : limit.toNat < 2^160) :
    (swapTargetWord zeroForOne next limit).toNat < 2^160 := by
  unfold swapTargetWord
  split <;> split <;> assumption

theorem swapTargetCompiled_eq (zeroForOne : Bool) (next limit : UInt256) :
    swapTargetCompiled zeroForOne next limit = swapTargetWord zeroForOne next limit := by
  have hs0 : UInt256.xor (UInt256.mul (UInt256.xor next limit) ⟨0⟩) limit = limit :=
    wordXorSelect next limit false
  have hs1 : UInt256.xor (UInt256.mul (UInt256.xor next limit) ⟨1⟩) limit = next :=
    wordXorSelect next limit true
  cases zeroForOne with
  | false =>
    simp only [swapTargetCompiled, swapTargetWord, Bool.false_eq_true, if_false]
    by_cases hlt : next.toNat < limit.toNat
    · rw [ult_one hlt]
      have hx : UInt256.xor (⟨1⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by decide +kernel
      rw [hx, hs1, if_neg (by omega)]
    · rw [ult_zero (Nat.le_of_not_gt hlt)]
      have hx : UInt256.xor (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ := by decide +kernel
      rw [hx, hs0]
      by_cases hgt : limit.toNat < next.toNat
      · rw [if_pos hgt]
      · rw [if_neg hgt]
        apply u256_inj
        omega
  | true =>
    simp only [swapTargetCompiled, swapTargetWord, if_true]
    by_cases hlt : next.toNat < limit.toNat
    · rw [ult_one hlt, if_pos hlt]
      have hx : UInt256.xor (⟨1⟩ : UInt256) ⟨1⟩ = ⟨0⟩ := by decide +kernel
      rw [hx, hs0]
    · rw [ult_zero (Nat.le_of_not_gt hlt), if_neg hlt]
      have hx : UInt256.xor (⟨0⟩ : UInt256) ⟨1⟩ = ⟨1⟩ := by decide +kernel
      rw [hx, hs1]

end Benchmarks.UniswapV4PoolManager

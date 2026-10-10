import Benchmarks.UniswapV4PoolManager.SignedWordBounds
import Benchmarks.UniswapV4PoolManager.WordSignedRepresentation
import Benchmarks.UniswapV4PoolManager.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: subtracting a nonnegative signed word overflows exactly when its result increases.
theorem signedSubNonnegFits_iff (a b : UInt256) (hb : 0 ≤ EVM.signed b) :
    int256Fits (EVM.signed a-EVM.signed b) ↔ EVM.signed (UInt256.sub a b) ≤ EVM.signed a := by
  have ha := signedWord_fits a
  have hb' := signedWord_fits b
  rw [← wordOfInt_signed_sub, ← normalizeSignedWordOfInt]
  change (-(2^255 : Int) ≤ EVM.signed a-EVM.signed b ∧ EVM.signed a-EVM.signed b < 2^255) ↔
    (if (EVM.signed a-EVM.signed b) % (2^256 : Int) < 2^255 then
      (EVM.signed a-EVM.signed b) % (2^256 : Int) else (EVM.signed a-EVM.signed b) % (2^256 : Int)-2^256) ≤ EVM.signed a
  unfold int256Fits at ha hb'
  split_ifs <;> omega

-- LIBRARY CANDIDATE: the optimized checked subtraction guard for a nonnegative operand.
theorem signedSubNonnegGuard (a b : UInt256) (hb : 0 ≤ EVM.signed b) :
    UInt256.land (UInt256.ofNat 1) (UInt256.sgt (UInt256.sub a b) a) =
      UInt256.fromBool (decide (¬int256Fits (EVM.signed a-EVM.signed b))) := by
  rw [sgt_signed]
  have he := signedSubNonnegFits_iff a b hb
  by_cases hf : int256Fits (EVM.signed a-EVM.signed b)
  · rw [decide_eq_false (not_lt_of_ge (he.mp hf)), decide_eq_false (not_not_intro hf)]
    rfl
  · rw [decide_eq_true (lt_of_not_ge (fun hh => hf (he.mpr hh))), decide_eq_true hf]
    rfl

end Benchmarks.UniswapV4PoolManager

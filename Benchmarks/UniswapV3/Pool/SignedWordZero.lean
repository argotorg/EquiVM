import Benchmarks.UniswapV3.Pool.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: zero tests are faithful on the signed EVM range.
theorem wordOfInt_zero_iff_signed (i : Int)
    (hlo : -(2 ^ 255 : Int) ≤ i) (hhi : i < 2 ^ 255) :
    EVM.wordOfInt i = ⟨0⟩ ↔ i = 0 := by
  constructor
  · intro h
    have hi := wordOfInt_signed_value i hlo hhi
    rw [h] at hi
    exact hi
  · rintro rfl
    rfl

end Benchmarks.UniswapV3.Pool

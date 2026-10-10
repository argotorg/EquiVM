import Benchmarks.UniswapV3.Pool.ModularWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: removing an intermediate fixed-width multiplication cast.
theorem normalizeInt_mul_right (ty : ABI.IntType) (i j : Int) :
    normalizeInt ty (i * normalizeInt ty j) = normalizeInt ty (i * j) := by
  have hr : (i * normalizeInt ty j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) =
      (i * j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) := by
    rw [Int.mul_emod, normalizeInt_residue, ← Int.mul_emod]
  cases ty with
  | uint width => exact hr
  | sint width => simp only [normalizeInt, IntType.bitWidth] at hr ⊢; rw [hr]

end Benchmarks.UniswapV3.Pool

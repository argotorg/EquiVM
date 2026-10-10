import Benchmarks.UniswapV4PoolManager.WordSignedRepresentation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: congruent integers encode as the same EVM word.
theorem wordOfInt_mod_congr {x y : Int} (h : x % (2^256 : Int) = y % (2^256 : Int)) :
    EVM.wordOfInt x = EVM.wordOfInt y := by
  rw [wordOfInt_eq_mod, wordOfInt_eq_mod]
  exact congrArg (fun z : Int => UInt256.ofNat z.toNat) h

-- GENERALIZES wordOfInt_signed_add to arbitrary integers.
theorem wordOfIntAdd (x y : Int) :
    EVM.wordOfInt (x+y) = EVM.wordOfInt x + EVM.wordOfInt y := by
  change EVM.wordOfInt (x+y) = UInt256.add (EVM.wordOfInt x) (EVM.wordOfInt y)
  rw [← wordOfInt_add_words]
  apply wordOfInt_mod_congr
  rw [wordOfIntResidue, wordOfIntResidue, Int.add_emod]

-- GENERALIZES wordOfInt_signed_sub to arbitrary integers.
theorem wordOfIntSub (x y : Int) :
    EVM.wordOfInt (x-y) = UInt256.sub (EVM.wordOfInt x) (EVM.wordOfInt y) := by
  rw [← wordOfInt_sub_natCasts]
  apply wordOfInt_mod_congr
  rw [wordOfIntResidue, wordOfIntResidue, Int.sub_emod]

end Benchmarks.UniswapV4PoolManager

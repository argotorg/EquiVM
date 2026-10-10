import Benchmarks.UniswapV4PoolManager.WordSignextend24
import Benchmarks.UniswapV4PoolManager.WordIntegerArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: encoding an integer as a signed EVM word preserves every narrower signed cast.
theorem normalizeSignedEncoded (bits : BitWidth) (n : Int) :
    normalizeInt (.sint bits) (EVM.signed (EVM.wordOfInt n)) = normalizeInt (.sint bits) n := by
  have hd : (2 : Int)^bits.val ∣ (2 : Int)^256 := pow_dvd_pow (2 : Int) bits.property.2.1
  have hw := normalizeUnsignedSigned (EVM.wordOfInt n)
  rw [wordOfIntResidue] at hw
  change EVM.signed (EVM.wordOfInt n) % (2^256 : Int) = n % (2^256 : Int) at hw
  have hr : EVM.signed (EVM.wordOfInt n) % (2 : Int)^bits.val = n % (2 : Int)^bits.val := by
    calc
      _ = (EVM.signed (EVM.wordOfInt n) % (2^256 : Int)) % (2 : Int)^bits.val :=
        (Int.emod_emod_of_dvd _ hd).symm
      _ = (n % (2^256 : Int)) % (2 : Int)^bits.val := by rw [hw]
      _ = _ := Int.emod_emod_of_dvd _ hd
  simp only [normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int, hr]

theorem normalizeSigned24Integer (n : Int) :
    normalizeInt (.sint ⟨24, by decide⟩) n =
      EVM.signed (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt n)) := by
  rw [← normalizeSignedEncoded ⟨24, by decide⟩ n, normalizeSigned24Word]

end Benchmarks.UniswapV4PoolManager

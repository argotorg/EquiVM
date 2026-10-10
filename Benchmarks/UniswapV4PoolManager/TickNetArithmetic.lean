import Benchmarks.UniswapV4PoolManager.TickLiquidityWords
import Benchmarks.UniswapV4PoolManager.Signed128Range

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickNetWord_signextend (packed : UInt256) :
    UInt256.signextend (UInt256.ofNat 15) (tickNetWord packed) = tickNetWord packed := by
  have hb := tickNetWord_fits packed
  simpa only [wordOfInt_signed] using signextend128_wordOfInt hb.1 hb.2

theorem tickNetAfter_int256 (packed : UInt256) {delta : Int} (upper : Bool)
    (hd : signedFits ⟨128, by decide⟩ delta) : int256Fits (tickNetAfter packed delta upper) := by
  have hb := tickNetWord_fits packed
  have h0 := hb.1; have h1 := hb.2; have d0 := hd.1; have d1 := hd.2
  change -(2^127 : Int) ≤ EVM.signed (tickNetWord packed) at h0
  change EVM.signed (tickNetWord packed) < (2^127 : Int) at h1
  change -(2^127 : Int) ≤ delta at d0
  change delta < (2^127 : Int) at d1
  cases upper <;> simp only [tickNetAfter, Bool.false_eq_true, if_false, if_true, int256Fits] <;> omega

theorem tickNetAfter_word (packed : UInt256) {delta : Int} (upper : Bool)
    (hd : signedFits ⟨128, by decide⟩ delta) :
    EVM.wordOfInt (tickNetAfter packed delta upper) =
      if upper then UInt256.sub (tickNetWord packed) (EVM.wordOfInt delta)
      else tickNetWord packed+EVM.wordOfInt delta := by
  have hd' := signed_wordOfInt (signedFits128_int256 hd)
  cases upper
  · simpa only [hd'] using wordOfInt_signed_add (tickNetWord packed) (EVM.wordOfInt delta)
  · simpa only [hd'] using wordOfInt_signed_sub (tickNetWord packed) (EVM.wordOfInt delta)

end Benchmarks.UniswapV4PoolManager

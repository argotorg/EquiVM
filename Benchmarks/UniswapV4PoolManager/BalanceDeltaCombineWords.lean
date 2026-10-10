import Benchmarks.UniswapV4PoolManager.BalanceDeltaCombineSource
import Benchmarks.UniswapV4PoolManager.WordIntegerArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem balanceDeltaCombineAmount_int256 (sub one : Bool) (a b : UInt256) :
    int256Fits (balanceDeltaCombineAmount sub one a b) := by
  have ha := balanceDeltaComponent_fits one a
  have hb := balanceDeltaComponent_fits one b
  change -(2^127 : Int) ≤ balanceDeltaComponent one a ∧ balanceDeltaComponent one a < 2^127 at ha
  change -(2^127 : Int) ≤ balanceDeltaComponent one b ∧ balanceDeltaComponent one b < 2^127 at hb
  cases sub <;> change -(2^255 : Int) ≤ _ ∧ _ < 2^255 <;>
    dsimp only [balanceDeltaCombineAmount, balanceDeltaCombineInt, Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> omega

theorem balanceDeltaCombineAmount0_word (sub : Bool) (a b : UInt256) :
    EVM.wordOfInt (balanceDeltaCombineAmount sub false a b) =
      if sub then UInt256.sub (UInt256.sar (UInt256.ofNat 128) a) (UInt256.sar (UInt256.ofNat 128) b)
      else UInt256.sar (UInt256.ofNat 128) a + UInt256.sar (UInt256.ofNat 128) b := by
  cases sub with
  | false => exact wordOfInt_signed_add _ _
  | true => exact wordOfInt_signed_sub _ _

theorem balanceDeltaCombineAmount1_word (sub : Bool) (a b : UInt256) :
    EVM.wordOfInt (balanceDeltaCombineAmount sub true a b) =
      if sub then UInt256.sub (UInt256.signextend (UInt256.ofNat 15) a) (UInt256.signextend (UInt256.ofNat 15) b)
      else UInt256.signextend (UInt256.ofNat 15) a + UInt256.signextend (UInt256.ofNat 15) b := by
  cases sub with
  | false => exact wordOfInt_signed_add _ _
  | true => exact wordOfInt_signed_sub _ _

end Benchmarks.UniswapV4PoolManager

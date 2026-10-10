import Benchmarks.UniswapV4PoolManager.FullMathReduce

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem fullMath128_twos : UInt256.land (UInt256.sub ⟨0⟩ fullMathQ128) fullMathQ128 = fullMathQ128 := by
  decide +kernel
theorem fullMath128_denominator : UInt256.div fullMathQ128 fullMathQ128 = ⟨1⟩ := by decide +kernel
theorem fullMath128_twosInverse :
    UInt256.div (UInt256.sub ⟨0⟩ fullMathQ128) fullMathQ128 + ⟨1⟩ = fullMathQ128 := by decide +kernel

def fullMath128ReduceFrame (f : Frame) (a b : UInt256) : Frame :=
  let f1 := wordLocal f "remainder" ⟨0⟩
  let f2 := wordLocal f1 "remainder" (fullMath128Remainder a b)
  let f3 := wordLocal f2 "prod1" (fullMath128ReducedHigh a b)
  let f4 := wordLocal f3 "prod0" (fullMath128ReducedLow a b)
  let f5 := wordLocal f4 "twos" fullMathQ128
  let f6 := wordLocal f5 "denominator" ⟨1⟩
  let f7 := wordLocal f6 "prod0" (UInt256.div (fullMath128ReducedLow a b) fullMathQ128)
  let f8 := wordLocal f7 "twos" fullMathQ128
  wordLocal f8 "prod0" (fullMath128Wide a b)

theorem fullMath128Reduce {f : Frame} {evm : EVM.State} {a b : UInt256}
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat fullMathQ128.toNat)))
    (hp0 : f.locals.get? "prod0" = some (.int (Int.ofNat (fullMathLow a b).toNat)))
    (hp1 : f.locals.get? "prod1" = some (.int (Int.ofNat (fullMathHigh a b).toNat))) :
    ExecBlock config f evm ((fullMathFunction.body.drop 7).take 9)
      (.ok (fullMath128ReduceFrame f a b) evm) := by
  have h := fullMathReduce (evm := evm) fullMathQ128_ne ha hb hd hp0 hp1
  simpa only [fullMathReduceFrame, fullMathRemainder, fullMathReducedLow,
    fullMathReducedHigh, fullMathTwos, fullMathOdd, fullMathTwosInverse, fullMathWide,
    fullMath128_twos, fullMath128_denominator, fullMath128_twosInverse,
    fullMath128ReduceFrame, fullMath128Remainder, fullMath128ReducedLow,
    fullMath128ReducedHigh, fullMath128Wide] using h

end Benchmarks.UniswapV4PoolManager

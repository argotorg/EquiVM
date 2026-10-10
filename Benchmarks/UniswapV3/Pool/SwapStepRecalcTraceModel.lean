import Benchmarks.UniswapV3.Pool.SwapStepPriceTraceModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

noncomputable def swapStepCalcWords (a : SwapStepArgs)
    (currentRaw targetRaw liquidityRaw feeRaw amountIn amountOut : UInt256) : List UInt256 :=
  [(swapStepMax a).toUInt256, (swapStepExactIn a).toUInt256,
   (swapStepZeroForOne a).toUInt256, ⟨0⟩, amountOut, amountIn,
   swapStepRawPrice a currentRaw targetRaw] ++
    swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw

noncomputable def swapStepRecalcWords (a : SwapStepArgs) (input : Bool)
    (currentRaw targetRaw liquidityRaw feeRaw other : UInt256) : List UInt256 :=
  swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
    (if input then swapStepBeforeAmount a input else other)
    (if input then other else swapStepBeforeAmount a input)

def swapStepRecalcEntry (zero : Bool) : UInt256 := if zero then ⟨12676⟩ else ⟨12753⟩

def swapStepRecalcGuardPC (zero input : Bool) : UInt256 :=
  if input then (if zero then ⟨12685⟩ else ⟨12763⟩)
  else (if zero then ⟨12722⟩ else ⟨12800⟩)

def swapStepRecalcCallPC (zero input : Bool) : UInt256 :=
  if input then (if zero then ⟨12690⟩ else ⟨12768⟩)
  else (if zero then ⟨12727⟩ else ⟨12805⟩)

def swapStepRecalcCallRet (zero input : Bool) : UInt256 :=
  if input then (if zero then ⟨12702⟩ else ⟨12780⟩)
  else (if zero then ⟨12739⟩ else ⟨12817⟩)

def swapStepRecalcJoinPC (zero input : Bool) : UInt256 :=
  if input then (if zero then ⟨12709⟩ else ⟨12787⟩)
  else (if zero then ⟨12746⟩ else ⟨12824⟩)

def swapStepRecalcReusePC (zero input : Bool) : UInt256 :=
  if input then (if zero then ⟨12707⟩ else ⟨12785⟩)
  else (if zero then ⟨12744⟩ else ⟨12822⟩)

theorem swapStepMaxWord (a : SwapStepArgs) :
    UInt256.eq (swapStepPrice a) a.target = (swapStepMax a).toUInt256 := by
  change (decide (swapStepPrice a = a.target)).toUInt256 = (swapStepMax a).toUInt256
  apply congrArg Bool.toUInt256
  apply Bool.eq_iff_iff.mpr
  simp only [swapStepMax, decide_eq_true_eq]
  constructor
  · intro h
    exact (congrArg UInt256.toNat h).symm
  · intro h
    exact u256_inj h.symm

end Benchmarks.UniswapV3.Pool

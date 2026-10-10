import Benchmarks.UniswapV3.Pool.TickLiquidityStorage
import Benchmarks.UniswapV3.Pool.LiquidityDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

structure TickUpdateArgs where
  tick : Int
  current : Int
  delta : Int
  global0 : UInt256
  global1 : UInt256
  secondsPerLiquidity : UInt256
  cumulative : Int
  time : UInt256
  upper : Bool
  maxLiquidity : UInt256

def TickUpdateArgs.Fits (a : TickUpdateArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.current ∧ a.current < 2 ^ 23) ∧
  (-(2 ^ 127 : Int) ≤ a.delta ∧ a.delta < 2 ^ 127) ∧
  a.secondsPerLiquidity.toNat < 2 ^ 160 ∧
  (-(2 ^ 55 : Int) ≤ a.cumulative ∧ a.cumulative < 2 ^ 55) ∧
  a.time.toNat < 2 ^ 32 ∧ a.maxLiquidity.toNat < 2 ^ 128

def tickUpdateGrossBefore (a : TickUpdateArgs) (evm : EVM.State) : Int :=
  Int.ofNat (tickGrossWord evm.accountMap evm.executionEnv a.tick).toNat

def tickUpdateGrossAfter (a : TickUpdateArgs) (evm : EVM.State) : Int :=
  liquidityDeltaResult (tickUpdateGrossBefore a evm) a.delta

def tickUpdateFlipped (a : TickUpdateArgs) (evm : EVM.State) : Bool :=
  decide (tickUpdateGrossAfter a evm = 0) != decide (tickUpdateGrossBefore a evm = 0)

def tickUpdateFunction : FunctionDecl := contract.functions[42]!

theorem tickUpdateLookup : lookupCallable? contract "Tick_update" =
    some tickUpdateFunction.toCallable := rfl

def tickUpdateValues (a : TickUpdateArgs) : List Value :=
  [.int a.tick, .int a.current, .int a.delta, .int (Int.ofNat a.global0.toNat),
   .int (Int.ofNat a.global1.toNat), .int (Int.ofNat a.secondsPerLiquidity.toNat),
   .int a.cumulative, .int (Int.ofNat a.time.toNat), .bool a.upper,
   .int (Int.ofNat a.maxLiquidity.toNat)]

def tickUpdateLocals (a : TickUpdateArgs) : Store :=
  let locals := (∅ : Store).insert "maxLiquidity" (.int (Int.ofNat a.maxLiquidity.toNat))
  let locals := locals.insert "upper" (.bool a.upper)
  let locals := locals.insert "time" (.int (Int.ofNat a.time.toNat))
  let locals := locals.insert "tickCumulative" (.int a.cumulative)
  let locals := locals.insert "secondsPerLiquidityCumulativeX128" (.int (Int.ofNat a.secondsPerLiquidity.toNat))
  let locals := locals.insert "feeGrowthGlobal1X128" (.int (Int.ofNat a.global1.toNat))
  let locals := locals.insert "feeGrowthGlobal0X128" (.int (Int.ofNat a.global0.toNat))
  let locals := locals.insert "liquidityDelta" (.int a.delta)
  let locals := locals.insert "tickCurrent" (.int a.current)
  locals.insert "tick" (.int a.tick)

def tickUpdateFrame (imms : Store) (a : TickUpdateArgs) : Frame :=
  {contract := contract, locals := tickUpdateLocals a, immutables := imms}

def tickUpdateFalseFrame (imms : Store) (a : TickUpdateArgs) : Frame :=
  let locals := (tickUpdateLocals a).insert "flipped" (.bool false)
  {tickUpdateFrame imms a with locals := locals}

def tickUpdateAliasFrame (imms : Store) (a : TickUpdateArgs) : Frame :=
  let locals := (tickUpdateFalseFrame imms a).locals.insert "info" (tickAlias a.tick)
  {tickUpdateFalseFrame imms a with locals := locals}

def tickUpdateBeforeFrame (imms : Store) (a : TickUpdateArgs) (evm : EVM.State) : Frame :=
  let locals := (tickUpdateAliasFrame imms a).locals.insert "liquidityGrossBefore"
    (.int (tickUpdateGrossBefore a evm))
  {tickUpdateAliasFrame imms a with locals := locals}

def tickUpdateAfterFrame (imms : Store) (a : TickUpdateArgs) (evm : EVM.State) : Frame :=
  let locals := (tickUpdateBeforeFrame imms a evm).locals.insert "liquidityGrossAfter"
    (.int (tickUpdateGrossAfter a evm))
  {tickUpdateBeforeFrame imms a evm with locals := locals}

def tickUpdateFlippedFrame (imms : Store) (a : TickUpdateArgs) (evm : EVM.State) : Frame :=
  let locals := (tickUpdateAfterFrame imms a evm).locals.insert "flipped" (.bool (tickUpdateFlipped a evm))
  {tickUpdateAfterFrame imms a evm with locals := locals}

theorem tickUpdateBind (a : TickUpdateArgs) :
    bindParams? tickUpdateFunction.params (tickUpdateValues a) = some (tickUpdateLocals a) := rfl

end Benchmarks.UniswapV3.Pool

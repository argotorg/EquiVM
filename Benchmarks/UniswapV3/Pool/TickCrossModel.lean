import Benchmarks.UniswapV3.Pool.TickHistoryStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

structure TickCrossArgs where
  tick : Int
  global0 : UInt256
  global1 : UInt256
  secondsPerLiquidity : UInt256
  cumulative : Int
  time : UInt256

def TickCrossArgs.Fits (a : TickCrossArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23) ∧
  a.secondsPerLiquidity.toNat < 2 ^ 160 ∧
  (-(2 ^ 55 : Int) ≤ a.cumulative ∧ a.cumulative < 2 ^ 55) ∧
  a.time.toNat < 2 ^ 32

def TickCrossArgs.global (a : TickCrossArgs) (second : Bool) : UInt256 :=
  if second then a.global1 else a.global0

inductive TickCrossField where
  | secondsPerLiquidity
  | cumulative
  | seconds

def TickCrossField.field : TickCrossField → TickHistoryField
  | .secondsPerLiquidity => .secondsPerLiquidity
  | .cumulative => .cumulative
  | .seconds => .seconds

def TickCrossField.type : TickCrossField → ABI.IntType
  | .secondsPerLiquidity => .uint ⟨160, by decide⟩
  | .cumulative => .sint ⟨56, by decide⟩
  | .seconds => .uint ⟨32, by decide⟩

def TickCrossField.globalName : TickCrossField → Ident
  | .secondsPerLiquidity => "secondsPerLiquidityCumulativeX128"
  | .cumulative => "tickCumulative"
  | .seconds => "time"

def TickCrossField.global (a : TickCrossArgs) : TickCrossField → Int
  | .secondsPerLiquidity => Int.ofNat a.secondsPerLiquidity.toNat
  | .cumulative => a.cumulative
  | .seconds => Int.ofNat a.time.toNat

def TickCrossField.old (old : UInt256) : TickCrossField → Int
  | .secondsPerLiquidity => Int.ofNat
      (UInt256.land (UInt256.div old (UInt256.ofNat (2 ^ 56)))
        (UInt256.ofNat (2 ^ 160 - 1))).toNat
  | .cumulative => normalizeInt (.sint ⟨56, by decide⟩) (Int.ofNat old.toNat)
  | .seconds => Int.ofNat (UInt256.land (UInt256.div old (UInt256.ofNat (2 ^ 216)))
      (UInt256.ofNat (2 ^ 32 - 1))).toNat

def tickCrossHistoryValue (a : TickCrossArgs) (field : TickCrossField) (old : UInt256) : Int :=
  normalizeInt field.type (field.global a - field.old old)

def tickCrossHistoryWord (a : TickCrossArgs) (field : TickCrossField) (old : UInt256) : UInt256 :=
  tickHistoryUpdate field.field old (EVM.wordOfInt (tickCrossHistoryValue a field old))

def tickCrossHistoryState (evm : EVM.State) (a : TickCrossArgs) (field : TickCrossField) :
    EVM.State :=
  modifyStorageWord evm (tickFieldSlot a.tick 3) (tickCrossHistoryWord a field)

def tickCrossFeeWord (a : TickCrossArgs) (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) :
    UInt256 :=
  UInt256.sub (a.global second) (tickFeeOutside σ ee a.tick second)

def tickCrossFeeState (evm : EVM.State) (a : TickCrossArgs) (second : Bool) : EVM.State :=
  tickFeeOutsideState evm a.tick second (tickCrossFeeWord a second evm.accountMap evm.executionEnv)

def tickCrossState (evm : EVM.State) (a : TickCrossArgs) : EVM.State :=
  let e0 := tickCrossFeeState evm a false
  let e1 := tickCrossFeeState e0 a true
  let e2 := tickCrossHistoryState e1 a .secondsPerLiquidity
  let e3 := tickCrossHistoryState e2 a .cumulative
  tickCrossHistoryState e3 a .seconds

def tickCrossFunction : FunctionDecl := contract.functions[23]!

theorem tickCrossLookup :
    lookupCallable? contract "Tick_cross" = some tickCrossFunction.toCallable := rfl

def TickCrossArgs.values (a : TickCrossArgs) : List Value :=
  [.int a.tick, .int (Int.ofNat a.global0.toNat), .int (Int.ofNat a.global1.toNat),
   .int (Int.ofNat a.secondsPerLiquidity.toNat), .int a.cumulative, .int (Int.ofNat a.time.toNat)]

def tickCrossLocals (a : TickCrossArgs) : Store :=
  let locals := (∅ : Store).insert "time" (.int (Int.ofNat a.time.toNat))
  let locals := locals.insert "tickCumulative" (.int a.cumulative)
  let locals := locals.insert "secondsPerLiquidityCumulativeX128"
    (.int (Int.ofNat a.secondsPerLiquidity.toNat))
  let locals := locals.insert "feeGrowthGlobal1X128" (.int (Int.ofNat a.global1.toNat))
  let locals := locals.insert "feeGrowthGlobal0X128" (.int (Int.ofNat a.global0.toNat))
  locals.insert "tick" (.int a.tick)

def tickCrossFrame (imms : Store) (a : TickCrossArgs) : Frame :=
  {contract := contract, locals := tickCrossLocals a, immutables := imms}

def tickCrossZeroFrame (imms : Store) (a : TickCrossArgs) : Frame :=
  {tickCrossFrame imms a with locals := (tickCrossLocals a).insert "liquidityNet" (.int 0)}

def tickCrossAliasFrame (imms : Store) (a : TickCrossArgs) : Frame :=
  {tickCrossZeroFrame imms a with
    locals := (tickCrossZeroFrame imms a).locals.insert "info" (tickAlias a.tick)}

def tickCrossResult (evm : EVM.State) (a : TickCrossArgs) : Int :=
  tickNetValue (tickCrossState evm a).accountMap (tickCrossState evm a).executionEnv a.tick

def tickCrossResultFrame (imms : Store) (a : TickCrossArgs) (evm : EVM.State) : Frame :=
  {tickCrossAliasFrame imms a with locals :=
    (tickCrossAliasFrame imms a).locals.insert "liquidityNet" (.int (tickCrossResult evm a))}

theorem tickCrossBind (a : TickCrossArgs) :
    bindParams? tickCrossFunction.params a.values = some (tickCrossLocals a) := rfl

end Benchmarks.UniswapV3.Pool

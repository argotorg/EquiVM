import Benchmarks.UniswapV3.Pool.TickReferences
import Benchmarks.UniswapV3.Pool.SourceWordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickFeeOutsideName (second : Bool) : Ident :=
  if second then "feeGrowthOutside1X128" else "feeGrowthOutside0X128"

def tickFeeOutside (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) (second : Bool) :
    UInt256 :=
  solcSlotWordAt (tickFieldSlot tick (if second then 2 else 1)) σ ee

theorem evalTickAliasFeeGrowth (locals imms : Store) (evm : EVM.State)
    (bindingName : Ident) (tick : Int) (second : Bool)
    (hget : locals.get? bindingName = some (tickAlias tick)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field (tickFeeOutsideName second)]⟩) =
      .ok (.int (Int.ofNat (tickFeeOutside evm.accountMap evm.executionEnv tick second).toNat)) := by
  rw [evalTickAliasField (tickFeeOutsideName second) (.int (.uint ⟨256, by decide⟩))
    (uint256Loc (tickFieldSlot tick (if second then 2 else 1)))
    locals imms evm bindingName tick hget
    (by cases second <;> rfl) (by cases second <;> rfl)]
  rw [storageLocLoad_uint256,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

structure TickFeeArgs where
  lower : Int
  upper : Int
  current : Int
  global0 : UInt256
  global1 : UInt256

def TickFeeArgs.global (a : TickFeeArgs) (second : Bool) : UInt256 :=
  if second then a.global1 else a.global0

def TickFeeArgs.boundary (a : TickFeeArgs) (above : Bool) : Int :=
  if above then a.upper else a.lower

def TickFeeArgs.direct (a : TickFeeArgs) (above : Bool) : Prop :=
  if above then a.current < a.upper else a.lower ≤ a.current

instance (a : TickFeeArgs) (above : Bool) : Decidable (a.direct above) :=
  by unfold TickFeeArgs.direct; infer_instance

def tickFeeSide (a : TickFeeArgs) (σ : AccountMap) (ee : ExecutionEnv)
    (above second : Bool) : UInt256 :=
  let outside := tickFeeOutside σ ee (a.boundary above) second
  if a.direct above then outside else UInt256.sub (a.global second) outside

def tickFeeInside (a : TickFeeArgs) (σ : AccountMap) (ee : ExecutionEnv)
    (second : Bool) : UInt256 :=
  UInt256.sub (UInt256.sub (a.global second) (tickFeeSide a σ ee false second))
    (tickFeeSide a σ ee true second)

def tickFeeGlobalName (second : Bool) : Ident :=
  if second then "feeGrowthGlobal1X128" else "feeGrowthGlobal0X128"

def tickFeeSideName (above second : Bool) : Ident :=
  if above then
    if second then "feeGrowthAbove1X128" else "feeGrowthAbove0X128"
  else
    if second then "feeGrowthBelow1X128" else "feeGrowthBelow0X128"

def tickFeeAliasName (above : Bool) : Ident := if above then "upper" else "lower"

def tickFeeSideExpr (above direct second : Bool) : Expr :=
  let outside := Expr.storage ⟨tickFeeAliasName above, [.field (tickFeeOutsideName second)]⟩
  if direct then outside else
    .cast (.binary .sub (.var (tickFeeGlobalName second)) outside)
      (.elem (.int (.uint ⟨256, by decide⟩)))

def tickFeeSideCondition (above : Bool) : Expr :=
  if above then .binary .lt (.var "tickCurrent") (.var "tickUpper")
  else .binary .ge (.var "tickCurrent") (.var "tickLower")

def tickFeeSideBody (above direct : Bool) : List Stmt :=
  [.assign .localVar ⟨tickFeeSideName above false, []⟩ (tickFeeSideExpr above direct false),
   .assign .localVar ⟨tickFeeSideName above true, []⟩ (tickFeeSideExpr above direct true)]

def tickFeeSideStmt (above : Bool) : Stmt :=
  .ite (tickFeeSideCondition above) (tickFeeSideBody above true) (tickFeeSideBody above false)

def tickFeeFunction : FunctionDecl := contract.functions[44]!

theorem tickFeeLookup :
    lookupCallable? contract "Tick_getFeeGrowthInside" = some tickFeeFunction.toCallable := rfl

end Benchmarks.UniswapV3.Pool

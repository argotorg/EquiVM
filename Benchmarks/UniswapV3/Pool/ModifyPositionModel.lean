import Benchmarks.UniswapV3.Pool.UpdatePositionModel
import Benchmarks.UniswapV3.Pool.Slot0Struct
import Benchmarks.UniswapV3.Pool.NoDelegateCall
import Benchmarks.UniswapV3.Pool.CheckTicksSource
import Benchmarks.UniswapV3.Pool.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure ModifyPositionArgs where
  owner : AccountAddress
  lower : Int
  upper : Int
  delta : Int

def ModifyPositionArgs.Fits (a : ModifyPositionArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.lower ∧ a.lower < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.upper ∧ a.upper < 2 ^ 23) ∧
  (-(2 ^ 127 : Int) ≤ a.delta ∧ a.delta < 2 ^ 127)

def ModifyPositionArgs.value (a : ModifyPositionArgs) : Value :=
  .struct "ModifyPositionParams" [("owner", .address a.owner), ("tickLower", .int a.lower),
    ("tickUpper", .int a.upper), ("liquidityDelta", .int a.delta)]

def ModifyPositionArgs.words (a : ModifyPositionArgs) : List UInt256 :=
  [EVM.word a.owner.val, EVM.wordOfInt a.lower, EVM.wordOfInt a.upper, EVM.wordOfInt a.delta]

def modifyPositionFunction : FunctionDecl := contract.functions[9]!

theorem modifyPositionLookup : lookupCallable? contract "_modifyPosition" =
    some modifyPositionFunction.toCallable := rfl

def modifyPositionLocals (a : ModifyPositionArgs) : Store := (∅ : Store).insert "params" a.value

def modifyPositionFrame (imms : Store) (a : ModifyPositionArgs) : Frame :=
  {contract := contract, locals := modifyPositionLocals a, immutables := imms}

theorem modifyPositionBind (a : ModifyPositionArgs) :
    bindParams? modifyPositionFunction.params [a.value] = some (modifyPositionLocals a) := rfl

def modifyPositionPositionZeroFrame (imms : Store) (a : ModifyPositionArgs) : Frame :=
  let locals := (modifyPositionLocals a).insert "position"
    (.fixedBytes ⟨31, by decide⟩ (List.replicate 32 0))
  {modifyPositionFrame imms a with locals := locals}

def modifyPositionAmount0ZeroFrame (imms : Store) (a : ModifyPositionArgs) : Frame :=
  let frame := modifyPositionPositionZeroFrame imms a
  {frame with locals := frame.locals.insert "amount0" (.int 0)}

def modifyPositionZeroFrame (imms : Store) (a : ModifyPositionArgs) : Frame :=
  let frame := modifyPositionAmount0ZeroFrame imms a
  {frame with locals := frame.locals.insert "amount1" (.int 0)}

def modifyPositionDelegateFrame (imms : Store) (a : ModifyPositionArgs) : Frame :=
  resumeAfterInternalCall (modifyPositionZeroFrame imms a) "__c0" none

def modifyPositionCheckedFrame (imms : Store) (a : ModifyPositionArgs) : Frame :=
  resumeAfterInternalCall (modifyPositionDelegateFrame imms a) "__c1" none

def modifyPositionSlotFrame (imms : Store) (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  let frame := modifyPositionCheckedFrame imms a
  let locals := frame.locals.insert "_slot0" (slot0StructValue evm.accountMap evm.executionEnv)
  {frame with locals := locals}

def modifyPositionUpdateArgs (a : ModifyPositionArgs) (evm : EVM.State) : UpdatePositionArgs :=
  {owner := a.owner, lower := a.lower, upper := a.upper, delta := a.delta,
    current := slot0TickValue evm.accountMap evm.executionEnv}

def modifyPositionCheckExprs : List Expr :=
  [.field (.var "params") "tickLower", .field (.var "params") "tickUpper"]

def modifyPositionUpdateExprs : List Expr :=
  [.field (.var "params") "owner", .field (.var "params") "tickLower",
    .field (.var "params") "tickUpper", .field (.var "params") "liquidityDelta",
    .field (.var "_slot0") "tick"]

macro "modify_position_prefix_get" : tactic =>
  `(tactic| (simp only [modifyPositionSlotFrame, modifyPositionCheckedFrame,
    modifyPositionDelegateFrame, modifyPositionZeroFrame, modifyPositionAmount0ZeroFrame,
    modifyPositionPositionZeroFrame, modifyPositionFrame, modifyPositionLocals,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty]; rfl))

end Benchmarks.UniswapV3.Pool

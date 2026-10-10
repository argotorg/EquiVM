import Benchmarks.UniswapV3.Pool.PositionGetSource
import Benchmarks.UniswapV3.Pool.FeeGrowthStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

structure UpdatePositionArgs where
  owner : AccountAddress
  lower : Int
  upper : Int
  delta : Int
  current : Int

def UpdatePositionArgs.Fits (a : UpdatePositionArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.lower ∧ a.lower < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.upper ∧ a.upper < 2 ^ 23) ∧
  (-(2 ^ 127 : Int) ≤ a.delta ∧ a.delta < 2 ^ 127) ∧
  (-(2 ^ 23 : Int) ≤ a.current ∧ a.current < 2 ^ 23)

def updatePositionFunction : FunctionDecl := contract.functions[30]!

theorem updatePositionLookup : lookupCallable? contract "_updatePosition" =
    some updatePositionFunction.toCallable := rfl

def updatePositionKey (a : UpdatePositionArgs) : UInt256 :=
  positionKey a.owner (EVM.wordOfInt a.lower) (EVM.wordOfInt a.upper)

def updatePositionKeyValue (a : UpdatePositionArgs) : Value :=
  .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (updatePositionKey a))

def updatePositionLocals (a : UpdatePositionArgs) : Store :=
  let locals := (∅ : Store).insert "tick" (.int a.current)
  let locals := locals.insert "liquidityDelta" (.int a.delta)
  let locals := locals.insert "tickUpper" (.int a.upper)
  let locals := locals.insert "tickLower" (.int a.lower)
  locals.insert "owner" (.address a.owner)

def updatePositionFrame (imms : Store) (a : UpdatePositionArgs) : Frame :=
  {contract := contract, locals := updatePositionLocals a, immutables := imms}

theorem updatePositionBind (a : UpdatePositionArgs) : bindParams? updatePositionFunction.params
    [.address a.owner, .int a.lower, .int a.upper, .int a.delta, .int a.current] =
      some (updatePositionLocals a) := rfl

def updatePositionZeroFrame (imms : Store) (a : UpdatePositionArgs) : Frame :=
  let locals := (updatePositionLocals a).insert "position" (.fixedBytes ⟨31, by decide⟩ (List.replicate 32 0))
  {updatePositionFrame imms a with locals := locals}

def updatePositionGetFrame (imms : Store) (a : UpdatePositionArgs) : Frame :=
  let locals := (updatePositionZeroFrame imms a).locals.insert "__c0" (updatePositionKeyValue a)
  {updatePositionZeroFrame imms a with locals := locals}

def updatePositionKeyFrame (imms : Store) (a : UpdatePositionArgs) : Frame :=
  let locals := (updatePositionGetFrame imms a).locals.insert "position" (updatePositionKeyValue a)
  {updatePositionGetFrame imms a with locals := locals}

def updatePositionGlobal0Frame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionKeyFrame imms a).locals.insert "_feeGrowthGlobal0X128"
    (.int (Int.ofNat (feeGrowthWord false evm.accountMap evm.executionEnv).toNat))
  {updatePositionKeyFrame imms a with locals := locals}

def updatePositionGlobal1Frame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionGlobal0Frame imms a evm).locals.insert "_feeGrowthGlobal1X128"
    (.int (Int.ofNat (feeGrowthWord true evm.accountMap evm.executionEnv).toNat))
  {updatePositionGlobal0Frame imms a evm with locals := locals}

def updatePositionLowerFalseFrame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionGlobal1Frame imms a evm).locals.insert "flippedLower" (.bool false)
  {updatePositionGlobal1Frame imms a evm with locals := locals}

def updatePositionReadyFrame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionLowerFalseFrame imms a evm).locals.insert "flippedUpper" (.bool false)
  {updatePositionLowerFalseFrame imms a evm with locals := locals}

macro "update_position_prefix_get" : tactic =>
  `(tactic| (simp only [updatePositionReadyFrame, updatePositionLowerFalseFrame,
    updatePositionGlobal1Frame, updatePositionGlobal0Frame, updatePositionKeyFrame,
    updatePositionGetFrame, updatePositionZeroFrame, updatePositionFrame, updatePositionLocals,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

theorem positionTick_wordOfInt (tick : Int)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) :
    positionTick (EVM.wordOfInt tick) = tick := by
  rw [positionTick, normalizeInt_wordOfInt, normalizeSint_eq_self ⟨24, by decide⟩ _ hlo hhi]

end Benchmarks.UniswapV3.Pool

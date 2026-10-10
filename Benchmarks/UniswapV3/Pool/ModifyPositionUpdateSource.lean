import Benchmarks.UniswapV3.Pool.ModifyPositionPrefix
import Benchmarks.UniswapV3.Pool.UpdatePositionInternal
import Benchmarks.UniswapV3.Pool.UpdatePositionMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def modifyPositionKey (a : ModifyPositionArgs) : UInt256 :=
  positionKey a.owner (EVM.wordOfInt a.lower) (EVM.wordOfInt a.upper)

def modifyPositionKeyValue (a : ModifyPositionArgs) : Value :=
  .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (modifyPositionKey a))

def modifyPositionUpdateFrame (imms : Store) (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  let frame := modifyPositionSlotFrame imms a evm
  {frame with locals := frame.locals.insert "__c2" (modifyPositionKeyValue a)}

def modifyPositionUpdatedFrame (imms : Store) (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  let frame := modifyPositionUpdateFrame imms a evm
  {frame with locals := frame.locals.insert "position" (modifyPositionKeyValue a)}

def modifyPositionUpdatedState (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : EVM.State :=
  updatePositionFinalState v (modifyPositionUpdateArgs a evm) evm

def modifyPositionUpdateBody : List Stmt :=
  [.internalCall "_updatePosition" modifyPositionUpdateExprs "__c2",
    .assign .localVar ⟨"position", []⟩ (.var "__c2")]

macro "modify_position_updated_get" : tactic =>
  `(tactic| (simp only [modifyPositionUpdatedFrame, modifyPositionUpdateFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; modify_position_prefix_get))

theorem modifyPositionAssignKeySource (imms : Store) (a : ModifyPositionArgs) (evm evm' : EVM.State) :
    ExecStmt config (modifyPositionUpdateFrame imms a evm) evm'
      (.assign .localVar ⟨"position", []⟩ (.var "__c2"))
      (.ok (modifyPositionUpdatedFrame imms a evm) evm') := by
  exact ExecStmt.assign (evalExpr_var_get (by modify_position_updated_get))
    (assignLocalVarBase_frame (old := .fixedBytes ⟨31, by decide⟩ (List.replicate 32 0))
      (by modify_position_updated_get))

end Benchmarks.UniswapV3.Pool

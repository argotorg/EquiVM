import Benchmarks.UniswapV3.Pool.ModifyPositionModel
import Benchmarks.UniswapV3.Pool.StructFieldSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionZerosSource (imms : Store) (evm : EVM.State) (a : ModifyPositionArgs) :
    ExecBlock config (modifyPositionFrame imms a) evm (modifyPositionFunction.body.take 3)
      (.ok (modifyPositionZeroFrame imms a) evm) := by
  refine ExecBlock.consNormal (solm' := modifyPositionPositionZeroFrame imms a) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)) ?_
  refine ExecBlock.consNormal (solm' := modifyPositionAmount0ZeroFrame imms a)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem modifyPositionDelegateCall (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (a : ModifyPositionArgs) (hself : evm.executionEnv.codeOwner = v.original) :
    ExecStmt config (modifyPositionZeroFrame (immStore v) a) evm
      (.internalCall "checkNotDelegateCall" [] "__c0")
      (.ok (modifyPositionDelegateFrame (immStore v) a) evm) :=
  internalCallFunctionReturn (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
    (calleeSolm := noDelegateCallFrame v) (value := none)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl (noDelegateCallReturns v evm hself)

theorem modifyPositionDelegateSource (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (a : ModifyPositionArgs) (hself : evm.executionEnv.codeOwner = v.original) :
    ExecBlock config (modifyPositionFrame (immStore v) a) evm (modifyPositionFunction.body.take 4)
      (.ok (modifyPositionDelegateFrame (immStore v) a) evm) := by
  change ExecBlock config _ _ (modifyPositionFunction.body.take 3 ++
    [.internalCall "checkNotDelegateCall" [] "__c0"]) _
  exact execBlock_append_ok (modifyPositionZerosSource (immStore v) evm a)
    (ExecBlock.consNormal (modifyPositionDelegateCall v evm a hself) ExecBlock.nil)

theorem evalModifyPositionCheckExprs (imms : Store) (evm : EVM.State) (a : ModifyPositionArgs) :
    evalExprs? config (modifyPositionDelegateFrame imms a) evm modifyPositionCheckExprs =
      .ok [.int a.lower, .int a.upper] := by
  have hp : evalExpr? config (modifyPositionDelegateFrame imms a) evm (.var "params") =
      .ok a.value := evalExpr_var_get (by modify_position_prefix_get)
  have hl := evalExpr_structField (name := "tickLower") hp rfl
  have hu := evalExpr_structField (name := "tickUpper") hp rfl
  simp only [modifyPositionCheckExprs, evalExprs?, hl, hu, bind, EvalResult.bind, pure]

theorem modifyPositionCheckCall (imms : Store) (evm : EVM.State) (a : ModifyPositionArgs)
    (hticks : validTicks a.lower a.upper) :
    ExecStmt config (modifyPositionDelegateFrame imms a) evm
      (.internalCall "checkTicks" modifyPositionCheckExprs "__c1")
      (.ok (modifyPositionCheckedFrame imms a) evm) :=
  internalCallFunctionReturn (callee := checkTicksFunction)
    (argVals := [.int a.lower, .int a.upper]) (locals := checkTicksLocals a.lower a.upper)
    (calleeSolm := checkTicksFrame imms a.lower a.upper) (value := none)
    (evalModifyPositionCheckExprs imms evm a) checkTicksLookup (checkTicksBind a.lower a.upper)
    (checkTicksReturns imms evm a.lower a.upper hticks)

theorem modifyPositionPrefixSource (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (a : ModifyPositionArgs) (hself : evm.executionEnv.codeOwner = v.original)
    (hticks : validTicks a.lower a.upper) :
    ExecBlock config (modifyPositionFrame (immStore v) a) evm (modifyPositionFunction.body.take 6)
      (.ok (modifyPositionSlotFrame (immStore v) a evm) evm) := by
  change ExecBlock config _ _ (modifyPositionFunction.body.take 4 ++
    [modifyPositionFunction.body[4]!, modifyPositionFunction.body[5]!]) _
  apply execBlock_append_ok (modifyPositionDelegateSource v evm a hself)
  exact ExecBlock.consNormal (modifyPositionCheckCall (immStore v) evm a hticks)
    (ExecBlock.consNormal (ExecStmt.letDecl
      (evalSlot0Struct _ (immStore v) evm (by modify_position_prefix_get))) ExecBlock.nil)

theorem modifyPositionDelegateReverts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (a : ModifyPositionArgs) (hself : evm.executionEnv.codeOwner ≠ v.original) :
    ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 modifyPositionFunction.body]
  apply execBlock_append_ok (modifyPositionZerosSource (immStore v) evm a)
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := noDelegateCallFunction)
    (argVals := []) (locals := ∅) (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl
    (noDelegateCallReverts v evm hself))

theorem modifyPositionTicksReverts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (a : ModifyPositionArgs) (hself : evm.executionEnv.codeOwner = v.original)
    (hticks : ¬validTicks a.lower a.upper) :
    ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 modifyPositionFunction.body]
  apply execBlock_append_ok (modifyPositionDelegateSource v evm a hself)
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := checkTicksFunction)
    (argVals := [.int a.lower, .int a.upper]) (locals := checkTicksLocals a.lower a.upper)
    (evalModifyPositionCheckExprs (immStore v) evm a) checkTicksLookup
    (checkTicksBind a.lower a.upper) (checkTicksReverts (immStore v) evm a.lower a.upper hticks))

theorem evalModifyPositionUpdateExprs (imms : Store) (evm evm' : EVM.State)
    (a : ModifyPositionArgs) :
    evalExprs? config (modifyPositionSlotFrame imms a evm) evm' modifyPositionUpdateExprs =
      .ok [.address a.owner, .int a.lower, .int a.upper, .int a.delta,
        .int (slot0TickValue evm.accountMap evm.executionEnv)] := by
  have hp : evalExpr? config (modifyPositionSlotFrame imms a evm) evm' (.var "params") =
      .ok a.value := evalExpr_var_get (by modify_position_prefix_get)
  have hs : evalExpr? config (modifyPositionSlotFrame imms a evm) evm' (.var "_slot0") =
      .ok (slot0StructValue evm.accountMap evm.executionEnv) :=
    evalExpr_var_get (by modify_position_prefix_get)
  have ho := evalExpr_structField (name := "owner") hp rfl
  have hl := evalExpr_structField (name := "tickLower") hp rfl
  have hu := evalExpr_structField (name := "tickUpper") hp rfl
  have hd := evalExpr_structField (name := "liquidityDelta") hp rfl
  have ht := evalExpr_structField (name := "tick") hs rfl
  simp only [modifyPositionUpdateExprs, evalExprs?, ho, hl, hu, hd, ht, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool

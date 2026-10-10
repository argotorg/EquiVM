import Benchmarks.UniswapV3.Pool.UpdatePositionModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem updatePositionGetSource (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs)
    (hfit : a.Fits) :
    ExecStmt config (updatePositionZeroFrame imms a) evm updatePositionFunction.body[1]!
      (.ok (updatePositionGetFrame imms a) evm) := by
  have hl := positionTick_wordOfInt a.lower hfit.1.1 hfit.1.2
  have hu := positionTick_wordOfInt a.upper hfit.2.1.1 hfit.2.1.2
  have ho : evalExpr? config (updatePositionZeroFrame imms a) evm (.var "owner") =
      .ok (.address a.owner) := evalExpr_var_get (by update_position_prefix_get)
  have el : evalExpr? config (updatePositionZeroFrame imms a) evm (.var "tickLower") =
      .ok (.int a.lower) := evalExpr_var_get (by update_position_prefix_get)
  have eu : evalExpr? config (updatePositionZeroFrame imms a) evm (.var "tickUpper") =
      .ok (.int a.upper) := evalExpr_var_get (by update_position_prefix_get)
  exact internalCallFunctionReturn (callee := positionGetFunction) (retVar := "__c0")
    (argVals := [.address a.owner, .int a.lower, .int a.upper])
    (calleeSolm := positionGetFrame imms a.owner (EVM.wordOfInt a.lower) (EVM.wordOfInt a.upper))
    (locals := positionGetLocals a.owner (EVM.wordOfInt a.lower) (EVM.wordOfInt a.upper))
    (value := some [updatePositionKeyValue a])
    (by simp only [evalExprs?, ho, el, eu, bind, EvalResult.bind, pure]) positionGetLookup
    (by simpa only [hl, hu] using positionGetBind a.owner (EVM.wordOfInt a.lower) (EVM.wordOfInt a.upper))
    (positionGetReturns imms evm a.owner (EVM.wordOfInt a.lower) (EVM.wordOfInt a.upper))

theorem updatePositionKeySource (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs)
    (hfit : a.Fits) :
    ExecBlock config (updatePositionFrame imms a) evm (updatePositionFunction.body.take 3)
      (.ok (updatePositionKeyFrame imms a) evm) := by
  refine ExecBlock.consNormal (solm' := updatePositionZeroFrame imms a) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)) ?_
  refine ExecBlock.consNormal (updatePositionGetSource imms evm a hfit) ?_
  exact ExecBlock.consNormal (ExecStmt.assign
    (evalExpr_var_get (by update_position_prefix_get))
    (assignLocalVarBase_frame (by update_position_prefix_get))) ExecBlock.nil

theorem updatePositionGlobalsSource (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs) :
    ExecBlock config (updatePositionKeyFrame imms a) evm
      [updatePositionFunction.body[3]!, updatePositionFunction.body[4]!,
        updatePositionFunction.body[5]!, updatePositionFunction.body[6]!]
      (.ok (updatePositionReadyFrame imms a evm) evm) := by
  refine ExecBlock.consNormal (solm' := updatePositionGlobal0Frame imms a evm) (evm' := evm)
    (ExecStmt.letDecl (evalFeeGrowthGlobal0X128 _ imms evm (by update_position_prefix_get))) ?_
  refine ExecBlock.consNormal (solm' := updatePositionGlobal1Frame imms a evm) (evm' := evm)
    (ExecStmt.letDecl (evalFeeGrowthGlobal1X128 _ imms evm (by update_position_prefix_get))) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)

theorem updatePositionPrefixSource (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs)
    (hfit : a.Fits) :
    ExecBlock config (updatePositionFrame imms a) evm (updatePositionFunction.body.take 7)
      (.ok (updatePositionReadyFrame imms a evm) evm) := by
  change ExecBlock config _ evm (updatePositionFunction.body.take 3 ++
    [updatePositionFunction.body[3]!, updatePositionFunction.body[4]!,
      updatePositionFunction.body[5]!, updatePositionFunction.body[6]!]) _
  exact execBlock_append_ok (updatePositionKeySource imms evm a hfit)
    (updatePositionGlobalsSource imms evm a)

theorem evalUpdatePositionNonzero (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs) :
    evalExpr? config (updatePositionReadyFrame imms a evm) evm
      (.binary .ne (.var "liquidityDelta") (.intLit 0)) = .ok (.bool (decide (a.delta ≠ 0))) := by
  have hd : evalExpr? config (updatePositionReadyFrame imms a evm) evm (.var "liquidityDelta") =
      .ok (.int a.delta) := evalExpr_var_get (by update_position_prefix_get)
  simp only [evalExpr?, hd, bind, EvalResult.bind, evalBinaryOp?, pure]
  apply congrArg EvalResult.ok
  apply congrArg Value.bool
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq, decide_eq_true_eq, Value.int.injEq]

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3Pool.Spec
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory

namespace Benchmarks.UniswapV3Pool

abbrev liquidityAddDeltaArgValues (x y : Int) : List Value :=
  [.int x, .int y]

abbrev liquidityAddDeltaStore (x y : Int) : Store :=
  ((∅ : Store).insert "y" (.int y)).insert "x" (.int x)

abbrev liquidityAddDeltaFrame (v : PoolImmutables) (x y : Int) : Frame :=
  { contract := contract v, locals := liquidityAddDeltaStore x y }

abbrev liquidityAddDeltaWrappedSub (x y : Int) : Int :=
  (x - (0 - y)) % (2 ^ (128 : Nat))

abbrev liquidityAddDeltaWrappedAdd (x y : Int) : Int :=
  (x + y) % (2 ^ (128 : Nat))

abbrev liquidityAddDeltaAfterZStore (x y z : Int) : Store :=
  (liquidityAddDeltaStore x y).insert "z" (.int z)

abbrev liquidityAddDeltaAfterZFrame (v : PoolImmutables) (x y z : Int) : Frame :=
  { contract := contract v, locals := liquidityAddDeltaAfterZStore x y z }

theorem liquidityAddDelta_bindParams (x y : Int) :
    bindParams? liquidityAddDeltaFunction.params (liquidityAddDeltaArgValues x y) =
      some (liquidityAddDeltaStore x y) := by
  rfl

theorem liquidityAddDeltaStore_x (x y : Int) :
    (liquidityAddDeltaStore x y).get? "x" = some (.int x) := by
  rw [liquidityAddDeltaStore]
  exact store_get_self ((∅ : Store).insert "y" (.int y)) "x" (.int x)

theorem liquidityAddDeltaStore_y (x y : Int) :
    (liquidityAddDeltaStore x y).get? "y" = some (.int y) := by
  rw [liquidityAddDeltaStore]
  rw [store_get_ne ((∅ : Store).insert "y" (.int y))
    (k := "x") (a := "y") (.int x) (by native_decide)]
  exact store_get_self (∅ : Store) "y" (.int y)

theorem liquidityAddDeltaAfterZStore_x (x y z : Int) :
    (liquidityAddDeltaAfterZStore x y z).get? "x" = some (.int x) := by
  rw [liquidityAddDeltaAfterZStore]
  rw [store_get_ne (liquidityAddDeltaStore x y)
    (k := "z") (a := "x") (.int z) (by native_decide)]
  exact liquidityAddDeltaStore_x x y

theorem liquidityAddDeltaAfterZStore_z (x y z : Int) :
    (liquidityAddDeltaAfterZStore x y z).get? "z" = some (.int z) := by
  rw [liquidityAddDeltaAfterZStore]
  exact store_get_self (liquidityAddDeltaStore x y) "z" (.int z)

theorem liquidityAddDelta_evalYLtZeroTrue {v : PoolImmutables} {evm x y}
    (hy : y < 0) :
    evalExpr? (config v) (liquidityAddDeltaFrame v x y) evm
      (ltE (.var "y") (.intLit 0)) = .ok (.bool true) := by
  simp only [liquidityAddDeltaFrame, ltE, evalExpr?, EvalResult.bind, bind, pure]
  rw [liquidityAddDeltaStore_y]
  simp [EvalResult.ofOption, evalBinaryOp?, hy]

theorem liquidityAddDelta_evalYLtZeroFalse {v : PoolImmutables} {evm x y}
    (hy : ¬ y < 0) :
    evalExpr? (config v) (liquidityAddDeltaFrame v x y) evm
      (ltE (.var "y") (.intLit 0)) = .ok (.bool false) := by
  simp only [liquidityAddDeltaFrame, ltE, evalExpr?, EvalResult.bind, bind, pure]
  rw [liquidityAddDeltaStore_y]
  simp [EvalResult.ofOption, evalBinaryOp?, hy]

theorem liquidityAddDelta_evalSubZ {v : PoolImmutables} {evm x y} :
    evalExpr? (config v) (liquidityAddDeltaFrame v x y) evm
      (uint128Wrap (subE (.var "x") (subE (.intLit 0) (.var "y")))) =
        .ok (.int (liquidityAddDeltaWrappedSub x y)) := by
  simp only [liquidityAddDeltaFrame, uint128Wrap, modE, subE, uint128Modulus,
    evalExpr?, EvalResult.bind, bind, pure]
  rw [liquidityAddDeltaStore_x, liquidityAddDeltaStore_y]
  norm_num [EvalResult.ofOption, evalBinaryOp?, liquidityAddDeltaWrappedSub]

theorem liquidityAddDelta_evalAddZ {v : PoolImmutables} {evm x y} :
    evalExpr? (config v) (liquidityAddDeltaFrame v x y) evm
      (uint128Wrap (addE (.var "x") (.var "y"))) =
        .ok (.int (liquidityAddDeltaWrappedAdd x y)) := by
  simp only [liquidityAddDeltaFrame, uint128Wrap, modE, addE, uint128Modulus,
    evalExpr?, EvalResult.bind, bind, pure]
  rw [liquidityAddDeltaStore_x, liquidityAddDeltaStore_y]
  norm_num [EvalResult.ofOption, evalBinaryOp?, liquidityAddDeltaWrappedAdd]

theorem liquidityAddDelta_evalZLtXTrue {v : PoolImmutables} {evm x y z}
    (hlt : z < x) :
    evalExpr? (config v) (liquidityAddDeltaAfterZFrame v x y z) evm
      (ltE (.var "z") (.var "x")) = .ok (.bool true) := by
  simp only [liquidityAddDeltaAfterZFrame, ltE, evalExpr?, EvalResult.bind, bind]
  rw [liquidityAddDeltaAfterZStore_z, liquidityAddDeltaAfterZStore_x]
  simp [EvalResult.ofOption, evalBinaryOp?, hlt]

theorem liquidityAddDelta_evalZLtXFalse {v : PoolImmutables} {evm x y z}
    (hlt : ¬ z < x) :
    evalExpr? (config v) (liquidityAddDeltaAfterZFrame v x y z) evm
      (ltE (.var "z") (.var "x")) = .ok (.bool false) := by
  simp only [liquidityAddDeltaAfterZFrame, ltE, evalExpr?, EvalResult.bind, bind]
  rw [liquidityAddDeltaAfterZStore_z, liquidityAddDeltaAfterZStore_x]
  simp [EvalResult.ofOption, evalBinaryOp?, hlt]

theorem liquidityAddDelta_evalZGeXTrue {v : PoolImmutables} {evm x y z}
    (hge : z >= x) :
    evalExpr? (config v) (liquidityAddDeltaAfterZFrame v x y z) evm
      (geE (.var "z") (.var "x")) = .ok (.bool true) := by
  simp only [liquidityAddDeltaAfterZFrame, geE, evalExpr?, EvalResult.bind, bind]
  rw [liquidityAddDeltaAfterZStore_z, liquidityAddDeltaAfterZStore_x]
  simp [EvalResult.ofOption, evalBinaryOp?, hge]

theorem liquidityAddDelta_evalZGeXFalse {v : PoolImmutables} {evm x y z}
    (hge : ¬ z >= x) :
    evalExpr? (config v) (liquidityAddDeltaAfterZFrame v x y z) evm
      (geE (.var "z") (.var "x")) = .ok (.bool false) := by
  simp only [liquidityAddDeltaAfterZFrame, geE, evalExpr?, EvalResult.bind, bind]
  rw [liquidityAddDeltaAfterZStore_z, liquidityAddDeltaAfterZStore_x]
  simp [EvalResult.ofOption, evalBinaryOp?, hge]

theorem liquidityAddDelta_evalReturnZ {v : PoolImmutables} {evm x y z} :
    evalExprs? (config v) (liquidityAddDeltaAfterZFrame v x y z) evm [.var "z"] =
      .ok [.int z] := by
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [liquidityAddDeltaAfterZStore_z]
  rfl

theorem uniswapV3PoolLiquidityAddDeltaSourceNegativeReturns
    {v : PoolImmutables} {evm x y}
    (hy : y < 0) (hreq : liquidityAddDeltaWrappedSub x y < x) :
    ExecFuncBody (config v) (liquidityAddDeltaFrame v x y) evm
      liquidityAddDeltaFunction.body
      (.returned (liquidityAddDeltaAfterZFrame v x y (liquidityAddDeltaWrappedSub x y))
        evm (some [.int (liquidityAddDeltaWrappedSub x y)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [liquidityAddDeltaFunction] using
    (ExecBlock.consReturn
      (ExecStmt.iteTrue (liquidityAddDelta_evalYLtZeroTrue (v := v) (evm := evm) hy)
        (ExecBlock.consNormal
          (ExecStmt.letDecl (liquidityAddDelta_evalSubZ (v := v) (evm := evm)))
          (ExecBlock.consNormal
            (ExecStmt.requireTrue (liquidityAddDelta_evalZLtXTrue
              (v := v) (evm := evm) (y := y) hreq))
            (ExecBlock.consReturn
              (ExecStmt.return (liquidityAddDelta_evalReturnZ
                (v := v) (evm := evm) (x := x) (y := y))))))))

theorem uniswapV3PoolLiquidityAddDeltaSourceNegativeReverts
    {v : PoolImmutables} {evm x y}
    (hy : y < 0) (hreq : ¬ liquidityAddDeltaWrappedSub x y < x) :
    ExecFuncBody (config v) (liquidityAddDeltaFrame v x y) evm
      liquidityAddDeltaFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [liquidityAddDeltaFunction] using
    (ExecBlock.consRevert
      (ExecStmt.iteTrue (liquidityAddDelta_evalYLtZeroTrue (v := v) (evm := evm) hy)
        (ExecBlock.consNormal
          (ExecStmt.letDecl (liquidityAddDelta_evalSubZ (v := v) (evm := evm)))
          (ExecBlock.consRevert
            (ExecStmt.requireFalse (liquidityAddDelta_evalZLtXFalse
              (v := v) (evm := evm) (y := y) hreq))))))

theorem uniswapV3PoolLiquidityAddDeltaSourceNonnegativeReturns
    {v : PoolImmutables} {evm x y}
    (hy : ¬ y < 0) (hreq : liquidityAddDeltaWrappedAdd x y >= x) :
    ExecFuncBody (config v) (liquidityAddDeltaFrame v x y) evm
      liquidityAddDeltaFunction.body
      (.returned (liquidityAddDeltaAfterZFrame v x y (liquidityAddDeltaWrappedAdd x y))
        evm (some [.int (liquidityAddDeltaWrappedAdd x y)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [liquidityAddDeltaFunction] using
    (ExecBlock.consReturn
      (ExecStmt.iteFalse (liquidityAddDelta_evalYLtZeroFalse (v := v) (evm := evm) hy)
        (ExecBlock.consNormal
          (ExecStmt.letDecl (liquidityAddDelta_evalAddZ (v := v) (evm := evm)))
          (ExecBlock.consNormal
            (ExecStmt.requireTrue (liquidityAddDelta_evalZGeXTrue
              (v := v) (evm := evm) (y := y) hreq))
            (ExecBlock.consReturn
              (ExecStmt.return (liquidityAddDelta_evalReturnZ
                (v := v) (evm := evm) (x := x) (y := y))))))))

theorem uniswapV3PoolLiquidityAddDeltaSourceNonnegativeReverts
    {v : PoolImmutables} {evm x y}
    (hy : ¬ y < 0) (hreq : ¬ liquidityAddDeltaWrappedAdd x y >= x) :
    ExecFuncBody (config v) (liquidityAddDeltaFrame v x y) evm
      liquidityAddDeltaFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [liquidityAddDeltaFunction] using
    (ExecBlock.consRevert
      (ExecStmt.iteFalse (liquidityAddDelta_evalYLtZeroFalse (v := v) (evm := evm) hy)
        (ExecBlock.consNormal
          (ExecStmt.letDecl (liquidityAddDelta_evalAddZ (v := v) (evm := evm)))
          (ExecBlock.consRevert
            (ExecStmt.requireFalse (liquidityAddDelta_evalZGeXFalse
              (v := v) (evm := evm) (y := y) hreq))))))

theorem uniswapV3PoolLookupLiquidityAddDelta (v : PoolImmutables) :
    lookupCallable? (contract v) "liquidityAddDelta" =
      some liquidityAddDeltaFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
    getTickAtSqrtRatioFunction, oracleLteFunction, oracleTransformFunction,
    getSurroundingObservationsFunction, observeSingleFunction, observeBodyFunction,
    liquidityAddDeltaFunction, oracleWriteFunction, tickGetFeeGrowthInsideFunction,
    tickUpdateFunction, tickClearFunction, tickBitmapFlipFunction, positionUpdateFunction,
    getAmount0DeltaUnsignedFunction, getAmount1DeltaUnsignedFunction,
    getAmount0DeltaSignedFunction, getAmount1DeltaSignedFunction, modifyPositionFunction]

end Benchmarks.UniswapV3Pool

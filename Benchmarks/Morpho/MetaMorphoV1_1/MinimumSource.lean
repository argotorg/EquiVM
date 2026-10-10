import Benchmarks.Morpho.MetaMorphoV1_1.Minimum
import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon

/-! Source execution of the unsigned minimum helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def minimumFunction : FunctionDecl := contract.functions[86]!

def minimumFrame (imms : Store) (x y : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "y" (uint256Value y)).insert "x" (uint256Value x)
    immutables := imms }

theorem minimumSource {cfg : Config} {frame : Frame} {evm : State} {lhs rhs : Expr}
    {x y : UInt256} (hx : evalExpr? cfg frame evm lhs = .ok (uint256Value x))
    (hy : evalExpr? cfg frame evm rhs = .ok (uint256Value y)) :
    evalExpr? cfg frame evm (.ite (.binary .lt lhs rhs) lhs rhs) =
      .ok (uint256Value (minimumWord x y)) := by
  have hcmp : evalExpr? cfg frame evm (.binary .lt lhs rhs) =
      .ok (.bool (decide (x.toNat < y.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [hx, hy, bind, EvalResult.bind, uint256Value, evalBinaryOp?,
      Int.ofNat_eq_natCast, Int.ofNat_lt]
  rw [evalExpr?, hcmp]
  by_cases h : x.toNat < y.toNat
  · simp only [h, decide_true, bind, EvalResult.bind, hx, minimumWord, if_pos]
  · simp only [h, decide_false, bind, EvalResult.bind, hy, minimumWord, if_false]

theorem minimumBody (evm : State) (imms : Store) (x y : UInt256) :
    ExecFuncBody config (minimumFrame imms x y) evm minimumFunction.body
      (.returned (minimumFrame imms x y) evm (some [uint256Value (minimumWord x y)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply minimumSource
  · simp only [evalExpr?, minimumFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, minimumFrame, store_get_ne _ _ (by decide : ("x" == "y") = false),
      store_get_self, EvalResult.ofOption]

theorem minimumCall (evm : State) (locals imms : Store) (x y : UInt256)
    (retVar : Ident) (lhs rhs : Expr)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (uint256Value x))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (uint256Value y)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_min" [lhs, rhs] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (uint256Value (minimumWord x y))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := minimumFunction) (value := some [uint256Value (minimumWord x y)])
    (argVals := [uint256Value x, uint256Value y])
    (by simp [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (minimumBody evm imms x y)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

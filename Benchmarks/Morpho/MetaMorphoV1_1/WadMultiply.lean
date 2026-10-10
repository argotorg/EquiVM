import Benchmarks.Morpho.MetaMorphoV1_1.MulDiv

/-! Checked fixed-point multiplication used by interest and fee calculations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def wadMulFunction : FunctionDecl := contract.functions[78]!

def wadMulFrame (imms : Store) (x y : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "y" (uint256Value y)).insert "x" (uint256Value x)
    immutables := imms }

def wadMulWord (x y : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul x y) (UInt256.ofNat (10 ^ 18))

def wadMulResultFrame (imms : Store) (x y : UInt256) : Frame :=
  { wadMulFrame imms x y with
    locals := (wadMulFrame imms x y).locals.insert "__c0" (uint256Value (wadMulWord x y)) }

theorem wadMulFrame_x (imms : Store) (x y : UInt256) (evm : State) :
    evalExpr? config (wadMulFrame imms x y) evm (.var "x") = .ok (uint256Value x) := by
  simp only [evalExpr?, wadMulFrame, store_get_self, EvalResult.ofOption]

theorem wadMulFrame_y (imms : Store) (x y : UInt256) (evm : State) :
    evalExpr? config (wadMulFrame imms x y) evm (.var "y") = .ok (uint256Value y) := by
  simp only [evalExpr?, wadMulFrame, store_get_ne _ _ (by decide : ("x" == "y") = false),
    store_get_self, EvalResult.ofOption]

theorem wadMulBody (imms : Store) (x y : UInt256) (evm : State)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config (wadMulFrame imms x y) evm wadMulFunction.body
      (.returned (wadMulResultFrame imms x y) evm (some [uint256Value (wadMulWord x y)])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (mulDivDownCall evm _ imms x y (UInt256.ofNat (10 ^ 18))
    "__c0" _ _ _ hfit (by decide) (wadMulFrame_x imms x y evm) (wadMulFrame_y imms x y evm)
    (by simp only [evalExpr?, pure]; rfl)) ?_
  exact ABlock.start.returns (by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption, wadMulWord])

theorem wadMulBodyReverts (imms : Store) (x y : UInt256) (evm : State)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config (wadMulFrame imms x y) evm wadMulFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (mulDivDownCallReverts evm _ imms x y
    (UInt256.ofNat (10 ^ 18)) "__c0" _ _ _ (fun h ↦ Nat.not_lt_of_ge hover h.1)
    (wadMulFrame_x imms x y evm) (wadMulFrame_y imms x y evm)
    (by simp only [evalExpr?, pure]; rfl))

set_option maxRecDepth 2000 in
theorem wadMulCall (evm : State) (locals imms : Store) (x y : UInt256)
    (retVar : Ident) (lhs rhs : Expr) (hfit : x.toNat * y.toNat < UInt256.size)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (uint256Value x))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (uint256Value y)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wMulDown" [lhs, rhs] retVar)
      (.ok { contract := contract
             locals := locals.insert retVar (uint256Value (wadMulWord x y))
             immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := wadMulFunction)
    (caller := { contract := contract, locals := locals, immutables := imms })
    (value := some [uint256Value (wadMulWord x y)])
    (argVals := [uint256Value x, uint256Value y])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (wadMulBody imms x y evm hfit)

set_option maxRecDepth 2000 in
theorem wadMulCallReverts (evm : State) (locals imms : Store) (x y : UInt256)
    (retVar : Ident) (lhs rhs : Expr) (hover : UInt256.size ≤ x.toNat * y.toNat)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (uint256Value x))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (uint256Value y)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wMulDown" [lhs, rhs] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := wadMulFunction)
    (argVals := [uint256Value x, uint256Value y])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (wadMulBodyReverts imms x y evm hover)

end Benchmarks.Morpho.MetaMorphoV1_1

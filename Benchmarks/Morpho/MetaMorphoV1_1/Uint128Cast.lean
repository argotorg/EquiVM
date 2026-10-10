import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic

/-! The checked uint128 conversion used before adding interest and fee shares. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def toUint128Function : FunctionDecl := contract.functions[80]!

def toUint128Frame (imms : Store) (x : UInt256) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "x" (uint256Value x), immutables := imms }

-- LIBRARY CANDIDATE: an unsigned cast leaves a value unchanged when it already fits.
theorem uintCastSource {cfg : Config} {frame : Frame} {evm : State} {expr : Expr}
    {x : UInt256} (width : ABI.BitWidth)
    (hx : evalExpr? cfg frame evm expr = .ok (uint256Value x))
    (hfit : x.toNat < 2 ^ width.val) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint width)))) =
      .ok (uint256Value x) := by
  have hn := normalizeInt_uint_eq_self width (Int.ofNat x.toNat) (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr hfit)
  simp only [evalExpr?, hx, bind, EvalResult.bind, uint256Value, castValue?,
    EvalResult.ofOption, hn]

theorem toUint128Frame_x (imms : Store) (x : UInt256) (evm : State) :
    evalExpr? config (toUint128Frame imms x) evm (.var "x") = .ok (uint256Value x) := by
  simp only [evalExpr?, toUint128Frame, store_get_self, EvalResult.ofOption]

theorem toUint128Guard (imms : Store) (x : UInt256) (evm : State) :
    evalExpr? config (toUint128Frame imms x) evm
      (.binary .le (.var "x") (.intLit (2 ^ 128 - 1))) =
      .ok (.bool (decide (x.toNat ≤ 2 ^ 128 - 1))) := by
  apply naturalLeSource (toUint128Frame_x imms x evm)
  simp only [evalExpr?, pure]
  rfl

theorem toUint128Body (imms : Store) (x : UInt256) (evm : State)
    (hfit : x.toNat < 2 ^ 128) :
    ExecFuncBody config (toUint128Frame imms x) evm toUint128Function.body
      (.returned (toUint128Frame imms x) evm (some [uint256Value x])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.returns (ABlock.requireStep ABlock.start ?_)
  · exact uintCastSource _ (toUint128Frame_x imms x evm) hfit
  · have hle : x.toNat ≤ 2 ^ 128 - 1 := by omega
    simpa only [hle, decide_true] using toUint128Guard imms x evm

theorem toUint128BodyReverts (imms : Store) (x : UInt256) (evm : State)
    (hover : 2 ^ 128 ≤ x.toNat) :
    ExecFuncBody config (toUint128Frame imms x) evm toUint128Function.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ABlock.start.requireRevert
  have hle : ¬ x.toNat ≤ 2 ^ 128 - 1 := by omega
  simpa only [hle, decide_false] using toUint128Guard imms x evm

set_option maxRecDepth 2000 in
theorem toUint128Call (evm : State) (locals imms : Store) (x : UInt256)
    (retVar : Ident) (expr : Expr) (hfit : x.toNat < 2 ^ 128)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (uint256Value x)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_toUint128" [expr] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (uint256Value x),
             immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := toUint128Function)
    (caller := { contract := contract, locals := locals, immutables := imms })
    (value := some [uint256Value x]) (argVals := [uint256Value x])
    (evalExprs?_singleton hx) rfl rfl (toUint128Body imms x evm hfit)

set_option maxRecDepth 2000 in
theorem toUint128CallReverts (evm : State) (locals imms : Store) (x : UInt256)
    (retVar : Ident) (expr : Expr) (hover : 2 ^ 128 ≤ x.toNat)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (uint256Value x)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_toUint128" [expr] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := toUint128Function) (argVals := [uint256Value x])
    (evalExprs?_singleton hx) rfl rfl (toUint128BodyReverts imms x evm hover)

end Benchmarks.Morpho.MetaMorphoV1_1

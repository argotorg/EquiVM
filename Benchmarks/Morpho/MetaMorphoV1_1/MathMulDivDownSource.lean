import Benchmarks.Morpho.MetaMorphoV1_1.FullMulDivSource

/-! Source execution of the rounding-toward-zero mulDiv wrapper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def unsignedRoundsUpFunction : FunctionDecl := contract.functions[84]!

def unsignedRoundsDownFrame (imms : Store) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "rounding" (uint256Value ⟨0⟩)
    immutables := imms }

theorem unsignedRoundsDownBody (imms : Store) (evm : State) :
    ExecFuncBody config (unsignedRoundsDownFrame imms) evm unsignedRoundsUpFunction.body
      (.returned (unsignedRoundsDownFrame imms) evm (some [.bool false])) := by
  have hg : evalExpr? config (unsignedRoundsDownFrame imms) evm
      (.binary .lt (.var "rounding") (.intLit 4)) = .ok (.bool true) := by
    simp only [evalExpr?, unsignedRoundsDownFrame, store_get_self, EvalResult.ofOption,
      uint256Value, bind, EvalResult.bind, pure, evalBinaryOp?]
    rfl
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.requireTrue hg)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, unsignedRoundsDownFrame, store_get_self,
    EvalResult.ofOption, uint256Value, bind, EvalResult.bind, pure, evalBinaryOp?, castValue?]
  rfl

theorem unsignedRoundsDownCall {locals imms : Store} {evm : State}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value ⟨0⟩]) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_unsignedRoundsUp" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret (.bool false)
          immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := unsignedRoundsUpFunction) hargs rfl rfl
    (unsignedRoundsDownBody imms evm)

def mathMulDivFunction : FunctionDecl := contract.functions[60]!

def mathMulDivDownFrame (imms : Store) (a b d : UInt256) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert "rounding" (uint256Value ⟨0⟩)).insert "denominator"
      (uint256Value d)).insert "y" (uint256Value b)).insert "x" (uint256Value a)
    immutables := imms }

def mathMulDivDownResultFrame (imms : Store) (a b d : UInt256) : Frame :=
  { mathMulDivDownFrame imms a b d with
    locals := (mathMulDivDownFrame imms a b d).locals.insert "result"
      (uint256Value (fullMulDivWord a b d)) }

def mathMulDivDownFinalFrame (imms : Store) (a b d : UInt256) : Frame :=
  { mathMulDivDownResultFrame imms a b d with
    locals := (mathMulDivDownResultFrame imms a b d).locals.insert "__c1" (.bool false) }

theorem mathMulDivDownArgs (imms : Store) (a b d : UInt256) (evm : State) :
    evalExprs? config (mathMulDivDownFrame imms a b d) evm
      [.var "x", .var "y", .var "denominator"] =
      .ok [uint256Value a, uint256Value b, uint256Value d] := by
  simp only [evalExprs?, evalExpr?, mathMulDivDownFrame, store_get_self,
    store_get_ne _ _ (by decide : ("x" == "y") = false),
    store_get_ne _ _ (by decide : ("x" == "denominator") = false),
    store_get_ne _ _ (by decide : ("y" == "denominator") = false),
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem mathMulDivDownBody (imms : Store) (a b d : UInt256) (evm : State)
    (hfit : fullMulDivFits a b d) :
    ExecFuncBody config (mathMulDivDownFrame imms a b d) evm mathMulDivFunction.body
      (.returned (mathMulDivDownFinalFrame imms a b d) evm
        (some [uint256Value (fullMulDivWord a b d)])) := by
  have hr : evalExprs? config (mathMulDivDownResultFrame imms a b d) evm
      [.var "rounding"] = .ok [uint256Value ⟨0⟩] := by
    simp only [evalExprs?, evalExpr?, mathMulDivDownResultFrame, mathMulDivDownFrame,
      store_get_ne _ _ (by decide : ("result" == "rounding") = false),
      store_get_ne _ _ (by decide : ("x" == "rounding") = false),
      store_get_ne _ _ (by decide : ("y" == "rounding") = false),
      store_get_ne _ _ (by decide : ("denominator" == "rounding") = false),
      store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]
  have hc := unsignedRoundsDownCall hr (ret := "__c1")
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (fullMulDivCall (mathMulDivDownArgs imms a b d evm) hfit)
  apply ExecBlock.consNormal hc
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?,
      store_get_ne _ _ (by decide : ("__c1" == "result") = false), store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem mathMulDivDownBodyReverts (imms : Store) (a b d : UInt256) (evm : State)
    (hbad : ¬ fullMulDivFits a b d) :
    ExecFuncBody config (mathMulDivDownFrame imms a b d) evm mathMulDivFunction.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert
    (ExecBlock.consRevert (fullMulDivCallReverts (mathMulDivDownArgs imms a b d evm) hbad))

theorem mathMulDivDownCall {locals imms : Store} {evm : State} {a b d : UInt256}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value a, uint256Value b, uint256Value d, uint256Value ⟨0⟩])
    (hfit : fullMulDivFits a b d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_mulDiv" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret (uint256Value (fullMulDivWord a b d))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := mathMulDivFunction) hargs rfl rfl
    (mathMulDivDownBody imms a b d evm hfit)

theorem mathMulDivDownCallReverts {locals imms : Store} {evm : State} {a b d : UInt256}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value a, uint256Value b, uint256Value d, uint256Value ⟨0⟩])
    (hbad : ¬ fullMulDivFits a b d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_mulDiv" args ret) .reverted := by
  exact internalCallFunctionRevert (callee := mathMulDivFunction) hargs rfl rfl
    (mathMulDivDownBodyReverts imms a b d evm hbad)

end Benchmarks.Morpho.MetaMorphoV1_1

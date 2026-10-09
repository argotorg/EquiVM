import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon

/-! Source evaluation of the singleton arrays used by Morpho's storage-reader calls. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: a newly allocated singleton array contains its element's default value.
theorem evalExpr_newSingleton {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ty : StorageType} {value : Value} (hdefault : defaultValue? ty = .ok value) :
    evalExpr? cfg frame evm (.newArray ty (.intLit 1)) = .ok (.array [value]) := by
  simp only [evalExpr?, bind, EvalResult.bind, pure, hdefault]
  rfl

-- LIBRARY CANDIDATE: overwrite the first element of a local singleton array.
theorem assignLocalSingleton {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value}
    (hget : frame.locals.get? name = some (.array [old])) :
    assignStorageRef? cfg frame evm .localVar
      { base := name, steps := [.aindex (.intLit 0)] } value =
      .ok ({ frame with locals := frame.locals.insert name (.array [value]) }, evm) := by
  simp only [assignStorageRef?, hget, updateLocalPath?, evalExpr?, bind, EvalResult.bind,
    pure, lookupIndex?, updateIndex?, intToNat?, EvalResult.ofOption]
  rfl

def morphoArrayFunction : FunctionDecl := contract.functions[49]!

def morphoArrayFrame (imms : Store) (value : Value) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "x" value, immutables := imms }

def morphoArrayResultFrame (imms : Store) (value : Value) : Frame :=
  { morphoArrayFrame imms value with
    locals := ((morphoArrayFrame imms value).locals.insert "res"
      (.array [.fixedBytes abiBytes32Width (List.replicate 32 0)])).insert "res" (.array [value]) }

theorem morphoArrayBody (evm : EVM.State) (imms : Store) (value : Value) :
    ExecFuncBody config (morphoArrayFrame imms value) evm morphoArrayFunction.body
      (.returned (morphoArrayResultFrame imms value) evm (some [.array [value]])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_newSingleton
    (value := .fixedBytes abiBytes32Width (List.replicate 32 0))
    (by simp only [defaultValue?, pure]; rfl))) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (value := value) ?_
    (assignLocalSingleton (store_get_self _ _ _))) ?_
  · simp only [evalExpr?, morphoArrayFrame,
      store_get_ne _ _ (show ("res" == "x") = false from by decide),
      store_get_self, EvalResult.ofOption]
  · exact ABlock.start.returns (by simp only [evalExpr?, store_get_self, EvalResult.ofOption])

theorem morphoArrayCall (evm : EVM.State) (locals imms : Store) (value : Value)
    (retVar : Ident) (arg : Expr)
    (heval : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm arg = .ok value) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MorphoLib__array" [arg] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (.array [value])
          immutables := imms }
        evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := morphoArrayFunction) (value := some [.array [value]]) (argVals := [value])
    (evalExprs?_singleton heval) rfl rfl (morphoArrayBody evm imms value)

end Benchmarks.Morpho.MetaMorphoV1_1

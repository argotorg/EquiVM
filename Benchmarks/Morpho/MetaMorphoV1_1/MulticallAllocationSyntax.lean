import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferAllocationSyntax

/-! Explicit result-array, calldata-copy, and return-buffer allocation for multicall. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedDelegateCallFunction : FunctionDecl :=
  { name := "__solcAddressFunctionDelegateCall"
    params := (Syntax.contractSyntax.functions[30]!).params ++
      [{ name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType := [.bytes, .elem (.int (.uint ⟨256, by decide⟩))]
    body := [.delegateCall (.var "target") (.var "data") "success" "returndata"] ++
      addressCallReturnBody }

def multicallLength : Expr := .arrayLength .localVar ⟨"data", []⟩

def multicallDataLength : Expr := .arrayLength .localVar ⟨"__solcDelegateData", []⟩

def allocatedMulticallLoop : Stmt :=
  .for
    [.letDecl "i" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]
    (.binary .lt (.var "i") multicallLength)
    [.assign .localVar ⟨"i", []⟩
      (.inRange (.uint ⟨256, by decide⟩)
        (.binary .add (.var "i") (.intLit 1)))]
    [.letDecl "__solcDelegateData" none (.index (.var "data") (.var "i")),
     .require (.binary .lt multicallDataLength (.intLit (Int.ofNat (2 ^ 64)))),
     .internalCall allocateFunction.name
       [.var cursorName, .binary .add (.intLit 32) multicallDataLength] cursorName,
     .internalCall allocatedDelegateCallFunction.name
       [.env .this, .var "__solcDelegateData", .var cursorName] "__solcDelegateResult",
     .letDecl "__c0" none (.tupleGet (.var "__solcDelegateResult") 0),
     .letDecl cursorName none (.tupleGet (.var "__solcDelegateResult") 1),
     .assign .localVar ⟨"results", [.aindex (.var "i")]⟩ (.var "__c0")]

def allocatedMulticallTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[50]!
  { source with
    body := source.body.take 4 ++
      [.letDecl cursorName none (.intLit 128),
       .require (.binary .lt multicallLength (.intLit (Int.ofNat (2 ^ 64)))),
       .internalCall allocateFunction.name
         [.var cursorName, .binary .add (.intLit 32)
           (.binary .mul (.intLit 32) multicallLength)] cursorName,
       .assign .localVar ⟨"results", []⟩ (.newArray .bytes multicallLength),
       allocatedMulticallLoop, .return [.var "results"]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

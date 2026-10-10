import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSyntax

/-! The transfer helpers with the compiler's request and return buffers made explicit. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def returnBytesLength : Expr := .arrayLength .localVar ⟨"returndata", []⟩

def reserveCallReturn : Stmt :=
  .ite (.binary .ne returnBytesLength (.intLit 0))
    [.require (.binary .lt returnBytesLength (.intLit (Int.ofNat (2 ^ 64)))),
     .internalCall allocateFunction.name
       [.var cursorName, .binary .add (.intLit 32) returnBytesLength] cursorName] []

def addressCallReturnBody : List Stmt :=
  [reserveCallReturn,
   .internalCall "Address_verifyCallResultFromTarget"
     [.var "target", .var "success", .var "returndata"] "__c0",
   .return [.var "__c0", .var cursorName]]

def allocatedAddressCallFunction : FunctionDecl :=
  { name := "__solcAddressFunctionCall"
    params := (Syntax.contractSyntax.functions[77]!).params ++
      [{ name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType := [.bytes, .elem (.int (.uint ⟨256, by decide⟩))]
    body :=
      [.require (.binary .ge (.env .selfbalance) (.intLit 0)),
       .lowLevelCall (.var "target") (.intLit 0) (.var "data") "success" "returndata" true] ++
      addressCallReturnBody }

def allocatedOptionalReturnFunction : FunctionDecl :=
  { name := "__solcCallOptionalReturn"
    params := (Syntax.contractSyntax.functions[54]!).params ++
      [{ name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body :=
      [.internalCall allocatedAddressCallFunction.name
         [.var "token", .var "data", .var cursorName] "__solcAddressResult",
       .letDecl "returndata" none (.tupleGet (.var "__solcAddressResult") 0),
       .letDecl cursorName none (.tupleGet (.var "__solcAddressResult") 1)] ++
      (Syntax.contractSyntax.functions[54]!).body.drop 1 ++ [.return [.var cursorName]] }

def allocatedSafeTransferFunction : FunctionDecl :=
  { name := "__solcSafeTransfer"
    params := (Syntax.contractSyntax.functions[19]!).params ++
      [{ name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body :=
      [.letDecl "data" none (.abiEncodeCall "transfer" [.var "to", .var "value"]),
       .internalCall allocateFunction.name [.var cursorName, .intLit 100] cursorName,
       .internalCall allocatedOptionalReturnFunction.name
         [.var "token", .var "data", .var cursorName] "__c0",
       .return [.var "__c0"]] }

def allocatedSkimTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[57]!
  { source with
    body := source.body.take 6 ++
      [.internalCall allocatedSafeTransferFunction.name
        [.var "token", .var "recipient", .var "amount", .intLit 160] "__c1"] ++
      source.body.drop 7 }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

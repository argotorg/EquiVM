import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationSyntax

/-! Cursor propagation through the source call graph used by `maxDeposit`. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def cursorType : ABIType := .elem (.int (.uint ⟨256, by decide⟩))

def reserveBytes (size : Nat) : Stmt :=
  .internalCall allocateFunction.name [.var cursorName, .intLit (Int.ofNat size)] cursorName

def returnValueExpr : List Expr → Expr
  | [value] => value
  | values => .tupleLit values

def returnValueType : List ABIType → ABIType
  | [ty] => ty
  | types => .tuple types

def cursorCall (name : Ident) (args : List Expr) (result : Ident) : List Stmt :=
  [.internalCall name (args ++ [.var cursorName]) slotsAndCursorName,
   .letDecl result none (.tupleGet (.var slotsAndCursorName) 0),
   .letDecl cursorName none (.tupleGet (.var slotsAndCursorName) 1)]

mutual

def allocationStatement (calls : Ident → Option Ident) (reserves : Ident → Nat) :
    Stmt → List Stmt
  | .internalCall name args result =>
      match calls name with
      | some renamed => cursorCall renamed args result
      | none => [.internalCall name args result]
  | .externalCall target name value args result perm =>
      [.externalCall target name value args result perm] ++
        if reserves name = 0 then [] else [reserveBytes (reserves name)]
  | .return values => [.return [returnValueExpr values, .var cursorName]]
  | .ite cond yes no =>
      [.ite cond (allocationBody calls reserves yes) (allocationBody calls reserves no)]
  | .while cond body => [.while cond (allocationBody calls reserves body)]
  | .for init cond post body =>
      [.for (allocationBody calls reserves init) cond (allocationBody calls reserves post)
        (allocationBody calls reserves body)]
  | .checkedCall target name value args result yes err no perm =>
      [.checkedCall target name value args result
        (allocationBody calls reserves yes) err (allocationBody calls reserves no) perm]
  | stmt => [stmt]
  termination_by stmt => sizeOf stmt

def allocationBody (calls : Ident → Option Ident) (reserves : Ident → Nat) :
    List Stmt → List Stmt
  | [] => []
  | stmt :: body => allocationStatement calls reserves stmt ++ allocationBody calls reserves body
  termination_by body => sizeOf body

end

/-- The successful id-to-parameters path reserves an initial zero struct (160 bytes),
then a bounded return buffer (160 bytes) and the decoded struct (160 bytes). -/
def allocatedMarketParamsFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[56]!
  { source with
    name := "__solcMarketParams"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := reserveBytes 160 :: allocationBody (fun _ ↦ none)
      (fun name ↦ if name == "idToMarketParams" then 320 else 0) source.body }

def allocatedToUint128Function : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[80]!
  { source with
    name := "__solcToUint128"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := reserveBytes 64 :: allocationBody (fun _ ↦ none) (fun _ ↦ 0) source.body }

def marketBalancesAllocationCalls (name : Ident) : Option Ident :=
  if name == "UtilsLib_toUint128" then some allocatedToUint128Function.name else none

/-- The market call reserves a bounded 192-byte return buffer and a 192-byte struct.
The conditional rate call reserves a further 32 bytes. -/
def allocatedMarketBalancesFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[55]!
  { source with
    name := "__solcExpectedMarketBalances"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody marketBalancesAllocationCalls
      (fun name ↦ if name == "market" then 384 else if name == "borrowRateView" then 32 else 0)
      source.body }

def allocatedMaxDepositFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[21]!
  { source with
    name := "__solcMaxDeposit"
    params := [{ name := cursorName, ty := cursorType }]
    returnType := [cursorType, cursorType]
    body := allocationBody (fun name ↦
      if name == "MorphoLib_supplyShares" then some allocatedSupplySharesFunction.name
      else if name == "_marketParams" then some allocatedMarketParamsFunction.name
      else if name == "MorphoBalancesLib_expectedMarketBalances" then
        some allocatedMarketBalancesFunction.name
      else none) (fun _ ↦ 0) source.body }

def allocatedMaxDepositTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[19]! with
    body := (Syntax.contractSyntax.transitions[19]!).body.take 3 ++
      [.internalCall allocatedMaxDepositFunction.name [.intLit 128] "__c0",
       .return [.tupleGet (.var "__c0") 0]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

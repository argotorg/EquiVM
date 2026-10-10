import Benchmarks.Morpho.MetaMorphoV1_1.Uint128Cast
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! The compiler reserves the cast's error string before checking the uint128 bound. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem allocatedToUint128Function_body :
    allocatedToUint128Function.body =
      [reserveBytes 64, .require (.binary .le (.var "x") (.intLit (2 ^ 128 - 1))),
       .return [.cast (.var "x") (.elem (.int (.uint ⟨128, by decide⟩))),
         .var cursorName]] := by
  change reserveBytes 64 :: allocationBody (fun _ ↦ none) (fun _ ↦ 0)
    [.require (.binary .le (.var "x") (.intLit (2 ^ 128 - 1))),
     .return [.cast (.var "x") (.elem (.int (.uint ⟨128, by decide⟩)))]] = _
  simp only [allocationBody, allocationStatement, returnValueExpr,
    List.nil_append, List.cons_append]

set_option maxRecDepth 2000 in
theorem allocatedToUint128Function_lookup :
    lookupCallable? contract allocatedToUint128Function.name =
      some allocatedToUint128Function.toCallable := by
  rfl

def allocatedToUint128Frame (imms : Store) (x ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert cursorName (uint256Value ptr)).insert "x" (uint256Value x)
    immutables := imms }

def allocatedToUint128ResultFrame (imms : Store) (x ptr : UInt256) : Frame :=
  { allocatedToUint128Frame imms x ptr with
    locals := (allocatedToUint128Frame imms x ptr).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨64⟩)) }

theorem allocatedToUint128Frame_cursor (imms : Store) (x ptr : UInt256) (evm : State) :
    evalExpr? config (allocatedToUint128Frame imms x ptr) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, allocatedToUint128Frame,
    store_get_ne _ _ (by decide : ("x" == cursorName) = false), store_get_self,
    EvalResult.ofOption]

theorem allocatedToUint128ResultFrame_x (imms : Store) (x ptr : UInt256) (evm : State) :
    evalExpr? config (allocatedToUint128ResultFrame imms x ptr) evm (.var "x") =
      .ok (uint256Value x) := by
  simp only [evalExpr?, allocatedToUint128ResultFrame, allocatedToUint128Frame,
    store_get_ne _ _ (by decide : (cursorName == "x") = false), store_get_self,
    EvalResult.ofOption]

theorem allocatedToUint128Guard (imms : Store) (x ptr : UInt256) (evm : State) :
    evalExpr? config (allocatedToUint128ResultFrame imms x ptr) evm
      (.binary .le (.var "x") (.intLit (2 ^ 128 - 1))) =
      .ok (.bool (decide (x.toNat ≤ 2 ^ 128 - 1))) := by
  apply naturalLeSource (allocatedToUint128ResultFrame_x imms x ptr evm)
  simp only [evalExpr?, pure]
  rfl

theorem allocatedToUint128Body (imms : Store) (x ptr : UInt256) (evm : State)
    (halloc : allocationFits ptr ⟨64⟩) (hfit : x.toNat < 2 ^ 128) :
    ExecFuncBody config (allocatedToUint128Frame imms x ptr) evm
      allocatedToUint128Function.body
      (.returned (allocatedToUint128ResultFrame imms x ptr) evm
        [uint256Value x, uint256Value (nextCursor ptr ⟨64⟩)]) := by
  apply ExecFuncBody.execBlockRet
  rw [allocatedToUint128Function_body]
  apply ExecBlock.consNormal (allocateCallReturns cursorName allocateFunction_lookup
    (allocatedToUint128Frame_cursor imms x ptr evm)
    (by simp only [evalExpr?, pure]; rfl) halloc)
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
  · apply ExecBlock.consReturn
    apply ExecStmt.return
    change evalExprs? config (allocatedToUint128ResultFrame imms x ptr) evm _ = _
    rw [evalExprs?, uintCastSource ⟨128, by decide⟩
      (allocatedToUint128ResultFrame_x imms x ptr evm) hfit]
    simp only [evalExprs?, bind, EvalResult.bind,
      evalExpr?, allocatedToUint128ResultFrame, store_get_self, EvalResult.ofOption, pure]
  · have hle : x.toNat ≤ 2 ^ 128 - 1 := by omega
    simpa only [hle, decide_true] using allocatedToUint128Guard imms x ptr evm

theorem allocatedToUint128BodyAllocationReverts (imms : Store) (x ptr : UInt256) (evm : State)
    (halloc : ¬ allocationFits ptr ⟨64⟩) :
    ExecFuncBody config (allocatedToUint128Frame imms x ptr) evm
      allocatedToUint128Function.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedToUint128Function_body]
  exact ExecBlock.consRevert (allocateCallReverts cursorName allocateFunction_lookup
    (allocatedToUint128Frame_cursor imms x ptr evm)
    (by simp only [evalExpr?, pure]; rfl) halloc)

theorem allocatedToUint128BodyOverflowReverts (imms : Store) (x ptr : UInt256) (evm : State)
    (halloc : allocationFits ptr ⟨64⟩) (hover : 2 ^ 128 ≤ x.toNat) :
    ExecFuncBody config (allocatedToUint128Frame imms x ptr) evm
      allocatedToUint128Function.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedToUint128Function_body]
  apply ExecBlock.consNormal (allocateCallReturns cursorName allocateFunction_lookup
    (allocatedToUint128Frame_cursor imms x ptr evm)
    (by simp only [evalExpr?, pure]; rfl) halloc)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  have hle : ¬ x.toNat ≤ 2 ^ 128 - 1 := by omega
  simpa only [hle, decide_false] using allocatedToUint128Guard imms x ptr evm

set_option maxRecDepth 2000 in
theorem allocatedToUint128Call (evm : State) (locals imms : Store) (x ptr : UInt256)
    (retVar : Ident) (expr cursorExpr : Expr)
    (halloc : allocationFits ptr ⟨64⟩) (hfit : x.toNat < 2 ^ 128)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (uint256Value x))
    (hp : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm cursorExpr = .ok (uint256Value ptr)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedToUint128Function.name [expr, cursorExpr] retVar)
      (.ok { contract := contract,
             locals := locals.insert retVar
               (.tuple [uint256Value x, uint256Value (nextCursor ptr ⟨64⟩)]),
             immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := allocatedToUint128Function)
    (caller := { contract := contract, locals := locals, immutables := imms })
    (value := some [uint256Value x, uint256Value (nextCursor ptr ⟨64⟩)])
    (argVals := [uint256Value x, uint256Value ptr])
    (by simp only [evalExprs?, hx, hp, bind, EvalResult.bind, pure])
    allocatedToUint128Function_lookup rfl (allocatedToUint128Body imms x ptr evm halloc hfit)

set_option maxRecDepth 2000 in
theorem allocatedToUint128CallReverts (evm : State) (locals imms : Store) (x ptr : UInt256)
    (retVar : Ident) (expr cursorExpr : Expr)
    (hbad : ¬ allocationFits ptr ⟨64⟩ ∨ 2 ^ 128 ≤ x.toNat)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (uint256Value x))
    (hp : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm cursorExpr = .ok (uint256Value ptr)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedToUint128Function.name [expr, cursorExpr] retVar) .reverted := by
  apply internalCallFunctionRevert (callee := allocatedToUint128Function)
    (argVals := [uint256Value x, uint256Value ptr])
    (by simp only [evalExprs?, hx, hp, bind, EvalResult.bind, pure])
    allocatedToUint128Function_lookup rfl
  by_cases halloc : allocationFits ptr ⟨64⟩
  · exact allocatedToUint128BodyOverflowReverts imms x ptr evm halloc
      (hbad.resolve_left (not_not.mpr halloc))
  · exact allocatedToUint128BodyAllocationReverts imms x ptr evm halloc

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

import Benchmarks.Midnight.NamedPositionSource

/-! The internal credit predicate, with its mapping read and caller-local result. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def hasCreditFunction : FunctionDecl := contract.functions[9]!

def hasCreditValue (evm : State) (id user : UInt256) : Bool :=
  decide (0 < (positionFieldWord evm id user 0).toNat)

theorem hasCreditSource {frame : Frame} {evm : State} {id user : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hu : frame.locals.get? "user" = some (.address (AccountAddress.ofNat user.toNat)))
    (hcanon : user.toNat < EVM.addressModulus) :
    ExecFuncBody config frame evm hasCreditFunction.body
      (.returned frame evm (some [.bool (hasCreditValue evm id user)])) := by
  have he : evalExpr? config frame evm (.storage { base := "position", steps :=
      [.mindex (.var "id"), .mindex (.var "user"), .field "credit"] }) =
      .ok (.int (positionFieldWord evm id user 0).toNat) := by
    apply evalNestedBytes32AddressField evm id user hbase hid hu rfl
    · rw [hc]; rfl
    · exact positionField_layout id user 0 hcanon
    · exact positionField_load evm id user 0
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  change evalExprs? config frame evm [.binary .gt (.storage { base := "position", steps :=
    [.mindex (.var "id"), .mindex (.var "user"), .field "credit"] }) (.intLit 0)] = _
  simp only [evalExprs?, evalExpr_binary_nonshort (by decide : BinaryOp.gt ≠ .and)
    (by decide : BinaryOp.gt ≠ .or), he, evalExpr?, bind, EvalResult.bind, evalBinaryOp?,
    gt_iff_lt, Int.natCast_pos, hasCreditValue, pure]

def hasCreditArguments (id user : UInt256) : Store :=
  ((∅ : Store).insert "user" (.address (AccountAddress.ofNat user.toNat))).insert
    "id" (wordBytes32Value id)

theorem callHasCredit {frame : Frame} {evm : State} {id user : UInt256}
    {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? config frame evm args =
      .ok [wordBytes32Value id, .address (AccountAddress.ofNat user.toNat)])
    (hcanon : user.toNat < EVM.addressModulus) :
    ExecStmt config frame evm (.internalCall "hasCredit" args name)
      (.ok (resumeAfterInternalCall frame name (some [.bool (hasCreditValue evm id user)])) evm) := by
  apply internalCallFunctionReturn (callee := hasCreditFunction)
    (locals := hasCreditArguments id user) he
  · rw [hc]; rfl
  · rfl
  · apply hasCreditSource (frame := { frame with locals := hasCreditArguments id user })
      hc _ _ _ hcanon <;>
      simp [hasCreditArguments, Std.HashMap.getElem_insert]

end Benchmarks.Midnight

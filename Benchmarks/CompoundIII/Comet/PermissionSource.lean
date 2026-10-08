import Benchmarks.CompoundIII.Comet.Storage
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def permissionBool (evm : EVM.State) (owner manager : AccountAddress) : Bool :=
  decide (owner = manager) || decide ((UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (isAllowedSlot owner manager))
      ⟨255⟩).toNat ≠ 0)

def permissionLocals (owner manager : AccountAddress) : Store :=
  ((∅ : Store).insert "manager" (.address manager)).insert "owner" (.address owner)

def hasPermissionCallable : CallableDecl :=
  { params := [⟨"owner", .elem .address⟩, ⟨"manager", .elem .address⟩]
    returnType := [.elem .bool]
    body := [.return [.binary .or (.binary .eq (.var "owner") (.var "manager"))
      (.storage ⟨"isAllowed", [.mindex (.var "owner"), .mindex (.var "manager")]⟩)]] }

theorem hasPermissionCallable_lookup :
    lookupCallable? contract "hasPermission_body" = some hasPermissionCallable := rfl

theorem hasPermissionCallable_returns (evm : EVM.State) (imms : Store)
    (owner manager : AccountAddress) :
    ExecFuncBody config
      { contract := contract, locals := permissionLocals owner manager, immutables := imms }
      evm hasPermissionCallable.body
      (.returned { contract := contract, locals := permissionLocals owner manager, immutables := imms }
        evm (some [.bool (permissionBool evm owner manager)])) := by
  let frame : Frame :=
    { contract := contract, locals := permissionLocals owner manager, immutables := imms }
  have ho : frame.locals.get? "owner" = some (.address owner) := by
    simp only [frame, permissionLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hm : frame.locals.get? "manager" = some (.address manager) := by
    simp only [frame, permissionLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hread := evalIsAllowed evm frame.locals imms owner manager "owner" "manager"
    (by simp [frame, permissionLocals]) ho hm
  change evalExpr? config frame _ _ = _ at hread
  rw [wordToElem_bool_value] at hread
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  change evalExpr? config frame evm _ = _
  simp only [evalExpr?, evalBinaryOp?, ho, hm, pure, bind, EvalResult.bind, EvalResult.ofOption]
  have hcmp : (Value.address owner == Value.address manager) = decide (owner = manager) := by
    apply Bool.eq_iff_iff.mpr
    simp
  simp only [evalExpr?, pure, bind, EvalResult.bind] at hread
  rw [hcmp]
  by_cases h : owner = manager
  · simp [h, permissionBool]
  · simp only [decide_eq_false h]
    rw [hread]
    simp [permissionBool, h, pure, bind, EvalResult.bind]

theorem hasPermission_call (frame : Frame) (evm : EVM.State) (owner manager : AccountAddress)
    (ownerExpr managerExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (ho : evalExpr? config frame evm ownerExpr = .ok (.address owner))
    (hm : evalExpr? config frame evm managerExpr = .ok (.address manager)) :
    ExecStmt config frame evm (.internalCall "hasPermission_body" [ownerExpr, managerExpr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.bool (permissionBool evm owner manager)) } evm) := by
  exact ExecStmt.internalCallReturn (callee := hasPermissionCallable)
    (cfg := config) (solm := frame) (evm := evm)
    (args := [ownerExpr, managerExpr]) (argVals := [.address owner, .address manager])
    (by simp only [evalExprs?, ho, hm, pure, bind, EvalResult.bind])
    (by rw [hc]; exact hasPermissionCallable_lookup) rfl
    (by simpa only [hc] using hasPermissionCallable_returns evm frame.immutables owner manager)

end Benchmarks.CompoundIII.Comet

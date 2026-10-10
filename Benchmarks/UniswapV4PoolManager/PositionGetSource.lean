import Benchmarks.UniswapV4PoolManager.PositionStorage
import Benchmarks.UniswapV4PoolManager.PositionKeySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev positionGetFunction : FunctionDecl := contract.functions[65]!
theorem positionGet_lookup : lookupCallable? contract "Position_get" = some positionGetFunction.toCallable := rfl
def positionGetReturnAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.18"

theorem positionGetBody {f : Frame} {evm : EVM.State} {id : UInt256} {owner : AccountAddress}
    {lower upper salt : UInt256} (hf : f.contract = contract)
    (hs : f.locals.get? "self" = some (positionsRefValue id))
    (ha : f.locals.get? "owner" = some (.address owner))
    (hl : f.locals.get? "tickLower" = some (.int (EVM.signed lower)))
    (hu : f.locals.get? "tickUpper" = some (.int (EVM.signed upper)))
    (hsalt : f.locals.get? "salt" = some (wordBytes32Value salt))
    (hlo : int24Canonical lower) (hup : int24Canonical upper) :
    ∃ f', ExecFuncBody config f evm positionGetFunction.body
      (.returned f' evm (some [positionRefValue id (positionKey owner lower upper salt)])) := by
  let key := positionKey owner lower upper salt
  let f1 : Frame := {f with locals := f.locals.insert "positionKey" (wordBytes32Value key)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "position" (positionRefValue id key)}
  let f3 : Frame := {f2 with locals := f2.locals.insert positionGetReturnAlias (positionRefValue id key)}
  have h0 : ExecStmt config f evm positionGetFunction.body[0]! (.ok f1 evm) :=
    positionKeyCall hf (evalLocalValue ha) (evalLocalValue hl) (evalLocalValue hu) (evalLocalValue hsalt)
      hlo hup "positionKey"
  have h1 : ExecStmt config f1 evm positionGetFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letStorage (positionMappingResolve
      ((store_get_ne _ _ (by decide : ("positionKey" == "self") = false)).trans hs)
      (evalLocalValue (store_get_self _ _ _)))
  have h2 : ExecStmt config f2 evm positionGetFunction.body[2]! (.ok f3 evm) :=
    ExecStmt.letStorage (resolveStorageAlias (store_get_self _ _ _))
  exact ⟨f3, .execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ABlock.start.returns (evalLocalValue (store_get_self _ _ _))))))⟩

theorem positionGetCall {f : Frame} {evm : EVM.State} {em ea el eu es : Expr}
    {id lower upper salt : UInt256} {owner : AccountAddress} (hf : f.contract = contract)
    (hm : evalExpr? config f evm em = .ok (positionsRefValue id))
    (ha : evalExpr? config f evm ea = .ok (.address owner))
    (hl : evalExpr? config f evm el = .ok (.int (EVM.signed lower)))
    (hu : evalExpr? config f evm eu = .ok (.int (EVM.signed upper)))
    (hs : evalExpr? config f evm es = .ok (wordBytes32Value salt))
    (hlo : int24Canonical lower) (hup : int24Canonical upper) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Position_get" [em, ea, el, eu, es] ret)
      (.ok {f with locals := f.locals.insert ret (positionRefValue id (positionKey owner lower upper salt))} evm) := by
  obtain ⟨f', hbody⟩ := positionGetBody
    (f := {f with locals := ((((((∅ : Store).insert "salt" (wordBytes32Value salt)).insert
      "tickUpper" (.int (EVM.signed upper))).insert "tickLower" (.int (EVM.signed lower))).insert
      "owner" (.address owner)).insert "self" (positionsRefValue id))}) (evm := evm) hf
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "owner") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("owner" == "tickLower") = false)
      (by decide : ("self" == "tickLower") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("tickLower" == "tickUpper") = false)
      (by decide : ("owner" == "tickUpper") = false)
      (by decide : ("self" == "tickUpper") = false)).trans (store_get_self _ _ _))
    ((store_get_ne4 _ _ _ _ _ (by decide : ("tickUpper" == "salt") = false)
      (by decide : ("tickLower" == "salt") = false) (by decide : ("owner" == "salt") = false)
      (by decide : ("self" == "salt") = false)).trans (store_get_self _ _ _)) hlo hup
  exact internalCallFunctionReturn (argVals := [positionsRefValue id, .address owner,
      .int (EVM.signed lower), .int (EVM.signed upper), wordBytes32Value salt])
    (value := some [positionRefValue id (positionKey owner lower upper salt)])
    (by simp only [evalExprs?, hm, ha, hl, hu, hs, bind, EvalResult.bind, pure])
    (by rw [hf]; exact positionGet_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager

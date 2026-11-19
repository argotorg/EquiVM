import Benchmarks.Midnight.MarketIdSource
import Reasoning.VyperDispatch

/-! Source execution of the SSTORE2 deployment helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def marketStoreCodeFunction : FunctionDecl := contract.functions[22]!

def marketStoreCodeFrame (frame : Frame) (addr : AccountAddress) : Frame :=
  {frame with locals := frame.locals.insert "create2Address" (.address addr)}

def marketStoreCodeResultFrame (frame : Frame) (addr : AccountAddress) : Frame :=
  marketStoreCodeFrame (marketStoreCodeFrame frame 0) addr

def marketStoreZeroSalt : Expr := .fixedBytesLit ⟨31, by decide⟩ (List.replicate 32 0)

def marketStoreCheck : Expr :=
  .binary .ne (.var "create2Address") (.cast (.intLit 0) (.elem .address))

theorem marketStoreCodeFunction_body : marketStoreCodeFunction.body =
    [.letDecl "create2Address" (some (.elem .address)) (.cast (.intLit 0) (.elem .address)),
      .new "SSTORE2" (.intLit 0) [.var "market"] "create2Address" (some marketStoreZeroSalt),
      .require marketStoreCheck, .return [.var "create2Address"]] := rfl

theorem marketStoreZeroAddress {frame : Frame} {evm : EVM.State} :
    evalExpr? config frame evm (.cast (.intLit 0) (.elem .address)) = .ok (.address 0) := by
  simp only [evalExpr?, castValue?, bind, EvalResult.bind, pure, EvalResult.ofOption]
  rfl

theorem marketStoreZeroSalt_eval {frame : Frame} {evm : EVM.State} :
    evalSalt? config frame evm (some marketStoreZeroSalt) =
      .ok (some (Ethereum.UInt256.toByteArray ⟨0⟩)) := by
  simp only [evalSalt?, marketStoreZeroSalt, evalExpr?, bind, EvalResult.bind, pure]
  decide +kernel

theorem marketStoreArgs {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExprs? config (marketStoreCodeFrame frame 0) evm [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp only [evalExprs?, evalExpr?, marketStoreCodeFrame,
    store_get_ne _ _ (show ("create2Address" == "market") = false from rfl), hm,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem marketStoreCheck_eval (frame : Frame) (evm : EVM.State) (addr : AccountAddress) :
    evalExpr? config (marketStoreCodeResultFrame frame addr) evm marketStoreCheck =
      .ok (.bool (decide (addr ≠ 0))) := by
  rw [marketStoreCheck, evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [evalExpr?, marketStoreCodeResultFrame, marketStoreCodeFrame,
    store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]
  simp [evalBinaryOp?, castValue?, Reasoning.VyperDispatch.value_address_beq,
    show AccountAddress.ofNat 0 = 0 from rfl]

theorem marketStoreCodeFailureSource {frame : Frame} {evm evm' : EVM.State} {m : MarketData}
    {addr : AccountAddress}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hperm : evm.executionEnv.perm = true)
    (hnew : newViaEVM config evm "SSTORE2" 0 [Model.marketValue m.value]
      (some (Ethereum.UInt256.toByteArray ⟨0⟩)) (addr, evm', false)) :
    ExecFuncBody config frame evm marketStoreCodeFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [marketStoreCodeFunction_body]
  refine ExecBlock.consNormal (ExecStmt.letDecl marketStoreZeroAddress) ?_
  apply ExecBlock.consRevert
  exact ExecStmt.newRevert hperm (by simp only [evalExpr?, pure]) (marketStoreArgs hm)
    marketStoreZeroSalt_eval hnew

theorem marketStoreCodeZeroSource {frame : Frame} {evm evm' : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hperm : evm.executionEnv.perm = true)
    (hnew : newViaEVM config evm "SSTORE2" 0 [Model.marketValue m.value]
      (some (Ethereum.UInt256.toByteArray ⟨0⟩)) (0, evm', true)) :
    ExecFuncBody config frame evm marketStoreCodeFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [marketStoreCodeFunction_body]
  refine ExecBlock.consNormal (ExecStmt.letDecl marketStoreZeroAddress) ?_
  refine ExecBlock.consNormal (ExecStmt.newSuccess hperm (by simp only [evalExpr?, pure])
    (marketStoreArgs hm)
    marketStoreZeroSalt_eval hnew) ?_
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [ne_eq, not_true_eq_false, decide_false] using marketStoreCheck_eval frame evm' 0

theorem marketStoreCodeSuccessSource {frame : Frame} {evm evm' : EVM.State} {m : MarketData}
    {addr : AccountAddress}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hperm : evm.executionEnv.perm = true) (haddr : addr ≠ 0)
    (hnew : newViaEVM config evm "SSTORE2" 0 [Model.marketValue m.value]
      (some (Ethereum.UInt256.toByteArray ⟨0⟩)) (addr, evm', true)) :
    ExecFuncBody config frame evm marketStoreCodeFunction.body
      (.returned (marketStoreCodeResultFrame frame addr) evm' (some [.address addr])) := by
  apply ExecFuncBody.execBlockRet
  rw [marketStoreCodeFunction_body]
  refine ExecBlock.consNormal (ExecStmt.letDecl marketStoreZeroAddress) ?_
  refine ExecBlock.consNormal (ExecStmt.newSuccess hperm (by simp only [evalExpr?, pure])
    (marketStoreArgs hm)
    marketStoreZeroSalt_eval hnew) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (marketStoreCheck_eval frame evm' addr).trans (by rw [decide_eq_true haddr])
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?,
    store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Midnight

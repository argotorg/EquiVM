import Benchmarks.CompoundIII.Comet.AccountBalanceSource
import Benchmarks.CompoundIII.Comet.Unsigned104

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def balanceWord (v : CometWithExtendedAssetListImmutables) (w0 w1 time basic : UInt256) : UInt256 :=
  if 0 < signed104 basic then
    presentValueWord (currentIndex v w0 w1 time false) (positivePrincipal basic)
  else ⟨0⟩

def balanceThen : List Stmt :=
  [.internalCall "unsigned104" [.var "principal"] "__c2",
    .internalCall "presentValueSupply" [.var "baseSupplyIndex_", .var "__c2"] "__c3",
    .return [.var "__c3"]]

def balanceRead : List Stmt := accountBalanceRead false

def balanceCallable : CallableDecl :=
  { params := [⟨"account", .elem .address⟩]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body := currentIndicesBlock ++ balanceRead ++
      [.ite (.binary .gt (.var "principal") (.intLit 0)) balanceThen [], .return [.intLit 0]] }

theorem balanceCallable_lookup :
    lookupCallable? contract "balanceOf_body" = some balanceCallable := rfl

def balanceEntry (v : CometWithExtendedAssetListImmutables) (addr : AccountAddress) : Frame :=
  accountBalanceEntry v addr

theorem balanceCallable_returns (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (addr : AccountAddress)
    (hv : CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    ∃ final, ExecFuncBody config (balanceEntry v addr) evm balanceCallable.body
      (.returned final evm (some [.int (balanceWord v
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))).toNat])) := by
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let time := timestampWord evm.executionEnv
  let basic := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)
  let idx := currentIndex v w0 w1 time false
  let f0 := balanceEntry v addr
  let f1 := currentIndicesFrame f0 v w0 w1 time
  let f2 : Frame := { f1 with locals := f1.locals.insert "baseSupplyIndex_" (.int idx.toNat) }
  let f3 : Frame := { f2 with locals := f2.locals.insert "principal" (.int (signed104 basic)) }
  have hprefix : ExecBlock config f0 evm (currentIndicesBlock ++ balanceRead) (.ok f3 evm) :=
    accountBalancePrefix v evm addr false hv
  have hprincipal : evalExpr? config f3 evm (.var "principal") =
      .ok (.int (signed104 basic)) :=
    accountBalancePrincipalEval v addr false w0 w1 time basic evm
  have hcond : evalExpr? config f3 evm (.binary .gt (.var "principal") (.intLit 0)) =
      .ok (.bool (decide (0 < signed104 basic))) := by
    simp only [evalExpr?, hprincipal, pure, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hp : 0 < signed104 basic
  · let principal := positivePrincipal basic
    let val := presentValueWord idx principal
    let f4 : Frame := { f3 with locals := f3.locals.insert "__c2" (.int principal.toNat) }
    let f5 : Frame := { f4 with locals := f4.locals.insert "__c3" (.int val.toNat) }
    refine ⟨f5, ExecFuncBody.execBlockRet ?_⟩
    change ExecBlock config f0 evm _ (.returned f5 evm (some [.int (balanceWord v w0 w1 time basic).toNat]))
    rw [balanceWord, if_pos hp]
    apply execBlockAppendOk hprefix
    apply ExecBlock.consReturn (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true hp])) ?_)
    have harg : evalExpr? config f3 evm (.var "principal") = .ok (.int principal.toNat) := by
      rw [hprincipal]
      exact congrArg (fun i ↦ EvalResult.ok (Value.int i)) (positivePrincipal_int (le_of_lt hp)).symm
    apply ExecBlock.consNormal (unsigned104_call f3 evm principal _ "__c2" rfl harg
      (lt_trans (positivePrincipal_lt basic) (by decide)))
    have hei : evalExpr? config f4 evm (.var "baseSupplyIndex_") = .ok (.int idx.toNat) := by
      simp only [evalExpr?, f4, f3, f2, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl
    have hep : evalExpr? config f4 evm (.var "__c2") = .ok (.int principal.toNat) := by
      simp only [evalExpr?, f4, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    apply ExecBlock.consNormal (presentValue_call f4 evm false idx principal _ _ "__c3" rfl
      (currentIndex_lt hv false) (lt_trans (positivePrincipal_lt basic) (by decide)) hei hep)
    exact ABlock.start.returns (by
      simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl)
  · refine ⟨f3, ExecFuncBody.execBlockRet ?_⟩
    change ExecBlock config f0 evm _ (.returned f3 evm (some [.int (balanceWord v w0 w1 time basic).toNat]))
    rw [balanceWord, if_neg hp]
    apply execBlockAppendOk hprefix
    apply ExecBlock.consNormal (ExecStmt.iteFalse (hcond.trans (by rw [decide_eq_false hp])) ExecBlock.nil)
    exact ABlock.start.returns (by simp only [evalExpr?, pure]; rfl)

theorem balanceCallable_reverts (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (addr : AccountAddress)
    (hv : ¬ CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    ExecFuncBody config (balanceEntry v addr) evm balanceCallable.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  have hpref := currentIndicesBlock_result v (balanceEntry v addr) evm rfl rfl
    (by simp [balanceEntry, accountBalanceEntry])
  dsimp only at hpref
  rw [if_neg hv] at hpref
  exact execBlockAppendReverted (execBlockAppendReverted hpref)

theorem balance_call_ok (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (addr : AccountAddress) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.address addr))
    (hv : CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    let val := balanceWord v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))
    ExecStmt config frame evm (.internalCall "balanceOf_body" [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int val.toNat) } evm) := by
  obtain ⟨final, hf⟩ := balanceCallable_returns v evm addr hv
  exact ExecStmt.internalCallReturn (callee := balanceCallable)
    (locals := (∅ : Store).insert "account" (.address addr))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.address addr])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact balanceCallable_lookup) rfl
    (by simpa only [hc, hi] using hf)

theorem balance_call_revert (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (addr : AccountAddress) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.address addr))
    (hv : ¬ CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    ExecStmt config frame evm (.internalCall "balanceOf_body" [expr] ret) .reverted := by
  apply ExecStmt.internalCallRevert (callee := balanceCallable)
    (locals := (∅ : Store).insert "account" (.address addr))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.address addr])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact balanceCallable_lookup) rfl
  simpa only [hc, hi] using balanceCallable_reverts v evm addr hv

end Benchmarks.CompoundIII.Comet

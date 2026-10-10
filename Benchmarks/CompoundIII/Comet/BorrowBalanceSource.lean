import Benchmarks.CompoundIII.Comet.AccountBalanceSource
import Benchmarks.CompoundIII.Comet.Unsigned104
import Benchmarks.CompoundIII.Comet.NegativePrincipal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def BorrowBalanceValid (v : CometWithExtendedAssetListImmutables)
    (w0 w1 time basic : UInt256) : Prop :=
  CurrentIndicesValid v w0 w1 time ∧ -(2^103 : Int) < signed104 basic

instance (v : CometWithExtendedAssetListImmutables) (w0 w1 time basic : UInt256) :
    Decidable (BorrowBalanceValid v w0 w1 time basic) := inferInstanceAs (Decidable (_ ∧ _))

def borrowBalanceWord (v : CometWithExtendedAssetListImmutables)
    (w0 w1 time basic : UInt256) : UInt256 :=
  if signed104 basic < 0 then
    presentValueWord (currentIndex v w0 w1 time true) (negativePrincipal basic)
  else ⟨0⟩

def borrowBalanceThen : List Stmt :=
  [.internalCall "unsigned104"
      [.inRange (.sint ⟨104, by decide⟩) (.binary .sub (.intLit 0) (.var "principal"))] "__c2",
    .internalCall "presentValueBorrow" [.var "baseBorrowIndex_", .var "__c2"] "__c3",
    .return [.var "__c3"]]

def borrowBalanceCallable : CallableDecl :=
  { params := [⟨"account", .elem .address⟩]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body := currentIndicesBlock ++ accountBalanceRead true ++
      [.ite (.binary .lt (.var "principal") (.intLit 0)) borrowBalanceThen [], .return [.intLit 0]] }

theorem borrowBalanceCallable_lookup :
    lookupCallable? contract "borrowBalanceOf_body" = some borrowBalanceCallable := rfl

theorem borrowBalanceCallable_returns (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (addr : AccountAddress)
    (hv : BorrowBalanceValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))) :
    ∃ final, ExecFuncBody config (accountBalanceEntry v addr) evm borrowBalanceCallable.body
      (.returned final evm (some [.int (borrowBalanceWord v
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))).toNat])) := by
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let time := timestampWord evm.executionEnv
  let basic := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)
  let idx := currentIndex v w0 w1 time true
  let f3 := accountBalanceFrame v addr true w0 w1 time basic
  have hprefix := accountBalancePrefix v evm addr true hv.1
  have hprincipal : evalExpr? config f3 evm (.var "principal") =
      .ok (.int (signed104 basic)) :=
    accountBalancePrincipalEval v addr true w0 w1 time basic evm
  have hcond : evalExpr? config f3 evm (.binary .lt (.var "principal") (.intLit 0)) =
      .ok (.bool (decide (signed104 basic < 0))) := by
    simp only [evalExpr?, hprincipal, pure, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hp : signed104 basic < 0
  · let principal := negativePrincipal basic
    let val := presentValueWord idx principal
    let f4 : Frame := { f3 with locals := f3.locals.insert "__c2" (.int principal.toNat) }
    let f5 : Frame := { f4 with locals := f4.locals.insert "__c3" (.int val.toNat) }
    refine ⟨f5, ExecFuncBody.execBlockRet ?_⟩
    change ExecBlock config (accountBalanceEntry v addr) evm _
      (.returned f5 evm (some [.int (borrowBalanceWord v w0 w1 time basic).toNat]))
    rw [borrowBalanceWord, if_pos hp]
    apply execBlockAppendOk hprefix
    apply ExecBlock.consReturn (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true hp])) ?_)
    have harg := checkedPrincipalNegSource hprincipal hp hv.2
    apply ExecBlock.consNormal (unsigned104_call f3 evm principal _ "__c2" rfl harg
      (lt_trans (negativePrincipal_lt hv.2) (by decide)))
    have hei : evalExpr? config f4 evm (.var "baseBorrowIndex_") = .ok (.int idx.toNat) := by
      simp only [evalExpr?, f4, f3, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        accountBalanceFrame, indexLocalName, EvalResult.ofOption]
      rfl
    have hep : evalExpr? config f4 evm (.var "__c2") = .ok (.int principal.toNat) := by
      simp only [evalExpr?, f4, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    apply ExecBlock.consNormal (presentValue_call f4 evm true idx principal _ _ "__c3" rfl
      (currentIndex_lt hv.1 true) (lt_trans (negativePrincipal_lt hv.2) (by decide)) hei hep)
    exact ABlock.start.returns (by
      simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl)
  · refine ⟨f3, ExecFuncBody.execBlockRet ?_⟩
    change ExecBlock config (accountBalanceEntry v addr) evm _
      (.returned f3 evm (some [.int (borrowBalanceWord v w0 w1 time basic).toNat]))
    rw [borrowBalanceWord, if_neg hp]
    apply execBlockAppendOk hprefix
    apply ExecBlock.consNormal (ExecStmt.iteFalse (hcond.trans (by rw [decide_eq_false hp])) ExecBlock.nil)
    exact ABlock.start.returns (by simp only [evalExpr?, pure]; rfl)

theorem borrowBalanceCallable_reverts (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (addr : AccountAddress)
    (hv : ¬ BorrowBalanceValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))) :
    ExecFuncBody config (accountBalanceEntry v addr) evm borrowBalanceCallable.body .reverted := by
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let time := timestampWord evm.executionEnv
  let basic := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)
  apply ExecFuncBody.execBlockRevert
  by_cases hc : CurrentIndicesValid v w0 w1 time
  · have hmin : signed104 basic = -(2^103 : Int) := by
      have hb := signed104_bounds basic
      have hn : ¬ -(2^103 : Int) < signed104 basic := fun hm ↦ hv ⟨hc, hm⟩
      omega
    have hpref := accountBalancePrefix v evm addr true hc
    apply execBlockAppendOk hpref
    have he := accountBalancePrincipalEval v addr true w0 w1 time basic evm
    have hcond : evalExpr? config (accountBalanceFrame v addr true w0 w1 time basic) evm
        (.binary .lt (.var "principal") (.intLit 0)) = .ok (.bool true) := by
      simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, hmin]
      rfl
    apply ExecBlock.consRevert (ExecStmt.iteTrue hcond ?_)
    apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
    simp only [evalExprs?, checkedPrincipalNegSource_revert he hmin, bind, EvalResult.bind]
  · have hpref := currentIndicesBlock_result v (accountBalanceEntry v addr) evm rfl rfl
      (by simp [accountBalanceEntry])
    dsimp only at hpref
    rw [if_neg hc] at hpref
    exact execBlockAppendReverted (execBlockAppendReverted hpref)

theorem borrowBalance_call_ok (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (addr : AccountAddress) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.address addr))
    (hv : BorrowBalanceValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))) :
    let val := borrowBalanceWord v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))
    ExecStmt config frame evm (.internalCall "borrowBalanceOf_body" [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int val.toNat) } evm) := by
  obtain ⟨final, hf⟩ := borrowBalanceCallable_returns v evm addr hv
  exact ExecStmt.internalCallReturn (callee := borrowBalanceCallable)
    (locals := (∅ : Store).insert "account" (.address addr))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.address addr])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact borrowBalanceCallable_lookup) rfl
    (by simpa only [hc, hi] using hf)

theorem borrowBalance_call_revert (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (addr : AccountAddress) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.address addr))
    (hv : ¬ BorrowBalanceValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))) :
    ExecStmt config frame evm (.internalCall "borrowBalanceOf_body" [expr] ret) .reverted := by
  apply ExecStmt.internalCallRevert (callee := borrowBalanceCallable)
    (locals := (∅ : Store).insert "account" (.address addr))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.address addr])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact borrowBalanceCallable_lookup) rfl
  simpa only [hc, hi] using borrowBalanceCallable_reverts v evm addr hv

end Benchmarks.CompoundIII.Comet

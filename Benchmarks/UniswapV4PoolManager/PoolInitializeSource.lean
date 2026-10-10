import Benchmarks.UniswapV4PoolManager.PoolCheckSource
import Benchmarks.UniswapV4PoolManager.Slot0InitializeSource
import Benchmarks.UniswapV4PoolManager.TickPriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev poolInitializeFunction : FunctionDecl := contract.functions[14]!
theorem poolInitialize_lookup : lookupCallable? contract "Pool_initialize" =
    some poolInitializeFunction.toCallable := rfl

def poolInitializeWord (price tick fee : UInt256) : UInt256 :=
  slot0LPFeeWord (slot0SetTickWord (slot0SetSqrtWord ⟨0⟩ price) tick) fee
def poolInitializePost (evm : EVM.State) (id price tick fee : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolSlot id) (poolInitializeWord price tick fee)
def poolInitializeTailResult (f : Frame) (evm : EVM.State) (id price tick fee : UInt256) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation else
    .returned f (poolInitializePost evm id price tick fee) (some [.int (EVM.signed tick)])
def poolInitializeResult (f : Frame) (evm : EVM.State) (id price fee : UInt256) : ExecResult :=
  if poolSqrtPriceWord evm id ≠ ⟨0⟩ then .reverted else
    match tickPriceResult price with
    | none => .reverted
    | some tick => poolInitializeTailResult f evm id price tick fee

theorem poolInitializeTail {f : Frame} {evm : EVM.State} {id price tick fee : UInt256} {old : Value}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (he : f.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)))
    (ht : f.locals.get? "__c1" = some (.int (EVM.signed tick)))
    (ho : f.locals.get? "tick" = some old) (hpc : price.toNat < 2^160) (hec : fee.toNat < 2^24) :
    ∃ f', ExecFuncBody config f evm (poolInitializeFunction.body.drop 4)
      (poolInitializeTailResult f' evm id price tick fee) := by
  let f1 : Frame := {f with locals := f.locals.insert "tick" (.int (EVM.signed tick))}
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c2" (wordBytes32Value ⟨0⟩)}
  let f3 : Frame := {f2 with locals := f2.locals.insert "__c3" (wordBytes32Value (slot0SetSqrtWord ⟨0⟩ price))}
  let f4 : Frame := {f3 with locals := f3.locals.insert "__c4" (wordBytes32Value (slot0SetTickWord (slot0SetSqrtWord ⟨0⟩ price) tick))}
  let f5 : Frame := {f4 with locals := f4.locals.insert "__c5" (wordBytes32Value (poolInitializeWord price tick fee))}
  have hzero : evalExpr? config f1 evm (.cast (.fixedBytesLit abiBytes32Width (List.replicate 32 0))
      (.elem (.bytes abiBytes32Width))) = .ok (wordBytes32Value ⟨0⟩) := by
    simp only [evalExpr?, bind, EvalResult.bind, pure]
    decide +kernel
  have hp2 : f2.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("tick" == "sqrtPriceX96") = false)
      (by decide : ("__c2" == "sqrtPriceX96") = false)).trans hp
  have ht3 : f3.locals.get? "tick" = some (.int (EVM.signed tick)) :=
    (store_get_ne2 _ _ _ (by decide : ("__c2" == "tick") = false)
      (by decide : ("__c3" == "tick") = false)).trans (store_get_self _ _ _)
  have he4 : f4.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("tick" == "lpFee") = false)
      (by decide : ("__c2" == "lpFee") = false) (by decide : ("__c3" == "lpFee") = false)
      (by decide : ("__c4" == "lpFee") = false)).trans he
  have hpre : ExecBlock config f evm ((poolInitializeFunction.body.drop 4).take 5) (.ok f5 evm) :=
    ExecBlock.consNormal (ExecStmt.assign (evalLocalValue ht) (assignLocalValue ho))
      (ExecBlock.consNormal (ExecStmt.letDecl hzero)
      (ExecBlock.consNormal (slot0SetSqrtCall (f := f2) hf hpc (evalLocalValue (store_get_self _ _ _)) (evalLocalValue hp2) "__c3")
      (ExecBlock.consNormal (slot0SetTickCall (f := f3) hf (evalLocalValue (store_get_self _ _ _)) (evalLocalValue ht3) "__c4")
      (ExecBlock.consNormal (slot0LPFeeCall (f := f4) hf hec (evalLocalValue (store_get_self _ _ _)) (evalLocalValue he4) "__c5")
        ExecBlock.nil))))
  have hs5 : f5.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne5 _ _ _ _ _ _ (by decide : ("tick" == "self") = false)
      (by decide : ("__c2" == "self") = false) (by decide : ("__c3" == "self") = false)
      (by decide : ("__c4" == "self") = false) (by decide : ("__c5" == "self") = false)).trans hs
  have ht5 : f5.locals.get? "tick" = some (.int (EVM.signed tick)) :=
    (store_get_ne2 _ _ _ (by decide : ("__c4" == "tick") = false)
      (by decide : ("__c5" == "tick") = false)).trans ht3
  have hval := evalLocalValue (cfg := config) (f := f5) (evm := evm) (store_get_self _ _ _)
  have hwrite := poolSlot0_write (evm := evm) hs5 (poolInitializeWord price tick fee)
  refine ⟨f5, execFuncBody_prepend hpre ?_⟩
  simp only [poolInitializeTailResult]
  by_cases hperm : evm.executionEnv.perm = false
  · simp only [if_pos hperm]
    exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.assignStatic hval hwrite hperm))
  · simp only [if_neg hperm]
    exact .execBlockRet (ExecBlock.consNormal (ExecStmt.assign hval hwrite)
      (ABlock.start.returns (evalLocalValue ht5)))

theorem poolInitializeBody {f : Frame} {evm : EVM.State} {id price fee : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (he : f.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)))
    (hpc : price.toNat < 2^160) (hec : fee.toNat < 2^24) :
    ∃ f', ExecFuncBody config f evm poolInitializeFunction.body (poolInitializeResult f' evm id price fee) := by
  let f1 : Frame := {f with locals := f.locals.insert "tick" (.int 0)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c0" (.int (Int.ofNat (poolSqrtPriceWord evm id).toNat))}
  have hinit : ExecStmt config f evm poolInitializeFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hs1 : f1.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne _ _ (by decide : ("tick" == "self") = false)).trans hs
  have hget := slot0SqrtCall (f := f1) (evm := evm) hf (poolSlot0_read hs1) "__c0"
  have hguard := evalNeWords (evalLocalValue (cfg := config) (f := f2) (evm := evm) (store_get_self _ _ _))
    (show evalExpr? config f2 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hz : poolSqrtPriceWord evm id ≠ ⟨0⟩
  · simp only [poolInitializeResult, if_pos hz]
    exact ⟨f2, .execBlockRevert (ExecBlock.consNormal hinit (ExecBlock.consNormal hget
      (ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hguard)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))⟩
  · have hp2 : f2.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) :=
      (store_get_ne2 _ _ _ (by decide : ("tick" == "sqrtPriceX96") = false)
        (by decide : ("__c0" == "sqrtPriceX96") = false)).trans hp
    have hprefix : ExecBlock config f evm (poolInitializeFunction.body.take 3) (.ok f2 evm) :=
      ExecBlock.consNormal hinit (ExecBlock.consNormal hget (ExecBlock.consNormal
        (ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hguard) ExecBlock.nil) ExecBlock.nil))
    have hcall := tickPriceCall (f := f2) (evm := evm) hf (evalLocalValue hp2) "__c1"
    cases hr : tickPriceResult price with
    | none =>
      simp only [hr] at hcall
      simp only [poolInitializeResult, if_neg hz, hr]
      exact ⟨f2, execFuncBody_prepend hprefix (.execBlockRevert (ExecBlock.consRevert hcall))⟩
    | some tick =>
      simp only [hr] at hcall
      let f3 : Frame := {f2 with locals := f2.locals.insert "__c1" (.int (EVM.signed tick))}
      have hs3 : f3.locals.get? "self" = some (poolRefValue id) :=
        (store_get_ne2 _ _ _ (by decide : ("__c0" == "self") = false)
          (by decide : ("__c1" == "self") = false)).trans hs1
      have hp3 : f3.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c1" == "sqrtPriceX96") = false)).trans hp2
      have he3 : f3.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)) :=
        (store_get_ne3 _ _ _ _ (by decide : ("tick" == "lpFee") = false)
          (by decide : ("__c0" == "lpFee") = false) (by decide : ("__c1" == "lpFee") = false)).trans he
      have ht3 : f3.locals.get? "tick" = some (.int 0) :=
        (store_get_ne2 _ _ _ (by decide : ("__c0" == "tick") = false)
          (by decide : ("__c1" == "tick") = false)).trans (store_get_self _ _ _)
      obtain ⟨f4, htail⟩ := poolInitializeTail (f := f3) (evm := evm) hf hs3 hp3 he3
        (store_get_self _ _ _) ht3 hpc hec
      simp only [poolInitializeResult, if_neg hz, hr]
      exact ⟨f4, execFuncBody_prepend hprefix
        (execFuncBody_prepend (execBlock_singleton hcall) htail)⟩

def poolInitializeCallResult (f : Frame) (evm : EVM.State) (id price fee : UInt256) (retVar : Ident) : ExecResult :=
  resumeCallResult f retVar (poolInitializeResult f evm id price fee)

theorem poolInitializeCall {f : Frame} {evm : EVM.State} {es ep ef : Expr} {id price fee : UInt256}
    (hf : f.contract = contract) (hpc : price.toNat < 2^160) (hec : fee.toNat < 2^24)
    (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (hp : evalExpr? config f evm ep = .ok (.int (Int.ofNat price.toNat)))
    (he : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Pool_initialize" [es, ep, ef] retVar)
      (poolInitializeCallResult f evm id price fee retVar) := by
  obtain ⟨f', hb⟩ := poolInitializeBody
    (f := {f with locals := (((∅ : Store).insert "lpFee" (.int (Int.ofNat fee.toNat))).insert
      "sqrtPriceX96" (.int (Int.ofNat price.toNat))).insert "self" (poolRefValue id)})
    (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "sqrtPriceX96") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("sqrtPriceX96" == "lpFee") = false)
      (by decide : ("self" == "lpFee") = false)).trans (store_get_self _ _ _)) hpc hec
  have hcall := internalCallFunctionExec (caller := f) (name := "Pool_initialize") (retVar := retVar)
    (args := [es, ep, ef]) (argVals := [poolRefValue id, .int (Int.ofNat price.toNat), .int (Int.ofNat fee.toNat)])
    (by simp only [evalExprs?, hs, hp, he, bind, EvalResult.bind, pure])
    (by rw [hf]; exact poolInitialize_lookup) rfl hb
  unfold poolInitializeCallResult
  unfold poolInitializeResult at hcall ⊢
  by_cases hz : poolSqrtPriceWord evm id ≠ ⟨0⟩
  · simpa only [if_pos hz] using hcall
  · simp only [if_neg hz] at hcall ⊢
    cases hr : tickPriceResult price <;>
      simpa only [hr, poolInitializeTailResult, resumeCallResult_ite, resumeCallResult_static,
        resumeCallResult_returned] using hcall

end Benchmarks.UniswapV4PoolManager

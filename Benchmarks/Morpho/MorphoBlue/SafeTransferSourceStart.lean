import Benchmarks.Morpho.MorphoBlue.SafeTransferSourceTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferFunctionFor (isFrom : Bool) : FunctionDecl :=
  if isFrom then safeTransferFromFunction else safeTransferFunction

def safeTransferInputAllocation (isFrom : Bool) : Nat := if isFrom then 224 else 192

def safeTransferCodeGuard : Expr :=
  .binary .gt (.extCodeSize (.var "token")) (.intLit 0)

def safeTransferCallDataExpr (isFrom : Bool) : Expr :=
  if isFrom then .abiEncodeCall "transferFrom" [.var "from", .var "to", .var "value"]
  else .abiEncodeCall "transfer" [.var "to", .var "value"]

def safeTransferCallStmt (isFrom : Bool) : Stmt :=
  .lowLevelCall (.var "token") (.intLit 0) (safeTransferCallDataExpr isFrom) "success" "returndata"

theorem safeTransferFunctionFor_body (isFrom : Bool) :
    (safeTransferFunctionFor isFrom).body =
      [.assign .localVar ⟨"__memory", []⟩
        (.binary .add (.var "__memory") (.intLit (Int.ofNat (safeTransferInputAllocation isFrom)))),
       .require (safeTransferCap (.var "__memory")), .require safeTransferCodeGuard,
       safeTransferCallStmt isFrom] ++ safeTransferTail := by
  cases isFrom <;> rfl

def safeTransferPrepared (frame : Frame) (isFrom : Bool) (n : Nat) : Frame :=
  { frame with locals :=
      frame.locals.insert "__memory" (.int (Int.ofNat (n + safeTransferInputAllocation isFrom))) }

theorem safeTransferPrepared_memory (frame : Frame) (isFrom : Bool) (n : Nat) :
    (safeTransferPrepared frame isFrom n).locals.get? "__memory" =
      some (.int (Int.ofNat (n + safeTransferInputAllocation isFrom))) := store_get_self _ _ _

theorem safeTransferPrepared_other (frame : Frame) (isFrom : Bool) (n : Nat) (name : Ident)
    (hn : name ≠ "__memory") :
    (safeTransferPrepared frame isFrom n).locals.get? name = frame.locals.get? name :=
  store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using Ne.symm hn)

theorem safeTransferSource_allocate {frame : Frame} {evm : EVM.State} {n : Nat}
    (isFrom : Bool) (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n))) :
    ABlock config evm frame (safeTransferFunctionFor isFrom).body
      (safeTransferPrepared frame isFrom n)
      ([.require (safeTransferCap (.var "__memory")), .require safeTransferCodeGuard,
        safeTransferCallStmt isFrom] ++ safeTransferTail) := by
  rw [safeTransferFunctionFor_body]
  exact ⟨fun hh ↦ .consNormal
    (.assign (safeTransferMemoryAdd_eval hm _) (assignLocalWord hm)) hh⟩

theorem safeTransferSource_inputRevert {frame : Frame} {evm : EVM.State} {n : Nat}
    (isFrom : Bool) (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hc : 2 ^ 64 ≤ n + safeTransferInputAllocation isFrom) :
    ExecFuncBody config frame evm (safeTransferFunctionFor isFrom).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (safeTransferSource_allocate isFrom hm).run (ExecBlock.consRevert (.requireFalse ?_))
  have he : evalExpr? config (safeTransferPrepared frame isFrom n) evm (.var "__memory") =
      .ok (.int (Int.ofNat (n + safeTransferInputAllocation isFrom))) := by
    simp only [evalExpr?, safeTransferPrepared_memory, EvalResult.ofOption]
  exact (safeTransferCap_eval he).trans (by rw [decide_eq_false (by omega)])

theorem safeTransferSource_afterInput {frame : Frame} {evm : EVM.State} {n : Nat}
    (isFrom : Bool) (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hc : n + safeTransferInputAllocation isFrom < 2 ^ 64) :
    ABlock config evm frame (safeTransferFunctionFor isFrom).body
      (safeTransferPrepared frame isFrom n)
      ([.require safeTransferCodeGuard, safeTransferCallStmt isFrom] ++ safeTransferTail) := by
  apply (safeTransferSource_allocate isFrom hm).requireStep
  have he : evalExpr? config (safeTransferPrepared frame isFrom n) evm (.var "__memory") =
      .ok (.int (Int.ofNat (n + safeTransferInputAllocation isFrom))) := by
    simp only [evalExpr?, safeTransferPrepared_memory, EvalResult.ofOption]
  exact (safeTransferCap_eval he).trans (by rw [decide_eq_true (by omega)])

theorem safeTransferSource_noCode {frame : Frame} {evm : EVM.State} {n : Nat}
    (isFrom : Bool) (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hc : n + safeTransferInputAllocation isFrom < 2 ^ 64)
    (hcode : evalExpr? config (safeTransferPrepared frame isFrom n) evm safeTransferCodeGuard =
      .ok (.bool false)) :
    ExecFuncBody config frame evm (safeTransferFunctionFor isFrom).body .reverted :=
  .execBlockRevert ((safeTransferSource_afterInput isFrom hm hc).run
    (.consRevert (.requireFalse hcode)))

def safeTransferCalled (frame : Frame) (isFrom : Bool) (n : Nat) (z : Bool)
    (out : ByteArray) : Frame :=
  { safeTransferPrepared frame isFrom n with
    locals := ((safeTransferPrepared frame isFrom n).locals.insert "success" (.bool z)).insert
      "returndata" (.bytes out) }

theorem safeTransferSource_call {frame : Frame} {evm evm' : EVM.State} {n : Nat}
    {isFrom z : Bool} {token : AccountAddress} {calldata out : ByteArray}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hc : n + safeTransferInputAllocation isFrom < 2 ^ 64)
    (hcode : evalExpr? config (safeTransferPrepared frame isFrom n) evm safeTransferCodeGuard =
      .ok (.bool true))
    (ht : (safeTransferPrepared frame isFrom n).locals.get? "token" = some (.address token))
    (hd : evalExpr? config (safeTransferPrepared frame isFrom n) evm
      (safeTransferCallDataExpr isFrom) = .ok (.bytes calldata))
    (hcall : callViaEVM evm token 0 calldata (z, evm', out)) :
    StateBlock config frame evm (safeTransferFunctionFor isFrom).body
      (safeTransferCalled frame isFrom n z out) evm' safeTransferTail := by
  have hp := (safeTransferSource_afterInput isFrom hm hc).requireStep hcode
  apply StateBlock.step (StateBlock.ofABlock hp)
  have ht' : evalExpr? config (safeTransferPrepared frame isFrom n) evm (.var "token") =
      .ok (.address token) := by simp only [evalExpr?, ht, EvalResult.ofOption]
  have hc' : callViaEVM evm (EVM.address token.val) 0 calldata (z, evm', out) := by
    have ht : EVM.address token.val = token := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt token.isLt
    simpa only [ht] using hcall
  have hv : evalExpr? config (safeTransferPrepared frame isFrom n) evm (.intLit 0) =
      .ok (.int 0) := by simp only [evalExpr?, pure]
  cases z
  · exact ExecStmt.lowLevelCallFailure ht' hv hd hc'
  · exact ExecStmt.lowLevelCallSuccess ht' hv hd hc'

end Benchmarks.Morpho.MorphoBlue

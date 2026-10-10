import Benchmarks.UniswapV4PoolManager.BooleanSource
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev hookValidationFunction : FunctionDecl := contract.functions[30]!
theorem hookValidation_lookup : lookupCallable? contract "Hooks_isValidHookAddress" =
    some hookValidationFunction.toCallable := rfl

def hookPairInvalid (hook required extra : UInt256) : Bool :=
  decide (UInt256.land hook required = ⟨0⟩) && decide (UInt256.land hook extra ≠ ⟨0⟩)
def hookBaseValid (hook fee : UInt256) : Bool :=
  if hook = ⟨0⟩ then decide (fee ≠ UInt256.ofNat 8388608) else
    decide (UInt256.land hook (UInt256.ofNat 16383) ≠ ⟨0⟩) || decide (fee = UInt256.ofNat 8388608)
def hookAddressValid (hook fee : UInt256) : Bool :=
  if hookPairInvalid hook (UInt256.ofNat 128) (UInt256.ofNat 8) then false else
  if hookPairInvalid hook (UInt256.ofNat 64) (UInt256.ofNat 4) then false else
  if hookPairInvalid hook (UInt256.ofNat 1024) (UInt256.ofNat 2) then false else
  if hookPairInvalid hook (UInt256.ofNat 256) (UInt256.ofNat 1) then false else hookBaseValid hook fee

def hookFlagExpr (mask : UInt256) : Expr :=
  .binary (.bitAnd (.uint ⟨160, by decide⟩)) (.var "flags") (.intLit (Int.ofNat mask.toNat))
def hookPairExpr (required extra : UInt256) : Expr :=
  .binary .and (.binary .eq (hookFlagExpr required) (.intLit 0))
    (.binary .ne (hookFlagExpr extra) (.intLit 0))

theorem evalHookFlag {f : Frame} {evm : EVM.State} {hook : UInt256}
    (hf : f.locals.get? "flags" = some (.int (Int.ofNat hook.toNat)))
    (hh : hook.toNat < 2^160) (mask : UInt256) (hm : mask.toNat < 2^160) :
    evalExpr? config f evm (hookFlagExpr mask) = .ok (.int (Int.ofNat (UInt256.land hook mask).toNat)) :=
  evalUintWordAnd ⟨160, by decide⟩ hh hm (evalLocalValue hf) (by simp only [evalExpr?, pure])

theorem evalHookPair {f : Frame} {evm : EVM.State} {hook : UInt256}
    (hf : f.locals.get? "flags" = some (.int (Int.ofNat hook.toNat))) (hh : hook.toNat < 2^160)
    (required extra : UInt256) (hr : required.toNat < 2^160) (he : extra.toNat < 2^160) :
    evalExpr? config f evm (hookPairExpr required extra) = .ok (.bool (hookPairInvalid hook required extra)) := by
  have hz : evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  exact evalAndBool (evalEqWords (evalHookFlag hf hh required hr) hz) (evalNeWords (evalHookFlag hf hh extra he) hz)

theorem hookBaseValidReturn {f : Frame} {evm : EVM.State} {hook : AccountAddress} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.address hook))
    (hf : f.locals.get? "flags" = some (.int (Int.ofNat (accountWord hook).toNat)))
    (he : f.locals.get? "fee" = some (.int (Int.ofNat fee.toNat))) :
    ExecBlock config f evm (hookValidationFunction.body.drop 5)
      (.returned f evm (some [.bool (hookBaseValid (accountWord hook) fee)])) := by
  have hz : evalExpr? config f evm (.cast (.intLit 0) (.elem .address)) = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [evalExpr?, bind, EvalResult.bind, pure]; rfl
  have hc := evalEqAddress (evalLocalValue (cfg := config) (evm := evm) hs) hz
  have hzero : (hook = AccountAddress.ofNat 0) ↔ accountWord hook = ⟨0⟩ :=
    accountWord_eq_iff hook ⟨0⟩ (by decide)
  simp only [hzero] at hc
  have hlit : evalExpr? config f evm (.intLit 8388608) = .ok (.int (Int.ofNat (UInt256.ofNat 8388608).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  have heq := evalEqWords (evalLocalValue (cfg := config) (evm := evm) he) hlit
  have hne := evalNeWords (evalLocalValue (cfg := config) (evm := evm) he) hlit
  have hflags := evalHookFlag (evm := evm) hf (accountWord_canonical hook) (UInt256.ofNat 16383) (by decide)
  have hor := evalOrBool (evalNeWords hflags
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)) heq
  have hret := evalBoolIte hc hne hor
  simp only [decide_eq_true_eq] at hret
  exact ABlock.start.returns hret

theorem hookValidationBody {f : Frame} {evm : EVM.State} {hook : AccountAddress} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.address hook))
    (he : f.locals.get? "fee" = some (.int (Int.ofNat fee.toNat))) :
    ExecFuncBody config f evm hookValidationFunction.body
      (.returned {f with locals := f.locals.insert "flags" (.int (Int.ofNat (accountWord hook).toNat))}
        evm (some [.bool (hookAddressValid (accountWord hook) fee)])) := by
  let f1 : Frame := {f with locals := f.locals.insert "flags" (.int (Int.ofNat (accountWord hook).toNat))}
  have hflags : f1.locals.get? "flags" = some (.int (Int.ofNat (accountWord hook).toNat)) := store_get_self _ _ _
  have h0 := evalHookPair (evm := evm) hflags (accountWord_canonical hook) (UInt256.ofNat 128) (UInt256.ofNat 8) (by decide) (by decide)
  have h1 := evalHookPair (evm := evm) hflags (accountWord_canonical hook) (UInt256.ofNat 64) (UInt256.ofNat 4) (by decide) (by decide)
  have h2 := evalHookPair (evm := evm) hflags (accountWord_canonical hook) (UInt256.ofNat 1024) (UInt256.ofNat 2) (by decide) (by decide)
  have h3 := evalHookPair (evm := evm) hflags (accountWord_canonical hook) (UInt256.ofNat 256) (UInt256.ofNat 1) (by decide) (by decide)
  have hend := hookBaseValidReturn (f := f1) (evm := evm)
    ((store_get_ne _ _ (by decide : ("flags" == "self") = false)).trans hs) hflags
    ((store_get_ne _ _ (by decide : ("flags" == "fee") = false)).trans he)
  exact .execBlockRet (ExecBlock.consNormal (ExecStmt.letDecl (evalAddressUint160 (evalLocalValue hs)))
    (falseReturnGuard h0 (falseReturnGuard h1 (falseReturnGuard h2 (falseReturnGuard h3 hend)))))

theorem hookValidationCall {f : Frame} {evm : EVM.State} {es ef : Expr} {hook : AccountAddress} {fee : UInt256}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (he : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_isValidHookAddress" [es, ef] retVar)
      (.ok {f with locals := f.locals.insert retVar (.bool (hookAddressValid (accountWord hook) fee))} evm) := by
  apply internalCallFunctionReturn (argVals := [.address hook, .int (Int.ofNat fee.toNat)])
    (value := some [.bool (hookAddressValid (accountWord hook) fee)])
    (by simp only [evalExprs?, hs, he, bind, EvalResult.bind, pure])
    (by rw [hf]; exact hookValidation_lookup) rfl
  exact hookValidationBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "fee") = false)).trans (store_get_self _ _ _))

end Benchmarks.UniswapV4PoolManager

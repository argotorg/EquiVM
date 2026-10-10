import Benchmarks.UniswapV4PoolManager.TransientSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev currencySlot : UInt256 := ⟨0x27e098c505d44ec3574004bca052aabf76bd35004c182099d8c575fb238593b9⟩
abbrev reservesSlot : UInt256 := ⟨0x1e0745a7db1623981f0b2a5d4232364c00787266eb75ad546f190e6cebe9bd95⟩
abbrev currencyZeroFunction : FunctionDecl := contract.functions[22]!
abbrev resetCurrencyFunction : FunctionDecl := contract.functions[23]!
abbrev syncReservesFunction : FunctionDecl := contract.functions[25]!

theorem currencyZero_lookup : lookupCallable? contract "CurrencyLibrary_isAddressZero" = some currencyZeroFunction.toCallable := rfl
theorem resetCurrency_lookup : lookupCallable? contract "CurrencyReserves_resetCurrency" = some resetCurrencyFunction.toCallable := rfl
theorem syncReserves_lookup : lookupCallable? contract "CurrencyReserves_syncCurrencyAndReserves" = some syncReservesFunction.toCallable := rfl

theorem currencyZeroBody {f : Frame} {evm : EVM.State} {currency : AccountAddress}
    (hc : f.locals.get? "currency" = some (.address currency)) :
    ExecFuncBody config f evm currencyZeroFunction.body
      (.returned f evm (some [.bool (decide (currency = AccountAddress.ofNat 0))])) := by
  apply ExecFuncBody.execBlockRet
  exact ABlock.start.returns (evalEqAddress (evalLocalValue hc)
    (evalCastValue (show evalExpr? config f evm (.intLit 0) = .ok (.int 0) from by simp only [evalExpr?, pure]) rfl))

theorem currencyZeroCall {f : Frame} {evm : EVM.State} {e : Expr} {currency : AccountAddress}
    (hf : f.contract = contract) (hc : evalExpr? config f evm e = .ok (.address currency)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyLibrary_isAddressZero" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.bool (decide (currency = AccountAddress.ofNat 0)))} evm) := by
  apply internalCallFunctionReturn (argVals := [.address currency])
    (value := some [.bool (decide (currency = AccountAddress.ofNat 0))])
    (evalExprs?_singleton hc) (by rw [hf]; exact currencyZero_lookup) rfl
  exact currencyZeroBody (store_get_self _ _ _)

theorem evalCurrencySlot {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    evalExpr? config f evm (.const "CURRENCY_SLOT") = .ok (.int (Int.ofNat currencySlot.toNat)) := by
  rw [evalExpr?, hf]; rfl

theorem evalReservesSlot {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    evalExpr? config f evm (.const "RESERVES_SLOT") = .ok (.int (Int.ofNat reservesSlot.toNat)) := by
  rw [evalExpr?, hf]; rfl

def resetCurrencyPost (evm : EVM.State) : EVM.State :=
  Solm.EVM.transientStore evm evm.executionEnv.codeOwner currencySlot ⟨0⟩
def syncReservesCurrencyPost (evm : EVM.State) (currency : AccountAddress) : EVM.State :=
  Solm.EVM.transientStore evm evm.executionEnv.codeOwner currencySlot (accountWord currency)
def syncReservesPost (evm : EVM.State) (currency : AccountAddress) (value : UInt256) : EVM.State :=
  Solm.EVM.transientStore (syncReservesCurrencyPost evm currency) evm.executionEnv.codeOwner reservesSlot value

theorem resetCurrencyBody {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    ExecFuncBody config f evm resetCurrencyFunction.body
      (if evm.executionEnv.perm = false then .staticViolation else .returned f (resetCurrencyPost evm) none) := by
  have he : evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  have hw := rawTransient_write (evm := evm) ⟨0⟩ hf (evalCurrencySlot hf)
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.assignTransientStatic he hw hp))
  · rw [if_neg hp]
    exact .execBlockOK (ExecBlock.consNormal (ExecStmt.assign he hw) ExecBlock.nil)

theorem resetCurrencyCall {f : Frame} {evm : EVM.State} (hf : f.contract = contract) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyReserves_resetCurrency" [] retVar)
      (if evm.executionEnv.perm = false then .staticViolation
       else .ok {f with locals := f.locals.insert retVar .unit} (resetCurrencyPost evm)) := by
  have hb := resetCurrencyBody (f := {f with locals := ∅}) (evm := evm) hf
  have hh := internalCallFunctionExec (caller := f) (name := "CurrencyReserves_resetCurrency")
    (retVar := retVar) (args := []) (argVals := []) rfl (by rw [hf]; exact resetCurrency_lookup) rfl hb
  simpa only [resumeCallResult_ite, resumeCallResult_static, resumeCallResult_returned] using hh

theorem syncReservesBody {f : Frame} {evm : EVM.State} {currency : AccountAddress} {value : UInt256}
    (hf : f.contract = contract) (hc : f.locals.get? "currency" = some (.address currency))
    (hv : f.locals.get? "value" = some (.int (Int.ofNat value.toNat))) :
    ExecFuncBody config f evm syncReservesFunction.body
      (if evm.executionEnv.perm = false then .staticViolation
       else .returned f (syncReservesPost evm currency value) none) := by
  have he := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
    (evalAddressUint160 (cfg := config) (evm := evm) (evalLocalValue hc))
  rw [normalizeInt_uint256_word] at he
  have hw := rawTransient_write (evm := evm) (accountWord currency) hf (evalCurrencySlot hf)
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.assignTransientStatic he hw hp))
  · rw [if_neg hp]
    have hw2 := rawTransient_write (evm := syncReservesCurrencyPost evm currency) value hf (evalReservesSlot hf)
    have hI : (syncReservesCurrencyPost evm currency).executionEnv = evm.executionEnv := by
      simp only [syncReservesCurrencyPost, transientStore_executionEnv]
    rw [hI] at hw2
    apply ExecFuncBody.execBlockOK
    exact ExecBlock.consNormal (ExecStmt.assign he hw)
      (ExecBlock.consNormal (ExecStmt.assign (evalLocalValue hv) hw2) ExecBlock.nil)

theorem syncReservesCall {f : Frame} {evm : EVM.State} {ec ev : Expr} {currency : AccountAddress} {value : UInt256}
    (hf : f.contract = contract) (hc : evalExpr? config f evm ec = .ok (.address currency))
    (hv : evalExpr? config f evm ev = .ok (.int (Int.ofNat value.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyReserves_syncCurrencyAndReserves" [ec, ev] retVar)
      (if evm.executionEnv.perm = false then .staticViolation
       else .ok {f with locals := f.locals.insert retVar .unit} (syncReservesPost evm currency value)) := by
  have hb := syncReservesBody (f := {f with locals := (((∅ : Store).insert "value"
    (.int (Int.ofNat value.toNat))).insert "currency" (.address currency))}) (evm := evm) hf
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("currency" == "value") = false)).trans (store_get_self _ _ _))
  have hh := internalCallFunctionExec (caller := f) (name := "CurrencyReserves_syncCurrencyAndReserves")
    (retVar := retVar) (args := [ec, ev]) (argVals := [.address currency, .int (Int.ofNat value.toNat)])
    (by simp only [evalExprs?, hc, hv, bind, EvalResult.bind, pure])
    (by rw [hf]; exact syncReserves_lookup) rfl hb
  simpa only [resumeCallResult_ite, resumeCallResult_static, resumeCallResult_returned] using hh

end Benchmarks.UniswapV4PoolManager

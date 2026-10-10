import Benchmarks.UniswapV4PoolManager.PoolSetSlot0Source
import Benchmarks.UniswapV4PoolManager.WordArrayLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def protocolFeeValid (fee : UInt256) : Prop :=
  (UInt256.land fee ⟨4095⟩).toNat < 1001 ∧ (UInt256.land fee ⟨16773120⟩).toNat < 4100096
instance (fee : UInt256) : Decidable (protocolFeeValid fee) := inferInstanceAs (Decidable (_ ∧ _))

abbrev protocolFeeValidFunction : FunctionDecl := contract.functions[51]!
abbrev slot0ProtocolFeeFunction : FunctionDecl := contract.functions[87]!
theorem protocolFeeValid_lookup : lookupCallable? contract "ProtocolFeeLibrary_isValidProtocolFee" =
    some protocolFeeValidFunction.toCallable := rfl
theorem slot0ProtocolFee_lookup : lookupCallable? contract "Slot0Library_setProtocolFee" =
    some slot0ProtocolFeeFunction.toCallable := rfl

theorem protocolFeeValidBody {f : Frame} {evm : EVM.State} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm protocolFeeValidFunction.body
      (.returned f evm (some [.bool (decide (protocolFeeValid fee))])) := by
  have h0 := evalUintWordAnd (y := ⟨4095⟩) ⟨24, by decide⟩ hc (by decide)
    (evalLocalValue (cfg := config) (evm := evm) hs)
    (show evalExpr? config f evm (.intLit 4095) = .ok (.int (Int.ofNat (⟨4095⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  have h1 := evalUintWordAnd (y := ⟨16773120⟩) ⟨24, by decide⟩ hc (by decide)
    (evalLocalValue (cfg := config) (evm := evm) hs)
    (show evalExpr? config f evm (.intLit 16773120) = .ok (.int (Int.ofNat (⟨16773120⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  have he := evalAndBool (evalNatLt h0 (rhs := .intLit 1001) (b := 1001) (by simp only [evalExpr?, pure]; rfl))
    (evalNatLt h1 (rhs := .intLit 4100096) (b := 4100096) (by simp only [evalExpr?, pure]; rfl))
  simpa only [protocolFeeValid, Bool.decide_and] using he

theorem protocolFeeValidCall {f : Frame} {evm : EVM.State} {e : Expr} {fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "ProtocolFeeLibrary_isValidProtocolFee" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.bool (decide (protocolFeeValid fee)))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat)])
    (value := some [.bool (decide (protocolFeeValid fee))]) (evalExprs?_singleton he)
    (by rw [hf]; exact protocolFeeValid_lookup) rfl
  exact protocolFeeValidBody (store_get_self _ _ _) hc

def protocolFeeClearMask : UInt256 := ⟨115792089237315784047456174635831223332708078880448723302429075438902230122495⟩
def slot0ProtocolFeeWord (packed fee : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land packed protocolFeeClearMask) (UInt256.shiftLeft fee ⟨184⟩)

theorem slot0ProtocolFeeBody {f : Frame} {evm : EVM.State} {packed fee : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed))
    (hf : f.locals.get? "_protocolFee" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm slot0ProtocolFeeFunction.body
      (.returned {f with locals := f.locals.insert "cleared" (.int (Int.ofNat (UInt256.land packed protocolFeeClearMask).toNat))}
        evm (some [wordBytes32Value (slot0ProtocolFeeWord packed fee)])) :=
  wordFieldSetBodyExec protocolFeeClearMask 184 ⟨24, by decide⟩ "_protocolFee" (by decide) (by decide) hp hf hc

theorem slot0ProtocolFeeCall {f : Frame} {evm : EVM.State} {ep ef : Expr} {packed fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (hp : evalExpr? config f evm ep = .ok (wordBytes32Value packed))
    (he : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_setProtocolFee" [ep, ef] retVar)
      (.ok {f with locals := f.locals.insert retVar (wordBytes32Value (slot0ProtocolFeeWord packed fee))} evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed, .int (Int.ofNat fee.toNat)])
    (value := some [wordBytes32Value (slot0ProtocolFeeWord packed fee)])
    (by simp only [evalExprs?, hp, he, bind, EvalResult.bind, pure])
    (by rw [hf]; exact slot0ProtocolFee_lookup) rfl
  exact slot0ProtocolFeeBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("_packed" == "_protocolFee") = false)).trans (store_get_self _ _ _)) hc

def protocolControllerWord (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) solcAddrMask
def protocolControllerAuthorized (evm : EVM.State) : Prop := accountWord evm.executionEnv.source = protocolControllerWord evm
instance (evm : EVM.State) : Decidable (protocolControllerAuthorized evm) := inferInstanceAs (Decidable (_ = _))

theorem protocolControllerWord_accountMap {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I) :
    UInt256.land (solcSlotWordAt ⟨2⟩ evm.accountMap I) solcAddrMask = protocolControllerWord evm := by
  unfold protocolControllerWord
  rw [storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])]

theorem protocolControllerGuard {f : Frame} {evm : EVM.State}
    (hf : f.contract = contract) (hb : f.locals.get? "protocolFeeController" = none) :
    evalExpr? config f evm (.binary .ne (.env .caller) (.storage {base := "protocolFeeController"})) =
      .ok (.bool (decide (¬protocolControllerAuthorized evm))) := by
  have hr := addressScalarRead (evm := evm) (slot := ⟨2⟩) hf hb (by decide +kernel) rfl
  have he := evalNeAddress (by simp only [evalExpr?, envValue, pure] :
    evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source)) hr
  simpa only [protocolControllerAuthorized, protocolControllerWord,
    ne_eq, accountWord_eq_iff _ _ (solcAddrMask_result_canonical _)] using he

end Benchmarks.UniswapV4PoolManager

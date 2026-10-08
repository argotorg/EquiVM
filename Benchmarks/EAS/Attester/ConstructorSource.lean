import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.ABIHelpers
import Benchmarks.EAS.Attester.LocalArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def constructorArgsStore (eas : AccountAddress) : Store :=
  Std.HashMap.ofList [("eas", .address eas)]

def constructorFinalImms (eas : AccountAddress) : Store :=
  (initialImmutables contract).insert "_eas" (.address eas)

theorem constructorFinalImms_get (eas : AccountAddress) :
    (constructorFinalImms eas).get? "_eas" = some (.address eas) := by
  simp [constructorFinalImms]

theorem constructorFinalImms_fit (eas : AccountAddress) :
    immutablesFit contract (constructorFinalImms eas) := by
  intro d hd
  change d ∈ [⟨"_eas", .address⟩] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst d
  exact ⟨.address eas, constructorFinalImms_get eas, rfl⟩

theorem constructorArgsStore_get (eas : AccountAddress) :
    (constructorArgsStore eas).get? "eas" = some (.address eas) := by
  simp [constructorArgsStore]

theorem constructorDeployment_shape {args : List Value} {code : ByteArray}
    (hd : config.selfDeployment attesterCreationBytecode args = some code) :
    ∃ eas : AccountAddress, args = [.address eas] ∧
      code = attesterCreationBytecode ++ (UInt256.ofNat eas.val).toByteArray := by
  change (do
    let bytes ← encodeABIValues? [.elem .address] args
    pure (attesterCreationBytecode ++ bytes.toByteArray)) = some code at hd
  cases args with
  | nil => simp [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at hd
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          simp [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
            staticABIEncodedSize?, isDynamicABIType] at hd
      | nil =>
          cases arg <;>
            simp only [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
              staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?,
              bind, Option.bind, pure, if_false, Option.some.injEq, List.append_nil,
                  List.nil_append,
              reduceCtorEq] at hd
          rename_i eas
          exact ⟨eas, rfl, by simpa only [word_toBytesBE_toByteArray_eq_toByteArray] using hd.symm⟩

theorem constructorGuard_eval {imms : Store} {evm : State} (eas : AccountAddress) :
    evalExpr? config ⟨contract, constructorArgsStore eas, imms⟩ evm
      (.binary .ne (.var "eas") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (eas ≠ ⟨0, by decide⟩))) := by
  simp only [evalExpr?, constructorArgsStore_get, EvalResult.ofOption, bind, EvalResult.bind,
    pure, show castValue? (.int 0) (.elem .address) = some (.address ⟨0, by decide⟩) from by decide,
    evalBinaryOp?, beq_eq_decide, Value.address.injEq, decide_not]

theorem constructorSourceNonpayable {σ σ₀ A I} {g : UInt256} (eas : AccountAddress)
    (hv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address eas] σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := constructorArgsStore eas) rfl rfl rfl ?_
  exact ExecFuncBody.execBlockRevert (blockReverts_nonPayable hv)

theorem constructorSourceZero {σ σ₀ A I} {g : UInt256} (eas : AccountAddress)
    (hv : I.weiValue = ⟨0⟩) (hz : eas = ⟨0, by decide⟩) :
    solmCtorExec config contract [.address eas] σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := constructorArgsStore eas) rfl rfl rfl ?_
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hv)) ?_
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hz, ne_eq, not_true_eq_false, decide_false] using
    constructorGuard_eval (imms := initialImmutables contract)
      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) eas

theorem constructorSourceSuccess {σ σ₀ A I} {g : UInt256} (eas : AccountAddress)
    (hv : I.weiValue = ⟨0⟩) (hz : eas ≠ ⟨0, by decide⟩) :
    solmCtorExec config contract [.address eas] σ σ₀ g A I
      (.returned ⟨contract, constructorArgsStore eas, constructorFinalImms eas⟩
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) none) := by
  refine solmCtorExec.intro (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := constructorArgsStore eas) rfl rfl rfl ?_
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hz] using constructorGuard_eval
      (imms := initialImmutables contract) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) eas
  exact ExecBlock.consNormal (ExecStmt.setImmutable (ty := .address)
    (evalLocalValue (constructorArgsStore_get eas)) rfl rfl) ExecBlock.nil

end Benchmarks.EAS.Attester

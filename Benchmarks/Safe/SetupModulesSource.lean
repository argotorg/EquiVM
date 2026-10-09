import Benchmarks.Safe.ModuleStorage
import Benchmarks.Safe.OwnerCount
import Benchmarks.Safe.ExecuteSource
import Benchmarks.Safe.InternalCall
import Benchmarks.Safe.LocalArrays
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure SetupModulesInput where
  target : UInt256
  payload : ByteArray

namespace SetupModulesInput

def args (p : SetupModulesInput) : Store :=
  ((∅ : Store).insert "data" (.bytes p.payload)).insert "to"
    (.address (AccountAddress.ofNat p.target.toNat))

def frame (p : SetupModulesInput) : Frame := { contract := contract, locals := p.args }

def state (_ : SetupModulesInput) (evm : EVM.State) : EVM.State := writeModuleLink evm ⟨1⟩ ⟨1⟩

def finalFrame (p : SetupModulesInput) (z : Bool) : Frame :=
  { p.frame with locals := p.args.insert "setupSuccess" (.bool z) }

end SetupModulesInput

theorem safeSetupModulesTarget (p : SetupModulesInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (.var "to") =
      .ok (.address (AccountAddress.ofNat p.target.toNat)) :=
  evalLocalValue (by simp [SetupModulesInput.frame, SetupModulesInput.args])

theorem safeSetupModulesEmpty (p : SetupModulesInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (eqE (.storage (modulesRef sentinelAddr)) zeroAddr) =
      .ok (.bool (decide (moduleLink evm ⟨1⟩ = ⟨0⟩))) :=
  evalAddressZero (solcAddrMask_result_canonical _)
    (safeEvalModuleLink evm p.args sentinelAddr ⟨1⟩
      (by simp [SetupModulesInput.args, Std.HashMap.getElem_insert])
      (by decide) (safeEvalModuleSentinel evm p.args))

theorem safeSetupModulesCondition (p : SetupModulesInput) (evm : EVM.State)
    (hc : p.target.toNat < EVM.addressModulus) :
    evalExpr? config p.frame evm (neE (.var "to") zeroAddr) =
      .ok (.bool (decide (p.target ≠ ⟨0⟩))) :=
  evalAddressNonzero hc (safeSetupModulesTarget p evm)

theorem safeSetupModulesCode (p : SetupModulesInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (gtE (.extCodeSize (.var "to")) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord evm.accountMap p.target).toNat))) :=
  evalExpr_codeGuard_of_accounts_eq rfl
    (accountAddress_ofUInt256_eq_ofNat_toNat p.target).symm (safeSetupModulesTarget p evm)

theorem safeSetupModulesPrefix (p : SetupModulesInput) (evm : EVM.State) {result : ExecResult}
    (he : moduleLink evm ⟨1⟩ = ⟨0⟩)
    (htail : ExecBlock config p.frame (p.state evm) (setupModulesFunction.body.drop 2) result) :
    ExecBlock config p.frame evm setupModulesFunction.body result := by
  exact .consNormal (.requireTrue (by
      simpa only [he, decide_true] using safeSetupModulesEmpty p evm))
    (.consNormal (.assign (safeEvalModuleSentinel evm p.args)
      (safeAssignModuleLink evm p.args sentinelAddr ⟨1⟩ ⟨1⟩
        (by simp [SetupModulesInput.args, Std.HashMap.getElem_insert])
        (by decide) (by decide) (safeEvalModuleSentinel evm p.args))) htail)

theorem safeSetupModulesAlreadyInitialized (p : SetupModulesInput) (evm : EVM.State)
    (he : moduleLink evm ⟨1⟩ ≠ ⟨0⟩) :
    ExecFuncBody config p.frame evm setupModulesFunction.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (by
    simpa only [he, decide_false] using safeSetupModulesEmpty p evm)))

theorem safeSetupModulesZero (p : SetupModulesInput) (evm : EVM.State)
    (he : moduleLink evm ⟨1⟩ = ⟨0⟩) (hz : p.target = ⟨0⟩) :
    ExecFuncBody config p.frame evm setupModulesFunction.body
      (.returned p.frame (p.state evm) none) := by
  apply ExecFuncBody.execBlockOK
  apply safeSetupModulesPrefix p evm he
  exact .consNormal (.iteFalse (by
    simpa only [hz, ne_eq, not_true_eq_false, decide_false] using
      safeSetupModulesCondition p (p.state evm) (by rw [hz]; decide)) .nil) .nil

theorem safeSetupModulesNoCode (p : SetupModulesInput) (evm : EVM.State)
    (hc : p.target.toNat < EVM.addressModulus) (he : moduleLink evm ⟨1⟩ = ⟨0⟩)
    (ht : p.target ≠ ⟨0⟩) (hz : extCodeSizeWord (p.state evm).accountMap p.target = ⟨0⟩) :
    ExecFuncBody config p.frame evm setupModulesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safeSetupModulesPrefix p evm he
  exact .consRevert (.iteTrue
    ((safeSetupModulesCondition p (p.state evm) hc).trans (by congr 2; exact decide_eq_true ht))
    (.consRevert (.requireFalse (by
      simpa only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
        safeSetupModulesCode p (p.state evm)))))

theorem safeSetupModulesExecute (p : SetupModulesInput) (evm : EVM.State) {result : ExecResult}
    (hb : ExecFuncBody config (executeFrame (AccountAddress.ofNat p.target.toNat) ⟨0⟩
      p.payload ⟨1⟩ (UInt256.lnot ⟨0⟩)) evm executeFunction.body result) :
    ExecStmt config p.frame evm (.internalCall "execute"
      [.var "to", .intLit 0, .var "data", .intLit 1, maxUint256Expr] "setupSuccess")
      (internalCallResult p.frame "setupSuccess" result) := by
  apply internalCallFunctionResult (callee := executeFunction)
    (argVals := [.address (AccountAddress.ofNat p.target.toNat), .int 0, .bytes p.payload,
      .int 1, .int (Int.ofNat (UInt256.lnot ⟨0⟩).toNat)])
    (locals := executeArgs (AccountAddress.ofNat p.target.toNat) ⟨0⟩ p.payload ⟨1⟩
      (UInt256.lnot ⟨0⟩))
  · simp [SetupModulesInput.frame, SetupModulesInput.args, evalExprs?, evalExpr?,
      EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert,
      maxUint256Expr, maxUint256]
    decide +kernel
  · rfl
  · rfl
  · exact hb

theorem safeSetupModulesCalled (p : SetupModulesInput) (evm : EVM.State)
    {f' : Frame} {evm' : EVM.State} {z : Bool}
    (hc : p.target.toNat < EVM.addressModulus) (he : moduleLink evm ⟨1⟩ = ⟨0⟩)
    (ht : p.target ≠ ⟨0⟩) (hz : extCodeSizeWord (p.state evm).accountMap p.target ≠ ⟨0⟩)
    (hb : ExecFuncBody config (executeFrame (AccountAddress.ofNat p.target.toNat) ⟨0⟩
      p.payload ⟨1⟩ (UInt256.lnot ⟨0⟩)) (p.state evm) executeFunction.body
      (.returned f' evm' (some [.bool z]))) :
    ExecFuncBody config p.frame evm setupModulesFunction.body
      (if z then .returned (p.finalFrame z) evm' none else .reverted) := by
  have hcond : evalExpr? config p.frame (p.state evm) (neE (.var "to") zeroAddr) =
      .ok (.bool true) := (safeSetupModulesCondition p (p.state evm) hc).trans
        (by congr 2; exact decide_eq_true ht)
  have hp : 0 < (extCodeSizeWord (p.state evm).accountMap p.target).toNat :=
    Nat.pos_of_ne_zero (fun h ↦ hz (u256_inj h))
  have hcode : evalExpr? config p.frame (p.state evm)
      (gtE (.extCodeSize (.var "to")) (.intLit 0)) = .ok (.bool true) :=
    (safeSetupModulesCode p (p.state evm)).trans (by congr 2; exact decide_eq_true hp)
  have hcall := safeSetupModulesExecute p (p.state evm) hb
  have hresult : evalExpr? config (p.finalFrame z) evm' (.var "setupSuccess") =
      .ok (.bool z) := evalLocalValue (by simp [SetupModulesInput.finalFrame])
  cases z with
  | false =>
      exact .execBlockRevert (safeSetupModulesPrefix p evm he
        (.consRevert (.iteTrue hcond (.consNormal (.requireTrue hcode)
          (.consNormal hcall (.consRevert (.requireFalse hresult)))))))
  | true =>
      exact .execBlockOK (safeSetupModulesPrefix p evm he
        (.consNormal (.iteTrue hcond (.consNormal (.requireTrue hcode)
          (.consNormal hcall (.consNormal (.requireTrue hresult) .nil)))) .nil))

end Benchmarks.Safe

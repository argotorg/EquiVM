import Benchmarks.Morpho.MetaMorphoV1_1.GuardianRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.PackedDeletion

/-! Source executions of pending guardian and timelock revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def revocationSlot (guardian : Bool) : UInt256 := if guardian then ⟨15⟩ else ⟨17⟩
def revocationName (guardian : Bool) : Ident :=
  if guardian then "pendingGuardian" else "pendingTimelock"
def revocationEvent (guardian : Bool) : Ident :=
  if guardian then "RevokePendingGuardian" else "RevokePendingTimelock"

def revocationState (guardian : Bool) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (revocationSlot guardian) ⟨0⟩

def revocationFrame (evm : EVM.State) (locals imms : Store) : Frame :=
  { contract := contract
    locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert "__role" .unit
    immutables := imms }

def revocationBody (guardian : Bool) : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "__calldata" (some .bytes) (.env .msgData),
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))),
    .internalCall "_checkGuardianRole" [] "__role", .delete ⟨revocationName guardian, []⟩,
    .internalCall "_msgSender" [] "__c3", .emit (revocationEvent guardian) [.var "__c3"]]

theorem revocationPrefix (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : guardianRoleAllowed evm) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (revocationBody guardian) (revocationFrame evm locals imms)
      [.delete ⟨revocationName guardian, []⟩, .internalCall "_msgSender" [] "__c3",
        .emit (revocationEvent guardian) [.var "__c3"]] := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (guardianRoleCall evm _ imms "__role" hrole) htail

theorem revocationDelete (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? (revocationName guardian) = none) :
    deleteStorage? config (revocationFrame evm locals imms) evm
      ⟨revocationName guardian, []⟩ = .ok (revocationState guardian evm) := by
  cases guardian
  · exact deleteStorage_pendingTimelock evm _ imms (by
      simpa [revocationFrame, store_get_ne, revocationName] using hbase)
  · exact deleteStorage_pendingGuardian evm _ imms (by
      simpa [revocationFrame, store_get_ne, revocationName] using hbase)

theorem revocationBodyReturns (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : guardianRoleAllowed evm)
    (hbase : locals.get? (revocationName guardian) = none) :
    ∃ final, ExecTransitionBody config contract evm locals (revocationBody guardian)
      (.returned final (revocationState guardian evm) none) imms := by
  refine ⟨{
    contract := contract
    locals := (revocationFrame evm locals imms).locals.insert "__c3"
      (.address (revocationState guardian evm).executionEnv.source)
    immutables := imms }, ExecFuncBody.execBlockOK ?_⟩
  apply (revocationPrefix guardian evm locals imms hwv hhi hrole).run
  refine ExecBlock.consNormal (ExecStmt.delete
    (revocationDelete guardian evm locals imms hbase)) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address (revocationState guardian evm).executionEnv.source)
      (by rfl) (by simp only [evalExpr?, envValue, pure])) ?_
  apply (ABlock.start.emitStep
    (vals := [.address (revocationState guardian evm).executionEnv.source]) ?_).run
  · exact ExecBlock.nil
  · simp [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind, pure]

theorem revocationBodyStatic (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : guardianRoleAllowed evm)
    (hbase : locals.get? (revocationName guardian) = none)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals (revocationBody guardian)
      .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (revocationPrefix guardian evm locals imms hwv hhi hrole).run
  exact ExecBlock.consStatic
    (ExecStmt.deleteStatic (revocationDelete guardian evm locals imms hbase) hperm)

theorem revocationBodyRevertsRole (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : ¬ guardianRoleAllowed evm) :
    ExecTransitionBody config contract evm locals (revocationBody guardian) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert (guardianRoleCallReverts evm _ imms "__role" hrole)

end Benchmarks.Morpho.MetaMorphoV1_1

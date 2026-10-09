import Benchmarks.Morpho.MorphoBlue.BodyCommon
import Benchmarks.Morpho.MorphoBlue.Storage
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue

def addressAdminBody (name arg event : Ident) : List Stmt :=
  calldataPrelude [
    .require (.binary .eq (.env .caller) (.storage ⟨"owner", []⟩)),
    .require (.binary .ne (.var arg) (.storage ⟨name, []⟩)),
    .assign .storage ⟨name, []⟩ (.var arg), .emit event [.var arg]]

def addressAdminFrame (v : MorphoImmutables) (locals : Store) (cd : ByteArray) : Frame :=
  { contract := contract, locals := locals.insert "__calldata" (.bytes cd), immutables := immStore v }

theorem addressAdminBodySplit (v : MorphoImmutables) (evm : EVM.State)
    (locals : Store) (name arg event : Ident) (slot value : UInt256)
    (hbaseOwner : (addressAdminFrame v locals evm.executionEnv.calldata).locals.get? "owner" = none)
    (hbaseName : (addressAdminFrame v locals evm.executionEnv.calldata).locals.get? name = none)
    (harg : (addressAdminFrame v locals evm.executionEnv.calldata).locals.get? arg =
      some (.address (AccountAddress.ofNat value.toNat)))
    (hty : storageTypeAt? contract.storage ⟨name, []⟩ = some (.elem .address))
    (hloc : Syntax.modelLayout ⟨name, []⟩ = some (.leaf (addressOffset0Loc slot)))
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : value.toNat < EVM.addressModulus)
    (ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv)
    (hne : value ≠ solcAddressSlotWord slot evm.accountMap evm.executionEnv) :
    ExecTransitionBody config contract evm locals (addressAdminBody name arg event)
      (.returned (addressAdminFrame v locals evm.executionEnv.calldata)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value))
        none) (immStore v) ∧
    (evm.executionEnv.perm = false →
      ExecTransitionBody config contract evm locals (addressAdminBody name arg event)
        .staticViolation (immStore v)) := by
  have hargEval (state : EVM.State) : evalExpr? config
      (addressAdminFrame v locals evm.executionEnv.calldata) state (.var arg) =
      .ok (.address (AccountAddress.ofNat value.toNat)) := by
    simp only [evalExpr?, harg, EvalResult.ofOption]
  have howner := evalMorphoOwnerCheck evm _ (immStore v) hbaseOwner
  have hnew := evalMorphoAddressNe evm _ (immStore v) name slot value (.var arg)
    hbaseName hty hloc (hargEval evm) hcanon
  have hprefix : ABlock config evm
      { contract := contract, locals := locals, immutables := immStore v }
      (addressAdminBody name arg event) (addressAdminFrame v locals evm.executionEnv.calldata)
      [.assign .storage ⟨name, []⟩ (.var arg), .emit event [.var arg]] :=
    ((calldataPrelude_ok hcv hsize).requireStep
      (by simpa only [ho, decide_true] using howner)).requireStep
      (by simpa only [ne_eq, hne, not_false_eq_true, decide_true] using hnew)
  have hassign := assignMorphoAddress evm _ (immStore v) name slot value hbaseName hty hloc hcanon
  constructor
  · apply ExecFuncBody.execBlockOK
    apply hprefix.run
    apply ExecBlock.consNormal (ExecStmt.assign (hargEval evm) hassign)
    apply ExecBlock.consNormal (ExecStmt.emit (evalExprs?_singleton (hargEval _)))
    exact ExecBlock.nil
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (hprefix.run (ExecBlock.consStatic (ExecStmt.assignStatic (hargEval evm) hassign hperm)))

theorem addressAdminBodyRejects (v : MorphoImmutables) (evm : EVM.State)
    (locals : Store) (name arg event : Ident) (slot value : UInt256)
    (hbaseOwner : (addressAdminFrame v locals evm.executionEnv.calldata).locals.get? "owner" = none)
    (hbaseName : (addressAdminFrame v locals evm.executionEnv.calldata).locals.get? name = none)
    (harg : (addressAdminFrame v locals evm.executionEnv.calldata).locals.get? arg =
      some (.address (AccountAddress.ofNat value.toNat)))
    (hty : storageTypeAt? contract.storage ⟨name, []⟩ = some (.elem .address))
    (hloc : Syntax.modelLayout ⟨name, []⟩ = some (.leaf (addressOffset0Loc slot)))
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : value.toNat < EVM.addressModulus)
    (hbad : solcSourceWord evm.executionEnv ≠ solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv ∨
      value = solcAddressSlotWord slot evm.accountMap evm.executionEnv) :
    ExecTransitionBody config contract evm locals (addressAdminBody name arg event)
      .reverted (immStore v) := by
  have howner := evalMorphoOwnerCheck evm _ (immStore v) hbaseOwner
  apply ExecFuncBody.execBlockRevert
  by_cases ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv
  · have heq := hbad.resolve_left (not_not.mpr ho)
    have hnew := evalMorphoAddressNe evm _ (immStore v) name slot value (.var arg)
      hbaseName hty hloc (by simp only [evalExpr?, harg, EvalResult.ofOption]) hcanon
    exact ((calldataPrelude_ok hcv hsize).requireStep
      (by simpa only [ho, decide_true] using howner)).requireRevert
      (by simpa only [heq, ne_eq, not_true_eq_false, decide_false] using hnew)
  · exact (calldataPrelude_ok hcv hsize).requireRevert
      (by simpa only [ho, decide_false] using howner)

end Benchmarks.Morpho.MorphoBlue

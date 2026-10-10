import Benchmarks.Morpho.MetaMorphoV1_1.SetCapStorage

/-! The zero-cap and already-enabled source paths do not call balance readers. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

theorem setCapZeroSource (evm : State) (imms : Store) (p : MarketParamsData)
    (id ptr : UInt256) :
    ∃ final, ExecFuncBody config (setCapFrame imms p id ⟨0⟩ ptr) evm
      allocatedSetCapFunction.body
      (.returned final (setCapFinalState evm id ⟨0⟩) (some [uint256Value ptr])) := by
  have hr := setCapFrame_ready imms p id ⟨0⟩ ptr
  obtain ⟨final, htail⟩ := setCapTailReturns (evm := evm) hr
  refine ⟨final, ExecFuncBody.execBlockRet ?_⟩
  apply (setCapAliasPrefix evm imms p id ⟨0⟩ ptr).run
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) htail
  simpa only [ne_eq, not_true_eq_false, decide_false] using setCapConditionSource hr.cap

theorem setCapZeroStatic (evm : State) (imms : Store) (p : MarketParamsData)
    (id ptr : UInt256) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (setCapFrame imms p id ⟨0⟩ ptr) evm allocatedSetCapFunction.body
      .staticViolation := by
  have hr := setCapFrame_ready imms p id ⟨0⟩ ptr
  apply ExecFuncBody.execBlockStatic
  apply (setCapAliasPrefix evm imms p id ⟨0⟩ ptr).run
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
    (setCapTailStatic hr hperm)
  simpa only [ne_eq, not_true_eq_false, decide_false] using setCapConditionSource hr.cap

theorem setCapExistingSource (evm : State) (imms : Store) (p : MarketParamsData)
    (id cap ptr : UInt256) (hcap : cap ≠ ⟨0⟩)
    (henabled : marketRemovalEnabledWord evm id ≠ ⟨0⟩) :
    ∃ final, ExecFuncBody config (setCapFrame imms p id cap ptr) evm
      allocatedSetCapFunction.body
      (.returned final (setCapFinalState (setCapClearTimeState evm id) id cap)
        (some [uint256Value ptr])) := by
  have hr := setCapFrame_ready imms p id cap ptr
  obtain ⟨final, htail⟩ := setCapTailReturns (evm := setCapClearTimeState evm id) hr
  refine ⟨final, ExecFuncBody.execBlockRet ?_⟩
  apply (setCapAliasPrefix evm imms p id cap ptr).run
  apply ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) htail
  · simpa only [ne_eq, hcap, not_false_eq_true, decide_true] using setCapConditionSource hr.cap
  · apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
      (ExecBlock.consNormal (setCapClearTimeAssign hr.reference) ExecBlock.nil)
    simpa only [henabled, decide_false] using setCapDisabledSource (evm := evm) hr.reference

theorem setCapExistingStatic (evm : State) (imms : Store) (p : MarketParamsData)
    (id cap ptr : UInt256) (hcap : cap ≠ ⟨0⟩)
    (henabled : marketRemovalEnabledWord evm id ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (setCapFrame imms p id cap ptr) evm allocatedSetCapFunction.body
      .staticViolation := by
  have hr := setCapFrame_ready imms p id cap ptr
  apply ExecFuncBody.execBlockStatic
  apply (setCapAliasPrefix evm imms p id cap ptr).run
  apply ExecBlock.consStatic (ExecStmt.iteTrue ?_ ?_)
  · simpa only [ne_eq, hcap, not_false_eq_true, decide_true] using setCapConditionSource hr.cap
  · apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
      (ExecBlock.consStatic (execStmt_assign_static (setCapClearTimeAssign hr.reference) hperm))
    simpa only [henabled, decide_false] using setCapDisabledSource (evm := evm) hr.reference

end Benchmarks.Morpho.MetaMorphoV1_1

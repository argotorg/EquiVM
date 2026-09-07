import Examples.UniswapV2Pair.ConstructorDomainSource
import Examples.UniswapV2Pair.Bytes32WordSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

noncomputable def constructorDomainState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (constructorDomainHashWord (UInt256.ofNat evm.executionEnv.codeOwner.val))

def constructorFactoryState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
      (uniswapSourceWord evm.executionEnv))

theorem constructorAssignDomain (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage
      domainSeparatorRef (permitWordBytes32Value
        (constructorDomainHashWord (UInt256.ofNat evm.executionEnv.codeOwner.val))) =
      .ok ({ contract := contract, locals := ∅ }, constructorDomainState evm) := by
  apply assignStorageRef_storage_scalar_value (ty := bytes32St)
    (er := { base := "DOMAIN_SEPARATOR", steps := [] }) (loc := bytes32Loc ⟨3⟩)
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
  · simp only [evalStorageRef, evalStorageRefSteps, domainSeparatorRef, EvalResult.bind, bind, pure]
  · native_decide
  · rfl
  · trivial
  · exact storageLocStore_bytes32 evm _ _ _ (valueToWord_bytes32_word _)

theorem constructorAssignFactory (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage
      factoryRef (.address evm.executionEnv.source) =
      .ok ({ contract := contract, locals := ∅ }, constructorFactoryState evm) := by
  apply assignStorageRef_storage_scalar_value (ty := addrSt)
    (er := { base := "factory", steps := [] }) (loc := addrLoc ⟨5⟩)
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
  · simp only [evalStorageRef, evalStorageRefSteps, factoryRef, EvalResult.bind, bind, pure]
  · native_decide
  · rfl
  · trivial
  · rw [← uniswapSource_ofNat evm.executionEnv]
    exact uniswapStorageLocStore_address_offset0 evm _ _ (uniswapSourceWord_canonical _)

theorem uniswapConstructorSourceReturns (evm : EVM.State) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ constructorDecl.body
      (.returned { contract := contract, locals := ∅ }
        (constructorFactoryState (constructorDomainState (uniswapLockExitedState evm))) none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure])
    (uniswapAssignUnlockedOne evm ∅
      (by simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simpa only [uniswapLockExitedState, uniswapUnlockedState, storageStore_executionEnv]
      using hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_constructor_domain _) (constructorAssignDomain _)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp only [sender, evalExpr?, envValue, pure])
      (constructorAssignFactory _)) ExecBlock.nil

theorem uniswapConstructorSourceReverts (evm : EVM.State) (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ constructorDecl.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure])
    (uniswapAssignUnlockedOne evm ∅
      (by simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false
    (by simpa only [uniswapLockExitedState, uniswapUnlockedState, storageStore_executionEnv]
      using hwv)))

end UniswapV2Pair

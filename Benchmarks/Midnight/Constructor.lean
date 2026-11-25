import Benchmarks.Midnight.Common
import Benchmarks.Midnight.CreationBlocks_001

variable {fork : Ethereum.Fork}

/-!
# Midnight constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Stele constructor body, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 1000

def constructorState (evm : EVM.State) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
    (setAddressOffset0Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩)
      (solcSourceWord evm.executionEnv))

theorem constructorAssignConfigurator (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage
      { base := "configurator" } (.address evm.executionEnv.source) =
      .ok ({ contract := contract, locals := ∅ }, constructorState evm) := by
  apply assignStorageRef_storage_scalar_value (hbackend := rfl)
    (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem .address)
    (er := { base := "configurator" }) (loc := addressOffset0Loc ⟨9⟩)
  · simp
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · have h := storageLocStore_address_offset0 evm ⟨9⟩ (solcSourceWord evm.executionEnv)
      (solcSourceWord_canonical _)
    rw [solcSource_ofNat] at h
    exact h

theorem constructorBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm ∅ contract.ctor.body
      (.returned { contract := contract, locals := ∅ } (constructorState evm) none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm)
    (by simp only [evalExpr?, envValue, pure]) (constructorAssignConfigurator evm)) ?_
  exact ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address (constructorState evm).executionEnv.source])
    (by simpa only [constructorState, storageStore_executionEnv] using hperm)
    (by simp only [evalExprs?, evalExpr?, envValue, pure, bind, EvalResult.bind])) ExecBlock.nil

theorem constructorReturnBytes :
    ByteArray.readWithPadding
      ((midnightCreationBytecode ++ ByteArray.empty).write 83 solcFreePtrMem 128 24557)
      128 24557 = midnightBytecode := by
  native_decide

theorem constructorTrace {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = midnightCreationBytecode)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) :
    RDret fork midnightCreationBytecode g (initState σ σ₀ g A I)
      (constructorState (initState σ σ₀ g A I)).accountMap midnightBytecode := by
  have hc : I.code = midnightCreationBytecode ++ ByteArray.empty := by simpa using hcode
  have rd := RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hc
  have rd1 := midnightCreationBlocks.midnightCreation_block_0_fallthrough (by simp) hwv rd
  have hr := midnightCreationBlocks.midnightCreation_block_10 (by simp) hperm rd1
  have hword : UInt256.lor (solcSourceWord I)
      (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWordAt ⟨9⟩ σ I)) =
      setAddressOffset0Word (solcSlotWordAt ⟨9⟩ σ I) (solcSourceWord I) := by
    rw [setAddressOffset0Word, solcAddrMask_clean (solcSourceWord_canonical I),
      u256_land_comm, u256_lor_comm]
  change RDret fork _ _ _
    (sstoreAccountMap I.codeOwner σ ⟨9⟩ (UInt256.lor (solcSourceWord I)
      (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWordAt ⟨9⟩ σ I))))
    (ByteArray.readWithPadding
      ((midnightCreationBytecode ++ ByteArray.empty).write 83 solcFreePtrMem 128 24557)
      128 24557) at hr
  rw [constructorReturnBytes, hword, ByteArray.append_empty] at hr
  simpa only [constructorState, storageStore_accountMap, initState] using hr

theorem constructorTraceRevert {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = midnightCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev fork midnightCreationBytecode g (initState σ σ₀ g A I) := by
  have hc : I.code = midnightCreationBytecode ++ ByteArray.empty := by simpa using hcode
  have rd := RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hc
  have rd1 := midnightCreationBlocks.midnightCreation_block_0_taken
    (by simp) hwv (by native_decide) rd
  have hr := midnightCreationBlocks.midnightCreation_block_78 (by simp
    [midnightCreationBlocks.midnightCreation_block_0_taken_stack]) rd1
  simpa only [ByteArray.append_empty] using hr

theorem midnightConstructorCorrect :
    typedConstructorRefinement config midnightCreationBytecode contract (fun _ => midnightBytecode) := by
  intro fork _hfork σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  have hlen := emptyCtorDeployment_args_length (cfg := config) (contract := contract)
    rfl rfl hdeploy
  have hdeployed := emptyCtorDeployment_eq_initcode (cfg := config) (contract := contract)
    rfl rfl hdeploy
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hlen
  subst args
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hr := constructorTrace (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hwv hperm
    exact hr.constructorRefinementEmptyParams hcode rfl (constructorBodyReturns _ hwv hperm) rfl
  · have hr := constructorTraceRevert (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hwv
    exact hr.constructorRefinementEmptyParams hcode rfl (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight

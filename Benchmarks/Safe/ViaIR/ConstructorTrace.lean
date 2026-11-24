import Benchmarks.Safe.ViaIR.Common
import Benchmarks.Safe.ViaIR.Blocks.Creation
import Reasoning.Constructor

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.CreationBlocks

namespace Benchmarks.Safe.ViaIR

theorem safeConstructorSource (evm : EVM.State) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm ∅ contract.ctor.body
      (.returned { contract := contract, locals := ∅ }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ ⟨1⟩) none) := by
  apply ExecFuncBody.execBlockOK
  refine .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.assign (hperm := Or.inr hperm) (by simp [evalExpr?, pure]; rfl)
      ?_) .nil)
  apply assignStorageRef_storage_scalar_value (er := { base := "threshold" })
    (loc := uint256Loc ⟨4⟩)
  · simp
  · simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm ⟨4⟩ ⟨1⟩

theorem safeConstructorSourceRevert (evm : EVM.State)
    (hv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody fork config contract evm ∅ contract.ctor.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (evalCallvalueEq_false hv)))

theorem safeCreationRuntime :
    ((safeCreationBytecode.write 31 solcFreePtrMem 128 11003).readWithPadding 128 11003) =
      safeBytecode := by native_decide

set_option maxRecDepth 100000 in
theorem safeConstructorTrace {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeCreationBytecode) (hv : I.weiValue = ⟨0⟩) (hp : I.perm = true) :
    RDret fork safeCreationBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨1⟩) safeBytecode := by
  have h₀ : RD fork (safeCreationBytecode ++ ByteArray.empty) I g (initState σ σ₀ g A I)
      ⟨0⟩ [] ByteArray.empty ⟨0⟩ ByteArray.empty σ 0 0 := by
    simpa only [ByteArray.append_empty] using RD.initState (σ := σ) (σ₀ := σ₀)
      (g := g) (A := A) hcode
  have h₁ := safeCreation_block_0_fallthrough (by simp) hv h₀
  have h₂ := safeCreation_block_10 (by simp) hp h₁
  simp only [ByteArray.append_empty] at h₂
  change RDret fork safeCreationBytecode g (initState σ σ₀ g A I)
    (sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨1⟩)
    ((safeCreationBytecode.write 31 solcFreePtrMem 128 11003).readWithPadding 128 11003) at h₂
  rw [safeCreationRuntime] at h₂
  exact h₂

set_option maxRecDepth 100000 in
theorem safeConstructorTraceRevert {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeCreationBytecode) (hv : I.weiValue ≠ ⟨0⟩) :
    RDrev fork safeCreationBytecode g (initState σ σ₀ g A I) := by
  have h₀ : RD fork (safeCreationBytecode ++ ByteArray.empty) I g (initState σ σ₀ g A I)
      ⟨0⟩ [] ByteArray.empty ⟨0⟩ ByteArray.empty σ 0 0 := by
    simpa only [ByteArray.append_empty] using RD.initState (σ := σ) (σ₀ := σ₀)
      (g := g) (A := A) hcode
  have h₁ := safeCreation_block_0_taken (by simp) hv (by jump_dest) h₀
  have h₂ := safeCreation_block_26 (by simp [safeCreation_block_0_taken_stack]) h₁
  simpa only [ByteArray.append_empty] using h₂

end Benchmarks.Safe.ViaIR

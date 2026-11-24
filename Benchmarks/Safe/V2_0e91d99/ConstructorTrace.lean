import Benchmarks.Safe.V2_0e91d99.SetupOwnersFinish
import Benchmarks.Safe.V2_0e91d99.Blocks.Creation
import Reasoning.Constructor

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V2_0e91d99.CreationBlocks

namespace Benchmarks.Safe.V2_0e91d99

theorem safeConstructorSource (evm : EVM.State) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm ∅ contract.ctor.body
      (.returned { contract := contract, locals := ∅ }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ ⟨1⟩) none) := by
  apply ExecFuncBody.execBlockOK
  exact .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.assign (hperm := Or.inr hperm) (by simp [evalExpr?, pure]; rfl)
      (safeAssignThresholdLocals evm ∅ ⟨1⟩ (by simp))) .nil)

theorem safeConstructorSourceRevert (evm : EVM.State)
    (hv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody fork config contract evm ∅ contract.ctor.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (evalCallvalueEq_false hv)))

theorem safeCreationRuntime :
    ((safeCreationBytecode.write 33 solcFreePtrMem 0 11749).readWithPadding 0 11749) =
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
  have h₁ := safeCreation_block_0_taken (by simp) (by rw [hv]; decide) (by jump_dest) h₀
  have h₂ := safeCreation_block_14 (by simp) hp h₁
  simp only [ByteArray.append_empty] at h₂
  change RDret fork safeCreationBytecode g (initState σ σ₀ g A I)
    (sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨1⟩)
    ((safeCreationBytecode.write 33 solcFreePtrMem 0 11749).readWithPadding 0 11749) at h₂
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
  have h₁ := safeCreation_block_0_fallthrough (by simp) (isZero_eq_zero_of_ne hv) h₀
  have h₂ := safeCreation_block_11 (by simp [safeCreation_block_0_fallthrough_stack]) h₁
  simpa only [ByteArray.append_empty] using h₂

end Benchmarks.Safe.V2_0e91d99

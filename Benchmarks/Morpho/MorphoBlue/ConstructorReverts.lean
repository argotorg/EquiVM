import Benchmarks.Morpho.MorphoBlue.ConstructorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoConstructorValueReverts {σ σ₀ A I} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = morphoCreationBytecode ++ tail) (hcv : I.weiValue ≠ ⟨0⟩) :
    RDrev (morphoCreationBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  have rd1 := morphoCreationBlocks.morphoCreation_block_0_taken (by simp) hcv (by jump_dest) rd0
  exact morphoCreationBlocks.morphoCreation_block_426
    (by simp [morphoCreationBlocks.morphoCreation_block_0_taken_stack]) rd1

theorem morphoConstructorZeroOwnerReverts {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (h : RD (morphoCreationBytecode ++ tail) I g s0 (UInt256.ofNat 114) (constructorOwnerStack ⟨0⟩)
      (constructorDecodedMem ⟨0⟩) aw rdata σ k C) :
    RDrev (morphoCreationBytecode ++ tail) g s0 := by
  have rd1 := morphoCreationBlocks.morphoCreation_block_114_taken
    (by simp) (by decide) (by jump_dest) h
  have rd2 := morphoCreationBlocks.morphoCreation_block_335 (by simp) rd1
  have rd3 := morphoCreationBlocks.morphoCreation_block_368_taken (by simp)
    (by native_decide) (by jump_dest) rd2
  have rd4 := morphoCreationBlocks.morphoCreation_block_402 (by simp) (by jump_dest) rd3
  have rd5 := morphoCreationBlocks.morphoCreation_block_368_fallthrough (by simp) (by native_decide) rd4
  exact morphoCreationBlocks.morphoCreation_block_377 (by simp) rd5

end Benchmarks.Morpho.MorphoBlue

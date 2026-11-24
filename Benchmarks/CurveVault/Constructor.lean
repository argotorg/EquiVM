import Benchmarks.CurveVault.Common
import Benchmarks.CurveVault.CreationBlocks_001

variable {fork : Ethereum.Fork}

/-!
# Vault constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Stele constructor body, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CurveVault

theorem vaultConstructorCorrect :
    typedConstructorRefinement config vaultCreationBytecode contract (fun _ => vaultBytecode) := by
  apply emptyConstructorCorrect_of_RDret rfl rfl rfl
  intro fork σ σ₀ A I g hcode
  have hinit := RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  have hinit' : RD fork (vaultCreationBytecode ++ ByteArray.empty) I g
      (initState σ σ₀ g A I) (UInt256.ofNat 0) [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty σ 0 0 := by
    simpa only [ByteArray.append_empty] using hinit
  have hret := vaultCreationBlocks.vaultCreation_block_0 (by simp) hinit'
  simp only [ByteArray.append_empty] at hret
  have houtput : (vaultCreationBytecode.write (UInt256.ofNat 17).toNat ByteArray.empty
      (UInt256.ofNat 0).toNat (UInt256.ofNat 8635).toNat).readWithPadding
      (UInt256.ofNat 0).toNat (UInt256.ofNat 8635).toNat = vaultBytecode := by native_decide
  rwa [houtput] at hret

end Benchmarks.CurveVault

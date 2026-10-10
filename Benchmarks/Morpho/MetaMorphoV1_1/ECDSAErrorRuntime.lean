import Benchmarks.Morpho.MetaMorphoV1_1.ECDSAErrorSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_087

/-! The shared enum check and the reachable ECDSA error-handler paths. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem ecdsaEnumCheck {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {error ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024) (herror : error.toNat < 4)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19213⟩ (error :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C' := by
  have r1 := metaMorphoV1_1_block_19213_fallthrough (immWords := wordsOf (immStore v))
    (by simpa only [List.length_cons] using hstack)
    (by rw [ugt_one herror]; rfl) rd
  exact RD.pack (metaMorphoV1_1_block_19222 (immWords := wordsOf (immStore v))
    (by omega) hret r1)

theorem ecdsaThrowStart {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {error : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024) (herror : error.toNat < 4)
    (rd : RD (deployedRuntime v) I g s0 ⟨19243⟩ (error :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨19252⟩ (error :: R) mem aw rdata σ k' C' := by
  have r1 := metaMorphoV1_1_block_19243 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact ecdsaEnumCheck v (by simpa only [List.length_cons] using hstack) herror
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1

theorem ecdsaThrowReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {errorArg ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19243⟩ (⟨0⟩ :: errorArg :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, r1⟩ := ecdsaThrowStart v
    (by simpa only [List.length_cons] using hstack) (by decide) rd
  have r2 := metaMorphoV1_1_block_19252_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rfl r1
  exact RD.pack (metaMorphoV1_1_block_19258 (immWords := wordsOf (immStore v))
    (by omega) hret r2)

theorem ecdsaThrowNonzero {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {error : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (herror : error.toNat < 4) (hne : error ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨19243⟩ (error :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨19270⟩ (error :: R) mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, r1⟩ := ecdsaThrowStart v hstack herror rd
  have r2 := metaMorphoV1_1_block_19252_taken (immWords := wordsOf (immStore v))
    (by omega) hne (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := metaMorphoV1_1_block_19261 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  exact ecdsaEnumCheck v (by simpa only [List.length_cons] using hstack) herror
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3

theorem ecdsaThrowOneReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨19243⟩ (⟨1⟩ :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, r1⟩ := ecdsaThrowNonzero v hstack (by decide) (by decide) rd
  have r2 := metaMorphoV1_1_block_19270_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by decide) r1
  exact metaMorphoV1_1_block_19279 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r2

theorem ecdsaThrowThreeReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {errorArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨19243⟩ (⟨3⟩ :: errorArg :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, r1⟩ := ecdsaThrowNonzero v
    (by simp only [List.length_cons]; omega) (by decide) (by decide) rd
  have r2 := metaMorphoV1_1_block_19270_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := metaMorphoV1_1_block_19293 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨k4, C4, r4⟩ := ecdsaEnumCheck v
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
  have r5 := metaMorphoV1_1_block_19302_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r4
  have r6 := metaMorphoV1_1_block_19329 (immWords := wordsOf (immStore v))
    (by simpa only [List.length_cons] using hstack)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r5
  obtain ⟨k7, C7, r7⟩ := ecdsaEnumCheck v
    (by simpa only [List.length_cons] using hstack) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r6
  have r8 := metaMorphoV1_1_block_19341_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r7
  exact metaMorphoV1_1_block_19349 (immWords := wordsOf (immStore v))
    (by omega) r8

end Benchmarks.Morpho.MetaMorphoV1_1

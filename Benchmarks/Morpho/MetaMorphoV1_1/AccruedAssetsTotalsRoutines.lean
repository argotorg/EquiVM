import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsTotals

/-! Bytecode routines for the accrued-assets loss adjustment and interest calculation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem accruedLossChoiceRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {last lost real ret fee : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hl : lost.toNat ≤ last.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12315⟩
      ([UInt256.sub last lost, lost, ret, real, last, fee] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12077⟩
      ([real, accruedNewLost last lost real, ⟨12346⟩, ⟨12353⟩, ret,
        accruedNewLost last lost real, last, fee] ++ R) mem aw' rdata σ k' C' := by
  by_cases hr : real.toNat < (UInt256.sub last lost).toNat
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12315_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) (by rw [ult_one hr]; rfl) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12323_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    obtain ⟨k3, C3, h3⟩ := checkedSubReturn v
      (by simp only [List.append, List.length_cons]; omega) (accruedLossSubFits hl hr)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_12339_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    exact ⟨aw4, k4, C4, by simpa only [accruedNewLost, if_pos hr] using h4⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12315_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [ult_zero (Nat.le_of_not_gt hr)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12433_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact ⟨aw2, k2, C2, by simpa only [accruedNewLost, if_neg hr] using h2⟩

theorem accruedTotalsReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {morpho len i real ret fee : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hfit : accruedTotalsFit (codeOwnerStorageWord I σ ⟨22⟩)
      (codeOwnerStorageWord I σ ⟨23⟩) real)
    (rd : RD (deployedRuntime v) I g s0 ⟨12296⟩
      ([morpho, len, i, real, ret, fee] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12353⟩
      ([accruedInterest (codeOwnerStorageWord I σ ⟨22⟩) (codeOwnerStorageWord I σ ⟨23⟩) real,
        ret, accruedNewLost (codeOwnerStorageWord I σ ⟨22⟩) (codeOwnerStorageWord I σ ⟨23⟩) real,
        accruedNewTotal (codeOwnerStorageWord I σ ⟨22⟩) (codeOwnerStorageWord I σ ⟨23⟩) real,
        fee] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12296_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := checkedSubReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit.1
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := accruedLossChoiceRoutine v hstack hfit.1 h2
  obtain ⟨k4, C4, h4⟩ := checkedAddReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit.2
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
  obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_12346_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
  obtain ⟨k6, C6, h6⟩ := checkedSubReturn v
    (by simp only [List.append, List.length_cons]; omega) (accruedTotal_ge_last hfit)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h5
  exact ⟨aw5, k6, C6, h6⟩

theorem accruedTotalsRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {morpho len i real ret fee : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hbad : ¬ accruedTotalsFit (codeOwnerStorageWord I σ ⟨22⟩)
      (codeOwnerStorageWord I σ ⟨23⟩) real)
    (rd : RD (deployedRuntime v) I g s0 ⟨12296⟩
      ([morpho, len, i, real, ret, fee] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12296_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hl : (codeOwnerStorageWord I σ ⟨23⟩).toNat ≤ (codeOwnerStorageWord I σ ⟨22⟩).toNat
  · obtain ⟨k2, C2, h2⟩ := checkedSubReturn v
      (by simp only [List.append, List.length_cons]; omega) hl
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := accruedLossChoiceRoutine v hstack hl h2
    exact checkedAddRevert v (by simp only [List.append, List.length_cons]; omega)
      (Nat.le_of_not_gt (fun h ↦ hbad ⟨hl, h⟩)) h3
  · exact checkedSubRevert v (by simp only [List.append, List.length_cons]; omega)
      (Nat.lt_of_not_ge hl) h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

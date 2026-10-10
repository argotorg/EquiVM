import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.FullMulDivWad
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_012

/-! Runtime fee calculation after the nonzero-interest and nonzero-fee guard. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem accruedFeeAmountPrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {interest ret lost total shares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hf : fullMulDivFits interest (accruedFeeWord I σ) ⟨1000000000000000000⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨12369⟩
      ([interest, ret, lost, total, shares] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12234⟩
      ([total, accruedFeeAssets interest (accruedFeeWord I σ), ⟨1572⟩,
        codeOwnerStorageWord I σ ⟨2⟩, accruedFeeAssets interest (accruedFeeWord I σ),
        ⟨12410⟩, lost, total, ret] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12369_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD _ _ _ _ _
    ([interest, accruedFeeWord I σ, ⟨12397⟩, ⟨12410⟩, lost, total, ret] ++ R)
      _ _ _ _ _ _ at h1
  obtain ⟨aw2, k2, C2, h2⟩ := fullMulDivWadReturn v
    (by simp only [List.append, List.length_cons]; omega) hf
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  exact metaMorphoV1_1_block_12397_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem accruedFeeConversionPrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {feeAssets supply total ret lost : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hf : feeAssets.toNat ≤ total.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12234⟩
      ([total, feeAssets, ⟨1572⟩, supply, feeAssets, ⟨12410⟩, lost, total, ret] ++ R)
        mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14489⟩
      ([feeAssets, supply, UInt256.sub total feeAssets, ⟨12410⟩, lost, total, ret] ++ R)
        mem aw' rdata σ k' C' := by
  obtain ⟨k1, C1, h1⟩ := checkedSubReturn v
    (by simp only [List.append, List.length_cons]; omega) hf
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  exact metaMorphoV1_1_block_1572_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem accruedFeeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {interest ret lost total shares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 21 ≤ 1024)
    (hfit : accruedFeeFits v.DECIMALS_OFFSET interest (accruedFeeWord I σ)
      (codeOwnerStorageWord I σ ⟨2⟩) total)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12369⟩
      ([interest, ret, lost, total, shares] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      ([lost, total, accruedFeeShares v.DECIMALS_OFFSET interest (accruedFeeWord I σ)
        (codeOwnerStorageWord I σ ⟨2⟩) total] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := accruedFeeAmountPrefix v (by omega) hfit.1 rd
  obtain ⟨aw2, k2, C2, h2⟩ := accruedFeeConversionPrefix v (by omega) hfit.2.1 h1
  obtain ⟨aw3, k3, C3, h3⟩ := convertSharesReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit.2.2
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
  exact metaMorphoV1_1_block_12410_packed (immWords := wordsOf (immStore v))
    (by change R.length + 4 ≤ 1024; omega) hret h3

theorem accruedFeeRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {interest ret lost total shares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 21 ≤ 1024)
    (hbad : ¬ accruedFeeFits v.DECIMALS_OFFSET interest (accruedFeeWord I σ)
      (codeOwnerStorageWord I σ ⟨2⟩) total)
    (rd : RD (deployedRuntime v) I g s0 ⟨12369⟩
      ([interest, ret, lost, total, shares] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hm : fullMulDivFits interest (accruedFeeWord I σ) ⟨1000000000000000000⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := accruedFeeAmountPrefix v (by omega) hm rd
    by_cases hf : (accruedFeeAssets interest (accruedFeeWord I σ)).toNat ≤ total.toNat
    · obtain ⟨aw2, k2, C2, h2⟩ := accruedFeeConversionPrefix v (by omega) hf h1
      exact convertSharesRevert v (by simp only [List.append, List.length_cons]; omega)
        (fun hc ↦ hbad ⟨hm, hf, hc⟩) h2
    · exact checkedSubRevert v (by simp only [List.append, List.length_cons]; omega)
        (Nat.lt_of_not_ge hf) h1
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12369_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    change RD _ _ _ _ _
      ([interest, accruedFeeWord I σ, ⟨12397⟩, ⟨12410⟩, lost, total, ret] ++ R)
        _ _ _ _ _ _ at h1
    exact fullMulDivWadRevert v (by simp only [List.append, List.length_cons]; omega) hm h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

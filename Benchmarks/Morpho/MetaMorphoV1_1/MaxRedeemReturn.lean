import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositEntry
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesRoutines

/-! Conversion and return of the redemption limit. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem maxRedeemEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total supply assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 19 ≤ 1024)
    (hfit : convertSharesFits v.DECIMALS_OFFSET assets supply total)
    (rd : RD (deployedRuntime v) I g s0 ⟨1572⟩
      ([total, supply, assets, ⟨1578⟩, ⟨32⟩] ++ R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (convertSharesWord v.DECIMALS_OFFSET assets supply total).toByteArray := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_1572_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := convertSharesReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  exact maxDepositEncodeReturn v (by simp only [List.append]; omega) h2

theorem maxRedeemConversionRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total supply assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 19 ≤ 1024)
    (hbad : ¬ convertSharesFits v.DECIMALS_OFFSET assets supply total)
    (rd : RD (deployedRuntime v) I g s0 ⟨1572⟩
      ([total, supply, assets, ⟨1578⟩, ⟨32⟩] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_1572_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact convertSharesRevert v
    (by simp only [List.append, List.length_cons]; omega) hbad h1

end Benchmarks.Morpho.MetaMorphoV1_1

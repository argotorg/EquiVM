import Benchmarks.Morpho.MetaMorphoV1_1.ECDSATryRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ECDSAErrorRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! Resume the public recovery wrapper after its try-recover helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem ecdsaRecoverReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {signer errorArg ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨1831⟩ (errorArg :: ⟨0⟩ :: signer :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (signer :: R) mem aw out σ k' C' := by
  have r1 := metaMorphoV1_1_block_1831 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact ecdsaThrowReturn v (by simpa only [List.length_cons] using hstack) hret r1

theorem ecdsaRecoverErrorReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {signer error errorArg ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (herror : error = ⟨1⟩ ∨ error = ⟨3⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1831⟩ (errorArg :: error :: signer :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_1831 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases herror with rfl | rfl
  · exact ecdsaThrowOneReverts v (by simp only [List.length_cons]; omega) r1
  · exact ecdsaThrowThreeReverts v (by simpa only [List.length_cons] using hstack) r1

end Benchmarks.Morpho.MetaMorphoV1_1

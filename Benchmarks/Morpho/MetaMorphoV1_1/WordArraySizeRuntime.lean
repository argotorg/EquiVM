import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_060
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.EAS.Attester.WordHelpers

/-! The shared checked size calculation for one-word memory arrays. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem wordArraySizeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {count ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcount : count.toNat ≤ solcMaxU64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12021⟩ (count :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (UInt256.ofNat (32 + 32 * count.toNat) :: R) mem aw out σ k' C' := by
  have r1 := metaMorphoV1_1_block_12021_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (ugt_zero hcount) rd
  have r2 := metaMorphoV1_1_block_12036 (immWords := wordsOf (immStore v))
    (by omega) hret r1
  have hmul : 32 * count.toNat < UInt256.size := by
    change count.toNat ≤ 18446744073709551615 at hcount
    change _ < 2 ^ 256
    omega
  have he : UInt256.shiftLeft count ⟨5⟩ = UInt256.ofNat (32 * count.toNat) := by
    simpa only [u256_ofNat_toNat] using shiftLeft5_ofNat_eq hmul
  have he' : UInt256.shiftLeft count (UInt256.ofNat 5) =
      UInt256.ofNat (32 * count.toNat) := he
  simpa only [metaMorphoV1_1_block_12036_stack, he', ofNat_add_words] using
    (show ∃ k' C', RD (deployedRuntime v) I g s0 ret _ mem aw out σ k' C' from
      ⟨_, _, r2⟩)

theorem wordArraySizeRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {count : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hcount : solcMaxU64 < count.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12021⟩ (count :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_12021_taken (immWords := wordsOf (immStore v))
    hstack (by
      rw [ugt_one (by change solcMaxU64 < count.toNat; exact hcount)]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2690 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r1

end Benchmarks.Morpho.MetaMorphoV1_1

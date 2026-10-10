import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueLoop

/-! The public queue-length guard and initialization of the validation loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem supplyQueueLengthGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C n : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hfit : n < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨10046⟩ (UInt256.ofNat n :: R)
      mem aw out σ k C) :
    (¬ n ≤ 30 ∧ RDrev (deployedRuntime v) g s0) ∨
    (n ≤ 30 ∧ ∃ k' C', RD (deployedRuntime v) I g s0 ⟨10055⟩
      (⟨0⟩ :: UInt256.ofNat n :: R) mem aw out σ k' C') := by
  by_cases hlen : n ≤ 30
  · have h1 := metaMorphoV1_1_block_10046_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by
        apply ugt_zero
        change (UInt256.ofNat n).toNat ≤ 30
        rw [ulit_toNat' n hfit]; exact hlen) rd
    exact .inr ⟨hlen, _, _, metaMorphoV1_1_block_10054
      (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) h1⟩
  · have h1 := metaMorphoV1_1_block_10046_taken
      (immWords := wordsOf (immStore v)) hstack (by
        have hgt : (UInt256.ofNat 30).toNat < (UInt256.ofNat n).toNat := by
          rw [ulit_toNat' n hfit]; change 30 < n; omega
        rw [ugt_one hgt]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨hlen, metaMorphoV1_1_block_10384 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1

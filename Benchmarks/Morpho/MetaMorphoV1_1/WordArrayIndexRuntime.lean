import Benchmarks.Morpho.MetaMorphoV1_1.ArrayRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_060
import Benchmarks.EAS.Attester.WordHelpers

/-! Shared array indexing routines used by the queue-update loops. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem memoryWordArrayIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr i ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hi : i.toNat < (memLoad ptr mem).toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12057⟩
      (ptr :: i :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      ((UInt256.shiftLeft i ⟨5⟩ + ptr + ⟨32⟩) :: R) mem aw' out σ k' C' := by
  have r1 := metaMorphoV1_1_block_12057_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ult_one hi]; rfl) rd
  obtain ⟨k', C', r2⟩ := RD.pack (metaMorphoV1_1_block_12067
    (immWords := wordsOf (immStore v)) hstack hret r1)
  exact ⟨_, k', C', r2⟩

-- LIBRARY CANDIDATE: normalize an in-bounds word-array element address.
theorem memoryWordArrayIndex_address (ptr i : Nat) (hfit : 32 * i < UInt256.size) :
    UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ + UInt256.ofNat ptr + ⟨32⟩ =
      UInt256.ofNat (ptr + 32 + 32 * i) := by
  rw [shiftLeft5_ofNat_eq hfit]
  change UInt256.ofNat (32 * i) + UInt256.ofNat ptr + UInt256.ofNat 32 = _
  rw [ofNat_add_words, ofNat_add_words]
  congr 1
  omega

theorem withdrawQueueIndexRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hi : (codeOwnerStorageWord I σ ⟨21⟩).toNat ≤ i.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨11491⟩ (i :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k', C', r1⟩ := metaMorphoV1_1_block_11491_taken
    (immWords := wordsOf (immStore v)) hstack
    (by
      change UInt256.isZero (UInt256.lt i (codeOwnerStorageWord I σ ⟨21⟩)) ≠ ⟨0⟩
      rw [ult_zero hi]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_11515 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r1

end Benchmarks.Morpho.MetaMorphoV1_1

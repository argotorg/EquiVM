import Benchmarks.Morpho.MetaMorphoV1_1.Uint128AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.Uint128Add
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_077

/-! The shared allocating cast and addition to an existing uint128 market field. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def castAddFits (ptr value old : UInt256) : Prop :=
  allocationFits ptr ⟨64⟩ ∧ value.toNat < 2 ^ 128 ∧ old.toNat + value.toNat < 2 ^ 128

instance (ptr value old : UInt256) : Decidable (castAddFits ptr value old) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxRecDepth 2000 in
theorem castAddFieldRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr field value old ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 15 ≤ 1024)
    (hlo : 96 ≤ field.toNat) (hsep : field.toNat + 32 ≤ ptr.toNat)
    (hmem : field.toNat + 32 ≤ mem.size) (hold : old.toNat < 2 ^ 128)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hload : memLoad field mem = old)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19367⟩
      (value :: ⟨17353⟩ :: ret :: uint128Mask :: field :: R) mem aw rdata σ k C) :
    (¬ castAddFits ptr value old ∧ RDrev (deployedRuntime v) g s0) ∨
    (castAddFits ptr value old ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret ((old + value) :: uint128Mask :: field :: R)
        (uint128CastMemory mem ptr) aw' rdata σ k' C') := by
  by_cases halloc : allocationFits ptr ⟨64⟩
  · by_cases hfit : value.toNat < 2 ^ 128
    · obtain ⟨aw1, k1, C1, h1⟩ := uint128CastReturn v
        (by simp only [List.length_cons]; omega) hfree halloc hfit
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
      have hread : memLoad field (uint128CastMemory mem ptr) = old := by
        have he := (uint128CastMemory_prefix mem ptr).load_preserved hlo hsep hmem
          field.val.isLt
        simpa only [u256_ofNat_toNat, hload] using he
      have hmask := u256LandMaskCleanOfToNat old uint128Mask (by decide +kernel) hold
      have h2 := metaMorphoV1_1_block_17353 (immWords := wordsOf (immStore v))
        (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      simp only [metaMorphoV1_1_block_17353_stack, hread, hmask] at h2
      by_cases hsum : old.toNat + value.toNat < 2 ^ 128
      · obtain ⟨k3, C3, h3⟩ := uint128AddReturn v
          (by simp only [List.length_cons]; omega) hold hfit hsum hret h2
        exact .inr ⟨⟨halloc, hfit, hsum⟩, _, k3, C3, h3⟩
      · exact .inl ⟨fun h ↦ hsum h.2.2, uint128AddRevert v
          (by simp only [List.length_cons]; omega) hold hfit (Nat.le_of_not_lt hsum) h2⟩
    · exact .inl ⟨fun h ↦ hfit h.2.1, uint128CastRevert v
        (by simp only [List.length_cons]; omega) hfree (.inr (Nat.le_of_not_lt hfit)) rd⟩
  · exact .inl ⟨fun h ↦ halloc h.1, uint128CastRevert v
      (by simp only [List.length_cons]; omega) hfree (.inl halloc) rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

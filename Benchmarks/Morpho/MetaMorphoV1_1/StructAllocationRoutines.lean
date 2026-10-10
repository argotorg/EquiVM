import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotAllocation

/-! The compiler's fixed-size allocator used for market-parameter structs. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

-- LIBRARY CANDIDATE: splitting two fixed, already-aligned reservations.
theorem allocationFits_aligned_split (ptr : UInt256) (a b : Nat)
    (hab : a + b < 2 ^ 64)
    (ha : roundedSize (UInt256.ofNat a) = UInt256.ofNat a)
    (hb : roundedSize (UInt256.ofNat b) = UInt256.ofNat b)
    (hsum : roundedSize (UInt256.ofNat (a + b)) = UInt256.ofNat (a + b)) :
    allocationFits ptr (UInt256.ofNat (a + b)) ↔
      allocationFits ptr (UInt256.ofNat a) ∧
        allocationFits (nextCursor ptr (UInt256.ofNat a)) (UInt256.ofNat b) := by
  have haFit : a < UInt256.size := by change _ < 2 ^ 256; omega
  have hbFit : b < UInt256.size := by change _ < 2 ^ 256; omega
  have habFit : a + b < UInt256.size := lt_trans hab (by decide)
  simp only [allocationFits_aligned _ _ hsum, allocationFits_aligned _ _ ha,
    allocationFits_aligned _ _ hb, UInt256.toNat_ofNat_of_lt haFit,
    UInt256.toNat_ofNat_of_lt hbFit, UInt256.toNat_ofNat_of_lt habFit, nextCursor, ha]
  constructor
  · intro h
    have hp : (ptr + UInt256.ofNat a).toNat = ptr.toNat + a :=
      uadd_word_ofNat_toNat ptr a (lt_trans (by omega : ptr.toNat + a < 2 ^ 64) (by decide))
    rw [hp]
    omega
  · rintro ⟨hfirst, hsecond⟩
    have hp : (ptr + UInt256.ofNat a).toNat = ptr.toNat + a :=
      uadd_word_ofNat_toNat ptr a (lt_trans hfirst (by decide))
    rw [hp] at hsecond
    omega

theorem allocationFits_160_twice (ptr : UInt256) :
    allocationFits ptr ⟨320⟩ ↔
      allocationFits ptr ⟨160⟩ ∧ allocationFits (nextCursor ptr ⟨160⟩) ⟨160⟩ :=
  allocationFits_aligned_split ptr 160 160 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 2000 in
theorem allocateStruct160Return {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hfit : allocationFits ptr ⟨160⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11275⟩ (ptr :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (nextCursor ptr ⟨160⟩)) aw' rdata σ k' C' := by
  have hnext := metaMorphoV1_1_block_11275_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    ((allocationGuard_eq_zero_iff ptr ⟨160⟩).mpr hfit) rd
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1_block_11298_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hnext
  exact ⟨aw', k', C', hdone⟩

set_option maxRecDepth 2000 in
theorem allocateStruct160Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hfit : ¬ allocationFits ptr ⟨160⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨11275⟩ (ptr :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hpanic := metaMorphoV1_1_block_11275_taken
    (immWords := wordsOf (immStore v)) hstack
    (fun hguard ↦ hfit ((allocationGuard_eq_zero_iff ptr ⟨160⟩).mp hguard))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2690 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_11275_taken_stack, List.length_cons]; omega) hpanic

theorem allocationFits_192_twice (ptr : UInt256) :
    allocationFits ptr ⟨384⟩ ↔
      allocationFits ptr ⟨192⟩ ∧ allocationFits (nextCursor ptr ⟨192⟩) ⟨192⟩ :=
  allocationFits_aligned_split ptr 192 192 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 2000 in
theorem allocateStruct192Return {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hfit : allocationFits ptr ⟨192⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11302⟩ (ptr :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (nextCursor ptr ⟨192⟩)) aw' rdata σ k' C' := by
  have hnext := metaMorphoV1_1_block_11302_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    ((allocationGuard_eq_zero_iff ptr ⟨192⟩).mpr hfit) rd
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1_block_11325_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hnext
  exact ⟨aw', k', C', hdone⟩

set_option maxRecDepth 2000 in
theorem allocateStruct192Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hfit : ¬ allocationFits ptr ⟨192⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨11302⟩ (ptr :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hpanic := metaMorphoV1_1_block_11302_taken
    (immWords := wordsOf (immStore v)) hstack
    (fun hguard ↦ hfit ((allocationGuard_eq_zero_iff ptr ⟨192⟩).mp hguard))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2690 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_11302_taken_stack, List.length_cons]; omega) hpanic

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

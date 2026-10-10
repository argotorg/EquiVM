import Benchmarks.Morpho.MetaMorphoV1_1.Eip712EncodeRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_027

/-! Allocation of the empty extensions array and initialization of the return header. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000
set_option autoImplicit false

def eip712ExtensionsMemory (mem : ByteArray) (ptr : Nat) : ByteArray :=
  writeWord (writeWord mem 64 (UInt256.ofNat (ptr + 32))) ptr ⟨0⟩

theorem eip712ExtensionsMemory_prefix (mem : ByteArray) (ptr : Nat) :
    MemoryPrefix mem (eip712ExtensionsMemory mem ptr) ptr :=
  (memoryPrefix_sparse_writeWord mem 64 ptr _ (.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ ptr ptr _ (.inl (le_refl _)))

theorem eip712ExtensionsMemory_size (mem : ByteArray) (ptr : Nat) :
    ptr + 32 ≤ (eip712ExtensionsMemory mem ptr).size := by
  rw [eip712ExtensionsMemory, writeWord_sparse_size]
  exact Nat.le_max_right _ _

theorem eip712ExtensionsMemory_length (mem : ByteArray) (ptr : Nat) (hptr : ptr < UInt256.size) :
    memLoad (UInt256.ofNat ptr) (eip712ExtensionsMemory mem ptr) = ⟨0⟩ :=
  memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt hptr)

theorem eip712ExtensionsMemory_free (mem : ByteArray) (ptr : Nat) (hlo : 96 ≤ ptr) :
    memLoad (UInt256.ofNat 64) (eip712ExtensionsMemory mem ptr) = UInt256.ofNat (ptr + 32) := by
  unfold eip712ExtensionsMemory Reasoning.Theory.writeWord
  rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size]; change 96 ≤ _; omega)
    (.inl (by exact hlo))]
  exact memLoad_write_same _ _ _ _ rfl

theorem eip712ReachExtensionsAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {namePtr versionPtr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (ptr : Nat) (hstack : R.length + 10 ≤ 1024)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (rd : RD (deployedRuntime v) I g s0 ⟨5049⟩
      (versionPtr :: namePtr :: ⟨5104⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11329⟩
      (UInt256.ofNat ptr :: ⟨32⟩ :: ⟨5068⟩ :: versionPtr :: ⟨5118⟩ :: ⟨32⟩ ::
        UInt256.ofNat ptr :: namePtr :: ⟨5104⟩ :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_5049_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨aw', k', C', by simpa only [metaMorphoV1_1_block_5049_stack, hptr] using h⟩

theorem eip712ExtensionsReachEncoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {namePtr versionPtr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (ptr : Nat) (hstack : R.length + 12 ≤ 1024)
    (hlo : 96 ≤ ptr) (hfit : ptr + 32 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨11329⟩
      (UInt256.ofNat ptr :: ⟨32⟩ :: ⟨5068⟩ :: versionPtr :: ⟨5118⟩ :: ⟨32⟩ ::
        UInt256.ofNat ptr :: namePtr :: ⟨5104⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11086⟩
      (namePtr :: UInt256.ofNat (ptr + 32 + 224) :: ⟨5104⟩ :: versionPtr :: ⟨5118⟩ :: ⟨32⟩ ::
        UInt256.ofNat ptr :: UInt256.ofNat (ptr + 32) :: UInt256.ofNat (ptr + 32) :: R)
      (eip712StartMemory (eip712ExtensionsMemory mem ptr) (ptr + 32)) aw' rdata σ k' C' := by
  have hf : ptr + 32 + 64 < UInt256.size := by change _ < 2 ^ 256; omega
  have hp := UInt256.toNat_ofNat_of_lt (show ptr < UInt256.size by omega)
  have hn : nextCursor (UInt256.ofNat ptr) ⟨32⟩ = UInt256.ofNat (ptr + 32) := ofNat_add_words _ _
  have ha : allocationFits (UInt256.ofNat ptr) ⟨32⟩ := by
    rw [allocationFits_iff_sum_lt, hp]
    exact hfit
  obtain ⟨aw1, k1, C1, h1⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) ha
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  rw [hn] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_5068_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  have hfree := eip712ExtensionsMemory_free mem ptr hlo
  simp only [eip712ExtensionsMemory, Reasoning.Theory.writeWord] at hfree
  refine ⟨aw2, k2, C2, ?_⟩
  simp only [metaMorphoV1_1_block_5068_stack, metaMorphoV1_1_block_5068_memory,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_write_len_zero, hp,
    Reasoning.Theory.writeWord] at h2
  rw [hfree] at h2
  simp only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl, ofNat_add_words] at h2
  simp only [UInt256.toNat_ofNat_of_lt (show ptr + 32 < UInt256.size by omega),
    UInt256.toNat_ofNat_of_lt (show ptr + 32 + 32 < UInt256.size by omega)] at h2
  exact h2

end Benchmarks.Morpho.MetaMorphoV1_1

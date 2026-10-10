import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_057
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_058

/-! Allocation and copying in the shared dynamic calldata decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def calldataBytesMemory (mem cd : ByteArray) (ptr start len : UInt256) : ByteArray :=
  writeWord
    (cd.write start.toNat
      (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len)
      (ptr + ⟨32⟩).toNat len.toNat)
    ((ptr + len) + ⟨32⟩).toNat ⟨0⟩

theorem calldataBytesLengthRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {start len total ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 10 ≤ 1024) (hlen : 2 ^ 64 ≤ len.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨11644⟩ (start :: len :: total :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_11644 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_11617_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [ugt_one (by change 2 ^ 64 - 1 < len.toNat; omega)]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_2690 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) h2

theorem calldataBytesAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr start len total ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 11 ≤ 1024) (hlen : len.toNat < 2 ^ 64)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (deployedRuntime v) I g s0 ⟨11644⟩ (start :: len :: total :: ret :: R)
      mem aw out σ k C) :
    (¬ allocationFits ptr (UInt256.ofNat (32 + len.toNat)) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (allocationFits ptr (UInt256.ofNat (32 + len.toNat)) ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨11670⟩ (len :: start :: ptr :: ret :: total :: R)
        (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) aw' out σ k' C') := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have h1 := metaMorphoV1_1_block_11644 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_11617_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (ugt_zero (by change len.toNat ≤ 2 ^ 64 - 1; omega)) h1
  have h3 := metaMorphoV1_1_block_11632 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  have hw := callReturnSizeWord len.toNat hlen
  rw [u256_ofNat_toNat] at hw
  simp only [metaMorphoV1_1_block_11632_stack, hw] at h3
  have h4 := metaMorphoV1_1_block_11656 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  simp only [metaMorphoV1_1_block_11656_stack, hfree] at h4
  by_cases hf : allocationFits ptr (UInt256.ofNat (32 + len.toNat))
  · obtain ⟨aw5, k5, C5, h5⟩ := allocateRoundedReturn v
      (by simp only [List.length_cons]; omega)
      ((allocationFits_bytesAlloc ptr len.toNat hlen).mpr hf)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
    rw [nextCursor_bytesAllocSize ptr len.toNat hlen] at h5
    exact .inr ⟨hf, aw5, k5, C5, h5⟩
  · exact .inl ⟨hf, allocateRoundedRevert v
      (by simp only [List.length_cons]; omega)
      (fun h ↦ hf ((allocationFits_bytesAlloc ptr len.toNat hlen).mp h)) h4⟩

theorem calldataBytesCopyReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr start len total ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 10 ≤ 1024) (hpayload : (start + len).toNat ≤ total.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11670⟩ (len :: start :: ptr :: ret :: total :: R)
      (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (ptr :: R)
      (calldataBytesMemory mem I.calldata ptr start len) aw' out σ k' C' := by
  have h1 := metaMorphoV1_1_block_11670_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero hpayload) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11684_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hret h1
  exact ⟨aw2, k2, C2, h2⟩

theorem calldataBytesCopyRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr start len total ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 8 ≤ 1024) (hpayload : total.toNat < (start + len).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨11670⟩ (len :: start :: ptr :: ret :: total :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_11670_taken (immWords := wordsOf (immStore v))
    (by omega) (by rw [ugt_one hpayload]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_11670_taken_stack, List.length_cons]; omega) h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

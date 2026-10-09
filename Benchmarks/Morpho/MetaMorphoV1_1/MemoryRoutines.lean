import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_056
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_060
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_075

/-! Shared memory allocation and array-index routines in the deployed bytecode. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

-- LIBRARY CANDIDATE: the allocator's upper-bound and wrapping checks pass below 2^64.
theorem allocationGuard (ptr size : UInt256)
    (hfit : ptr.toNat + size.toNat < 2 ^ 64) :
    UInt256.lor
      (UInt256.gt (ptr + size) (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩))
      (UInt256.lt (ptr + size) ptr) = ⟨0⟩ := by
  have hword : (ptr + size).toNat = ptr.toNat + size.toNat :=
    addWord_toNat ptr size (lt_trans hfit (by decide))
  rw [ugt_zero (by rw [hword]; change ptr.toNat + size.toNat ≤ 2 ^ 64 - 1; omega),
    ult_zero (by rw [hword]; omega)]
  rfl

set_option maxRecDepth 2000 in
theorem allocateReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr size ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hround : UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩) = size)
    (hfit : ptr.toNat + size.toNat < 2 ^ 64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11329⟩ (ptr :: size :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (ptr + size)) aw' rdata σ k' C' := by
  have hguard := allocationGuard ptr size hfit
  have hnext := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11329_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by
      change UInt256.lor
        (UInt256.gt (ptr + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩))
          (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩))
        (UInt256.lt (ptr + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩)) ptr) = ⟨0⟩
      rwa [hround]) rd
  change RD _ _ _ _ _
    ((ptr + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩)) :: ret :: R)
    _ _ _ _ _ _ at hnext
  rw [hround] at hnext
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11358_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hnext
  exact ⟨aw', k', C', hdone⟩

set_option maxRecDepth 2000 in
theorem firstArrayElementReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hlen : memLoad ptr mem ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12044⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret ((ptr + ⟨32⟩) :: R)
      mem aw' rdata σ k' C' := by
  have hindex := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12044_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (isZero_eq_zero_of_ne hlen) rd
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12052_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hindex
  change RD _ _ _ _ _ ((⟨32⟩ + ptr) :: R) _ _ _ _ _ _ at hdone
  rw [u256_add_comm ⟨32⟩ ptr] at hdone
  exact ⟨aw', k', C', hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1

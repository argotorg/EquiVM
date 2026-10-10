import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocation
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_039

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem wordBytesCallTailAllocationTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr src len ret selector : UInt256}
    {words : List UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hf : ptr.toNat+99+32*words.length+len.toNat < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14575⟩
      (UInt256.ofNat (ptr.toNat+68+32*words.length+paddedSize len.toNat) :: ptr :: ret :: ptr :: R)
      (wordBytesCallMemory I.calldata mem src.toNat (ptr.toNat+32) selector words len) aw rdata σ k C) :
    (¬AllocationBounds ptr (wordBytesCallAllocationSize words len) ∧
      ∃ aw' k' C', C+92+Cₘ aw' ≤ C'+Cₘ aw ∧
        RD (deployedRuntime v) I g s0 ⟨7857⟩
          (allocationEnd ptr (wordBytesCallAllocationSize words len) :: ret :: ptr :: R)
          (wordBytesCallObjectMemory I.calldata mem src.toNat ptr selector words len) aw' rdata σ k' C') ∨
    (AllocationBounds ptr (wordBytesCallAllocationSize words len) ∧
      ∃ aw' k' C', C+106+Cₘ aw' ≤ C'+Cₘ aw ∧
        RD (deployedRuntime v) I g s0 ret (ptr :: R)
          (wordBytesCallAllocatedMemory I.calldata mem src.toNat ptr selector words len) aw' rdata σ k' C') := by
  obtain ⟨hsub, hheader⟩ := wordBytesCallAllocation_arith ptr len words hf
  have hm : poolManager_block_14575_memory
      (mem := wordBytesCallMemory I.calldata mem src.toNat (ptr.toNat+32) selector words len)
      (x0 := UInt256.ofNat (ptr.toNat+68+32*words.length+paddedSize len.toNat)) (x1 := ptr) (x3 := ptr) =
      wordBytesCallObjectMemory I.calldata mem src.toNat ptr selector words len := by
    simp only [poolManager_block_14575_memory, hsub, hheader]
    rfl
  have rd := poolManager_block_14575 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManager_block_14575_stack, hsub, hm] at rd
  rcases allocateCheckedTrace v (by simp only [List.length_cons]; omega) hret rd with
    ⟨hbad, hr⟩ | ⟨hgood, hr⟩
  · refine .inl ⟨hbad, _, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega
  · refine .inr ⟨hgood, _, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega

end Benchmarks.UniswapV4PoolManager

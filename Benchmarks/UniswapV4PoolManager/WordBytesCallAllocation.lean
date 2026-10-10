import Benchmarks.UniswapV4PoolManager.WordBytesCallMemory
import Benchmarks.UniswapV4PoolManager.AllocationCostTrace
import Benchmarks.UniswapV4PoolManager.TickLogCompiled
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: reserve a bytes header together with an encoded ABI call.
def wordBytesCallAllocationSize (words : List UInt256) (len : UInt256) : UInt256 :=
  UInt256.ofNat (68+32*words.length+paddedSize len.toNat)

def wordBytesCallAllocatedMemory (src mem : ByteArray) (srcOff : Nat) (ptr selector : UInt256)
    (words : List UInt256) (len : UInt256) : ByteArray :=
  writeWord (wordBytesCallObjectMemory src mem srcOff ptr selector words len) 64
    (allocationEnd ptr (wordBytesCallAllocationSize words len))

theorem wordBytesCallAllocation_end_toNat (ptr len : UInt256) (words : List UInt256)
    (hf : ptr.toNat+130+32*words.length+len.toNat < UInt256.size) :
    (allocationEnd ptr (wordBytesCallAllocationSize words len)).toNat =
      ptr.toNat+96+32*words.length+paddedSize len.toNat := by
  have hp := paddedSize_le_add31 len.toNat
  have hs : (wordBytesCallAllocationSize words len).toNat = 68+32*words.length+paddedSize len.toNat :=
    UInt256.toNat_ofNat_of_lt (by omega)
  rw [allocationEnd_toNat _ _ (by rw [hs]; omega), hs]
  have hr : paddedSize (68+32*words.length+paddedSize len.toNat) =
      96+32*words.length+paddedSize len.toNat := by
    unfold paddedSize
    omega
  rw [hr]; omega

theorem wordBytesCallAllocation_arith (ptr len : UInt256) (words : List UInt256)
    (hf : ptr.toNat+99+32*words.length+len.toNat < UInt256.size) :
    UInt256.sub (UInt256.ofNat (ptr.toNat+68+32*words.length+paddedSize len.toNat)) ptr =
      wordBytesCallAllocationSize words len ∧
    wordBytesCallAllocationSize words len+
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      UInt256.ofNat (36+32*words.length+paddedSize len.toNat) := by
  have hp := paddedSize_le_add31 len.toNat
  constructor
  · apply u256_inj
    rw [usub_ofNat_word_toNat (by omega) (by omega), wordBytesCallAllocationSize,
      UInt256.toNat_ofNat_of_lt (by omega)]
    omega
  · change wordBytesCallAllocationSize words len+UInt256.sub ⟨0⟩ (UInt256.ofNat 32) = _
    rw [wordAddNegSub, wordBytesCallAllocationSize]
    apply u256_inj
    rw [usub_ofNat_lit_toNat (by omega) (by omega), UInt256.toNat_ofNat_of_lt (by omega)]
    omega

theorem wordBytesCallAllocationTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr src len ret selector arg : UInt256}
    {words : List UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024)
    (hf : ptr.toNat+99+32*words.length+len.toNat < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨7990⟩
      (UInt256.ofNat (ptr.toNat+68+32*words.length+paddedSize len.toNat) :: ptr :: ret :: arg :: ptr :: R)
      (wordBytesCallMemory I.calldata mem src.toNat (ptr.toNat+32) selector words len) aw rdata σ k C) :
    (¬AllocationBounds ptr (wordBytesCallAllocationSize words len) ∧
      ∃ aw' k' C', C+92+Cₘ aw' ≤ C'+Cₘ aw ∧
        RD (deployedRuntime v) I g s0 ⟨7857⟩
          (allocationEnd ptr (wordBytesCallAllocationSize words len) :: ret :: arg :: ptr :: R)
          (wordBytesCallObjectMemory I.calldata mem src.toNat ptr selector words len) aw' rdata σ k' C') ∨
    (AllocationBounds ptr (wordBytesCallAllocationSize words len) ∧
      ∃ aw' k' C', C+106+Cₘ aw' ≤ C'+Cₘ aw ∧
        RD (deployedRuntime v) I g s0 ret (arg :: ptr :: R)
          (wordBytesCallAllocatedMemory I.calldata mem src.toNat ptr selector words len) aw' rdata σ k' C') := by
  obtain ⟨hsub, hheader⟩ := wordBytesCallAllocation_arith ptr len words hf
  have hm : poolManager_block_7990_memory
      (mem := wordBytesCallMemory I.calldata mem src.toNat (ptr.toNat+32) selector words len)
      (x0 := UInt256.ofNat (ptr.toNat+68+32*words.length+paddedSize len.toNat)) (x1 := ptr) (x4 := ptr) =
      wordBytesCallObjectMemory I.calldata mem src.toNat ptr selector words len := by
    simp only [poolManager_block_7990_memory, hsub, hheader]
    rfl
  have rd := poolManager_block_7990 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManager_block_7990_stack, hsub, hm] at rd
  rcases allocateCheckedTrace v (by simp only [List.length_cons]; omega) hret rd with
    ⟨hbad, hr⟩ | ⟨hgood, hr⟩
  · refine .inl ⟨hbad, _, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega
  · refine .inr ⟨hgood, _, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega

end Benchmarks.UniswapV4PoolManager

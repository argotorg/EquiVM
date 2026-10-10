import Benchmarks.UniswapV4PoolManager.BytesObjectMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 4000

theorem bytesObjectCopyTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw src ptr len saved : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hsrc : src.toNat+32 < UInt256.size) (hfit : ptr.toNat+len.toNat+64 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9389⟩ (src :: len :: ptr :: saved :: R)
      (writeWord mem ptr.toNat len) aw rdata σ k C) :
    ∃ aw' k' C', C+58+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨9049⟩ (saved :: ptr :: saved :: R)
        (bytesObjectMemory mem (src.toNat+32) ptr len) aw' rdata σ k' C' := by
  have hs : (src+UInt256.ofNat 32).toNat = src.toNat+32 := uadd_word_ofNat_toNat src 32 hsrc
  have hp : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hl : (ptr+len).toNat = ptr.toNat+len.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]
  have he : ((ptr+len)+UInt256.ofNat 32).toNat = ptr.toNat+32+len.toNat := by
    rw [uadd_word_ofNat_toNat _ 32 (by rw [hl]; omega), hl]
    omega
  have hm : poolManager_block_9389_memory (mem := writeWord mem ptr.toNat len)
      (x0 := src) (x1 := len) (x2 := ptr) = bytesObjectMemory mem (src.toNat+32) ptr len := by
    unfold poolManager_block_9389_memory
    rw [hs, hp, he]
    rfl
  have rd := poolManager_block_9389 hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  rw [hm] at rd
  refine ⟨_, _, _, ?_, rd⟩
  dsimp only [mcopyExpansionCost, memExpansionCost]
  omega

end Benchmarks.UniswapV4PoolManager

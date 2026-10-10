import Benchmarks.UniswapV4PoolManager.BytesReturnDecode
import Benchmarks.UniswapV4PoolManager.CopiedReturnMemory
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 4000

/-- Header checks performed before allocating the decoded bytes object. -/
def BytesReturnHeadBounds (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ (calldataWord out 0).toNat ≤ solcMaxU64 ∧
  (calldataWord out 0).toNat+32 ≤ out.size ∧
  (calldataWord out (calldataWord out 0).toNat).toNat ≤ solcMaxU64

theorem bytesReturnHeadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr next : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hout : out.size < 2^138) (hptr : ptr.toNat ≤ solcMaxU64)
    (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat ≤ mem.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9259⟩ (UInt256.ofNat out.size :: ptr :: R)
      (copiedReturnMemory out mem ptr.toNat next) aw out σ k C) :
    (¬BytesReturnBounds out ∧ RDrev (deployedRuntime v) g s0) ∨
    (BytesReturnHeadBounds out ∧ ∃ aw' k' C', C+134+Cₘ aw' ≤ C'+Cₘ aw ∧ aw.toNat ≤ aw'.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨9321⟩
        ((ptr+calldataWord out 0) :: calldataWord out (calldataWord out 0).toNat ::
          (ptr+UInt256.ofNat out.size) :: R)
        (copiedReturnMemory out mem ptr.toNat next) aw' out σ k' C') := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hm : 96 ≤ mem.size := by omega
  have hp64 : ptr.toNat ≤ 2^64-1 := hptr
  have ho255 : out.size < 2^255 := lt_trans hout (by decide)
  by_cases hs : 32 ≤ out.size
  swap
  · have rd := poolManager_block_9259_taken (by omega)
      (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) (by omega)]; decide) hj h
    exact .inl ⟨fun hb => hs hb.1, emptyRevert v
      (by simp only [poolManager_block_9259_taken_stack, List.length_cons]; omega) rd⟩
  have rd1 := poolManager_block_9259_fallthrough (by omega)
    (by rw [word_add_sub_left]; exact slt_ofNat_lit_zero (by decide) hs ho255) h
  dsimp only [poolManager_block_9259_fallthrough_stack] at rd1
  let off := calldataWord out 0
  have hload : memLoad ptr (copiedReturnMemory out mem ptr.toNat next) = off :=
    copiedReturnMemory_load out mem ptr.toNat 0 next ptr hm hmem hlo (by omega) (by omega)
  by_cases hoff : off.toNat ≤ solcMaxU64
  swap
  · have rd := poolManager_block_9273_taken (by simp only [List.length_cons]; omega)
      (by rw [hload]
          change UInt256.gt off (UInt256.ofNat solcMaxU64) ≠ ⟨0⟩
          rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < off.toNat from Nat.lt_of_not_ge hoff)]; decide)
      hj rd1
    exact .inl ⟨fun hb => hoff hb.2.2.1, emptyRevert v
      (by simp only [poolManager_block_9273_taken_stack, List.length_cons]; omega) rd⟩
  have rd2 := poolManager_block_9273_fallthrough (by simp only [List.length_cons]; omega)
    (by rw [hload]; exact ugt_zero hoff) rd1
  dsimp only [poolManager_block_9273_fallthrough_stack] at rd2
  rw [hload] at rd2
  have ho64 : off.toNat ≤ 2^64-1 := hoff
  have hp : (ptr+off).toNat = ptr.toNat+off.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt]
    change ptr.toNat+off.toNat < 2^256
    omega
  have hp31 : (ptr+off+UInt256.ofNat 31).toNat = ptr.toNat+off.toNat+31 := by
    rw [uadd_word_ofNat_toNat _ 31 (by
      rw [hp]
      change _ < 2^256
      omega), hp]
  have he : (ptr+UInt256.ofNat out.size).toNat = ptr.toNat+out.size :=
    uadd_word_ofNat_toNat ptr out.size (by
      change _ < 2^256; omega)
  have he255 : (ptr+UInt256.ofNat out.size).toNat < 2^255 := by
    rw [he]; omega
  have heq : ptr+UInt256.ofNat out.size = UInt256.ofNat (ptr.toNat+out.size) := by
    rw [← he, u256_ofNat_toNat]
  by_cases hw : off.toNat+32 ≤ out.size
  swap
  · have hc : UInt256.slt (ptr+off+UInt256.ofNat 31) (ptr+UInt256.ofNat out.size) = ⟨0⟩ := by
      rw [heq]
      apply slt_lit_zero (by rwa [he] at he255)
      · rw [hp31]; omega
      · rw [hp31]; omega
    have rd := poolManager_block_9291_taken (by omega) (by rw [hc]; decide) hj rd2
    exact .inl ⟨fun hb => hw hb.2.2.2.1, emptyRevert v
      (by simp only [poolManager_block_9291_taken_stack, List.length_cons]; omega) rd⟩
  have hc : UInt256.slt (ptr+off+UInt256.ofNat 31) (ptr+UInt256.ofNat out.size) = ⟨1⟩ := by
    rw [heq]
    apply slt_lit_one_low (by rwa [he] at he255)
    rw [hp31]; omega
  have rd3 := poolManager_block_9291_fallthrough (by omega) (by rw [hc]; rfl) rd2
  dsimp only [poolManager_block_9291_fallthrough_stack] at rd3
  let len := calldataWord out off.toNat
  have hlen : memLoad (ptr+off) (copiedReturnMemory out mem ptr.toNat next) = len :=
    copiedReturnMemory_load out mem ptr.toNat off.toNat next (ptr+off) hm hmem hlo hw hp
  by_cases hn : len.toNat ≤ solcMaxU64
  swap
  · have rd := poolManager_block_9303_taken (by simp only [List.length_cons]; omega)
      (by rw [hlen]
          change UInt256.gt len (UInt256.ofNat solcMaxU64) ≠ ⟨0⟩
          rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < len.toNat from Nat.lt_of_not_ge hn)]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    exact .inl ⟨fun hb => hn hb.2.2.2.2.1, poolManager_block_7857
      (by simp only [poolManager_block_9303_taken_stack, List.length_cons]; omega) rd⟩
  have rd4 := poolManager_block_9303_fallthrough (by simp only [List.length_cons]; omega)
    (by rw [hlen]; exact ugt_zero hn) rd3
  dsimp only [poolManager_block_9303_fallthrough_stack] at rd4
  rw [hlen] at rd4
  refine .inr ⟨⟨hs, hoff, hw, hn⟩, _, _, _, ?_, ?_, rd4⟩
  · dsimp only [memExpansionCost]
    omega
  · exact (memoryWords_ge_active aw ptr ⟨32⟩).trans (memoryWords_ge_active _ _ _)

end Benchmarks.UniswapV4PoolManager

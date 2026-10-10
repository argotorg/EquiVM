import Benchmarks.UniswapV4PoolManager.BytesDecode
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

/-- The shared calldata bytes-slice decoder returns its length and payload offset. -/
theorem decodeBytesSlice {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw start ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size) (hstart : start.toNat+solcMaxU64+32 < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12109⟩
      (start :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    (¬BytesSliceBounds I.calldata start.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (BytesSliceBounds I.calldata start.toNat ∧ ∃ k' C', C+114 ≤ C' ∧ RD (deployedRuntime v) I g s0 ret
      (calldataWord I.calldata start.toNat :: (start+⟨32⟩) :: R) mem aw rdata σ k' C') := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have h31 : (start+UInt256.ofNat 31).toNat = start.toNat+31 := uadd_word_ofNat_toNat start 31
    (lt_trans (by omega : start.toNat+31 < 2^255) (by decide))
  have h31lo : (start+UInt256.ofNat 31).toNat < 2^255 := by rw [h31]; omega
  by_cases hh : I.calldata.size < 2^255
  swap
  · have hg := slt_zero_low_high h31lo (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega)
    have rd := poolManagerBlocks.poolManager_block_12109_taken (by omega)
      (by rw [hg]; decide) hj h
    exact .inl ⟨fun hb => hh hb.1, emptyRevert v
      (by simp only [poolManagerBlocks.poolManager_block_12109_taken_stack, List.length_cons]; omega) rd⟩
  by_cases hw : start.toNat+32 ≤ I.calldata.size
  swap
  · have hg := slt_lit_zero hh (by rw [h31]; omega) h31lo
    have rd := poolManagerBlocks.poolManager_block_12109_taken (by omega)
      (by rw [hg]; decide) hj h
    exact .inl ⟨fun hb => hw hb.2.1, emptyRevert v
      (by simp only [poolManagerBlocks.poolManager_block_12109_taken_stack, List.length_cons]; omega) rd⟩
  have hg := slt_lit_one_low hh (by rw [h31]; omega)
  have rd1 := poolManagerBlocks.poolManager_block_12109_fallthrough (by omega) (by rw [hg]; rfl) h
  change RD _ _ _ _ ⟨12122⟩ (ret :: UInt256.ofNat I.calldata.size :: start :: R) _ _ _ _ _ _ at rd1
  let len := calldataWord I.calldata start.toNat
  by_cases hn : len.toNat ≤ solcMaxU64
  swap
  · have rd := poolManagerBlocks.poolManager_block_12122_taken (by omega)
      (by change UInt256.gt len (UInt256.ofNat solcMaxU64) ≠ ⟨0⟩
          rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < len.toNat from Nat.lt_of_not_ge hn)]; decide) hj rd1
    exact .inl ⟨fun hb => hn hb.2.2.1, emptyRevert v
      (by simp only [poolManagerBlocks.poolManager_block_12122_taken_stack, List.length_cons]; omega) rd⟩
  have rd2 := poolManagerBlocks.poolManager_block_12122_fallthrough (by omega) (ugt_zero hn) rd1
  change RD _ _ _ _ ⟨12140⟩ (UInt256.ofNat I.calldata.size :: ret :: len :: start :: R) _ _ _ _ _ _ at rd2
  have hs : (start+len).toNat = start.toNat+len.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (lt_trans (by omega : start.toNat+len.toNat < 2^255) (by decide))]
  have he : ((start+len)+UInt256.ofNat 32).toNat = start.toNat+len.toNat+32 := by
    rw [uadd_word_ofNat_toNat _ 32 (by rw [hs]; exact lt_trans (by omega : start.toNat+len.toNat+32 < 2^255) (by decide)), hs]
  by_cases hp : start.toNat+32+len.toNat ≤ I.calldata.size
  swap
  · have rd := poolManagerBlocks.poolManager_block_12140_taken (by omega)
      (by rw [ugt_one (by rw [he, UInt256.toNat_ofNat_of_lt hsize]; omega)]; decide) hj rd2
    exact .inl ⟨fun hb => hp hb.2.2.2, emptyRevert v
      (by simp only [poolManagerBlocks.poolManager_block_12140_taken_stack, List.length_cons]; omega) rd⟩
  have rd3 := poolManagerBlocks.poolManager_block_12140_fallthrough (by omega)
    (ugt_zero (by rw [he, UInt256.toNat_ofNat_of_lt hsize]; omega)) rd2
  have rd4 := poolManagerBlocks.poolManager_block_12154 (by simp; omega) hret rd3
  exact .inr ⟨⟨hh, hw, hn, hp⟩, _, _, by omega, rd4⟩

end Benchmarks.UniswapV4PoolManager

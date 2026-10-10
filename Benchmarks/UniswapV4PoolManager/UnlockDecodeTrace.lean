import Benchmarks.UniswapV4PoolManager.BytesSliceTrace
import Benchmarks.UniswapV4PoolManager.WordArrayDecode
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_025

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

theorem unlockDecodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024)
    (hs : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨8816⟩ R mem aw rdata σ k C) :
    (¬BytesCalldataBounds I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (BytesCalldataBounds I.calldata ∧ ∃ k' C', C+197 ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨8889⟩
      (calldataWord I.calldata (4+(calldataWord I.calldata 4).toNat) ::
       (⟨4⟩+(calldataWord I.calldata 4)+⟨32⟩) :: R) mem aw rdata σ k' C') := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hshort : I.calldata.size < 36
  · have hc := viaIRStaticLenCheckShort (words := 1) hs hshort (by decide) hsize
    have rd := poolManagerBlocks.poolManager_block_8816_taken (by omega)
      (by change UInt256.slt (UInt256.ofNat I.calldata.size+UInt256.ofNat (UInt256.size-4))
            (UInt256.ofNat (32*1)) ≠ ⟨0⟩
          rw [hc]; decide) hj h
    exact .inl ⟨fun hb => (Nat.not_lt_of_ge hb.1) hshort, emptyRevert v (by omega) rd⟩
  by_cases hhuge : 2^255+4 ≤ I.calldata.size
  · have hc := viaIRStaticLenCheckHuge (words := 1) hhuge hsize (by decide)
    have rd := poolManagerBlocks.poolManager_block_8816_taken (by omega)
      (by change UInt256.slt (UInt256.ofNat I.calldata.size+UInt256.ofNat (UInt256.size-4))
            (UInt256.ofNat (32*1)) ≠ ⟨0⟩
          rw [hc]; decide) hj h
    exact .inl ⟨by intro hb; have := hb.2.1; omega, emptyRevert v (by omega) rd⟩
  have hc := viaIRStaticLenCheckOk (words := 1) (by omega) (by omega) hsize
  have rd0 := poolManagerBlocks.poolManager_block_8816_fallthrough (by omega) hc h
  let off := calldataWord I.calldata 4
  by_cases ho : off.toNat ≤ solcMaxU64
  swap
  · have rd := poolManagerBlocks.poolManager_block_8858_taken (by omega)
      (by change UInt256.gt off (UInt256.ofNat solcMaxU64) ≠ ⟨0⟩
          rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < off.toNat from Nat.lt_of_not_ge ho)]; decide) hj rd0
    exact .inl ⟨fun hb => ho hb.2.2.1, emptyRevert v
      (by simp only [poolManagerBlocks.poolManager_block_8858_taken_stack, List.length_cons]; omega) rd⟩
  have rd1 := poolManagerBlocks.poolManager_block_8858_fallthrough (ee := I) (by omega) (ugt_zero ho) rd0
  have rd2 := poolManagerBlocks.poolManager_block_8876 (ee := I) (x0 := off) (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  dsimp only [poolManagerBlocks.poolManager_block_8876_stack] at rd2
  have hoff : (UInt256.ofNat 4+off).toNat = 4+off.toNat := add4_word_toNat off ho
  rcases decodeBytesSlice (I := I) (start := UInt256.ofNat 4+off) v hstack hsize
      (by rw [hoff]; norm_num [solcMaxU64] at ho ⊢; omega)
      (by rw [deployedRuntime_jumps]; jump_dest) rd2 with ⟨hbad, hr⟩ | ⟨hb, k', C', hcost, hr⟩
  · refine .inl ⟨?_, hr⟩
    intro hb
    rw [hoff] at hbad
    apply hbad
    exact ⟨hb.2.1, hb.2.2.2⟩
  · rw [hoff] at hb
    refine .inr ⟨⟨by omega, hb.1, ho, hb.2⟩, k', C', by omega, ?_⟩
    rw [hoff] at hr
    exact hr

end Benchmarks.UniswapV4PoolManager

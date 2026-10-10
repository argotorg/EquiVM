import Benchmarks.UniswapV4PoolManager.PoolKeyDecodeBounds
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem initializeDecodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hlen : 196 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit)
    (hsize : I.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨4038⟩ R entryMemory aw rdata σ k C) :
    (¬(PoolKeyCanonical (poolKeyOfCalldata I.calldata) ∧
        (calldataWord I.calldata 164).toNat < 2^160) ∧ RDrev (deployedRuntime v) g s0) ∨
    (PoolKeyCanonical (poolKeyOfCalldata I.calldata) ∧
      (calldataWord I.calldata 164).toNat < 2^160 ∧ ∃ aw' k' C',
      aw'.toNat ≤ max aw.toNat 10 ∧ RD (deployedRuntime v) I g s0 ⟨4081⟩
        (calldataWord I.calldata 164 :: ⟨160⟩ :: calldataWord I.calldata 164 :: R)
        (poolKeyMemory (poolKeyOfCalldata I.calldata)) aw' rdata σ k' C') := by
  have rd1 := poolManagerBlocks.poolManager_block_4038 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  rcases decodePoolKeyTraceWords v hstack (by omega) hhi hsize
      (by rw [deployedRuntime_jumps]; jump_dest) rd1 with ⟨hbad, hr⟩ | ⟨hc, aw1, k1, C1, haw1, rd2⟩
  · exact .inl ⟨fun hh => hbad hh.1, hr⟩
  · by_cases hp : (calldataWord I.calldata 164).toNat < 2^160
    · obtain ⟨k2, C2, rd3⟩ := RD.pack (poolManagerBlocks.poolManager_block_4046_fallthrough
        (by omega) (addressSubMask_zero hp) rd2)
      have hclean : UInt256.land (calldataWord I.calldata 164)
          (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
          calldataWord I.calldata 164 := solcAddrMask_clean hp
      simp only [poolManagerBlocks.poolManager_block_4046_fallthrough_stack] at rd3
      change RD _ _ _ _ _ (UInt256.land (calldataWord I.calldata 164) _ :: _ :: _ :: _) _ _ _ _ _ _ at rd3
      rw [hclean] at rd3
      exact .inr ⟨hc, hp, aw1, k2, C2, haw1, rd3⟩
    · have rd3 := poolManagerBlocks.poolManager_block_4046_taken (by omega)
        (addressSubMask_nonzero hp) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact .inl ⟨fun hh => hp hh.2, emptyRevert v (by change R.length+5 ≤ 1024; omega) rd3⟩

end Benchmarks.UniswapV4PoolManager

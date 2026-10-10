import Benchmarks.UniswapV3.Pool.ObservationMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_062
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_069

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleSearchZeroMem (mem : ByteArray) (p : UInt256) : ByteArray :=
  wordArrayAllocMem (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩])
    (p + ⟨128⟩) [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]

theorem observationPairInitializeCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (search : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (if search then ⟨20379⟩ else ⟨18642⟩)
      R mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 256 ≤ 2 ^ 200)
    (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', C + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if search then ⟨20395⟩ else ⟨18658⟩)
        ((p + ⟨128⟩) :: p :: R) (oracleSearchZeroMem mem p) aw' rdata σ k' C' ∧
      HeapMemory (oracleSearchZeroMem mem p) aw' (p + ⟨128⟩ + ⟨128⟩) ∧
      MemoryPrefix mem (oracleSearchZeroMem mem p) p.toNat ∧
      (p + ⟨128⟩ + ⟨128⟩).toNat ≤ aw'.toNat * 32 + 32 := by
  have r1 : RD (deployedRuntime v) ee g s0 ⟨22090⟩
      ((if search then ⟨20387⟩ else ⟨18650⟩) :: R) mem aw rdata σ (k + 4) (C + 15) := by
    cases search
    · exact uniswapV3Pool_block_18642 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    · exact uniswapV3Pool_block_20379 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw1, k1, C1, hC1, r2, hm1, _⟩ := observationZeroCursorX (v := v) r1 hm (by omega)
    (by cases search <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest) (by evm_ov)
  have hp1 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have r3 : RD (deployedRuntime v) ee g s0 ⟨22090⟩
      ((if search then ⟨20395⟩ else ⟨18658⟩) :: p :: R)
      (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) aw1 rdata σ (k1 + 4) (C1 + 15) := by
    cases search
    · exact uniswapV3Pool_block_18650 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    · exact uniswapV3Pool_block_20387 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw2, k2, C2, hC2, r4, hm2, hcover2⟩ := observationZeroMonoX (v := v) r3 hm1
    (by rw [hp1]; omega)
    (by cases search <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest) (by evm_ov)
  refine ⟨aw2, k2, C2, by omega, r4, hm2, ?_, hcover2⟩
  have hpre1 := wordArrayAllocMem_prefix mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  have hpre2 := wordArrayAllocMem_prefix
    (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) (p + ⟨128⟩) [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  exact hpre1.trans (hpre2.mono (by rw [hp1]; omega))

theorem observationPairInitializeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (search : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (if search then ⟨20379⟩ else ⟨18642⟩)
      R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 256 ≤ 2 ^ 200)
    (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', C + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if search then ⟨20395⟩ else ⟨18658⟩)
        ((p + ⟨128⟩) :: p :: R) (oracleSearchZeroMem mem p) aw' rdata σ k' C' ∧
      HeapMemory (oracleSearchZeroMem mem p) aw' (p + ⟨128⟩ + ⟨128⟩) ∧
      MemoryPrefix mem (oracleSearchZeroMem mem p) p.toNat ∧
      (p + ⟨128⟩ + ⟨128⟩).toNat ≤ aw'.toNat * 32 + 32 := by
  exact observationPairInitializeCursorX (v := v) search rd hm.cursor hb hov

end Benchmarks.UniswapV3.Pool

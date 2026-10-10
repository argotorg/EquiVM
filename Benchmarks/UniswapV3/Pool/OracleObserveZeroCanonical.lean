import Benchmarks.UniswapV3.Pool.OracleObserveZeroFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleObserveZeroMemory (mem : ByteArray) (p : UInt256) (last : OracleObservation)
    (time : UInt256) (tick : Int) (liquidity : UInt256) : ByteArray :=
  if last.timestamp = time then wordArrayAllocMem mem p last.words
  else oracleTransformMem (wordArrayAllocMem mem p last.words) (p + ⟨128⟩) last time tick liquidity

def oracleObserveZeroFree (p : UInt256) (last : OracleObservation) (time : UInt256) : UInt256 :=
  if last.timestamp = time then p + ⟨128⟩ else p + ⟨128⟩ + ⟨256⟩

theorem oracleObserveZeroFree_bound (p : UInt256) (last : OracleObservation) (time : UInt256)
    (hb : p.toNat + 384 ≤ 2 ^ 200) :
    (oracleObserveZeroFree p last time).toNat ≤ p.toNat + 384 := by
  unfold oracleObserveZeroFree
  split_ifs
  · change (p + UInt256.ofNat 128).toNat ≤ p.toNat + 384
    rw [uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)]
    omega
  · rw [uadd_assoc]
    change (p + UInt256.ofNat 384).toNat ≤ p.toNat + 384
    rw [uadd_word_ofNat_toNat p 384 (by change _ < 2 ^ 256; omega)]

theorem oracleObserveZeroCanonicalFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret card liquidity index tickRaw secondsAgoRaw timeRaw time : UInt256}
    {tick : Int} {last : OracleObservation} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13311⟩
      ((if last.initialized then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 4294967295 :: p :: last.timestamp ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw ::
        ⟨8⟩ :: ret :: R)
      (observationReadHeadMem mem p last) (oracleReadHeadAw mem aw) rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      ((oracleObserveZeroResult last time tick liquidity).secondsPerLiquidity ::
        EVM.wordOfInt (oracleObserveZeroResult last time tick liquidity).tickCumulative :: R)
      (oracleObserveZeroMemory mem p last time tick liquidity) aw' rdata σ k' C' ∧
      HeapMemory (oracleObserveZeroMemory mem p last time tick liquidity) aw'
        (oracleObserveZeroFree p last time) := by
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hmem : uniswapV3Pool_block_13311_taken_memory (mem := observationReadHeadMem mem p last)
      (x0 := if last.initialized then ⟨1⟩ else ⟨0⟩) (x2 := p) = wordArrayAllocMem mem p last.words := by
    simp only [uniswapV3Pool_block_13311_taken_memory, hp96]
    exact observationReadHeadMem_write mem p last
  have hmemf : uniswapV3Pool_block_13311_fallthrough_memory (mem := observationReadHeadMem mem p last)
      (x0 := if last.initialized then ⟨1⟩ else ⟨0⟩) (x2 := p) = wordArrayAllocMem mem p last.words := hmem
  obtain ⟨hm1, hlast, _, hcover1⟩ := oracleReadCompletedMemory_cursor last hm.cursor (by omega)
  have ht : UInt256.land timeRaw (UInt256.ofNat 4294967295) = time := htime
  by_cases heq : last.timestamp = time
  · have r1 := uniswapV3Pool_block_13311_taken (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [ht, heq, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    rw [hmem] at r1
    simp only [uniswapV3Pool_block_13311_taken_stack] at r1
    have r2 := oracleObserveZeroLoadX (v := v) r1 hm1 (by rw [hp128]; omega) hlast
      (by rw [hp128]) hcover1 (by evm_ov)
    have r3 := uniswapV3Pool_block_13584 (immWords := wordsOf (immStore v)) (by evm_ov) hret r2
    simp only [oracleObserveZeroResult, oracleObserveZeroMemory, oracleObserveZeroFree, if_pos heq]
    exact ⟨_, _, _, r3, hm1⟩
  · have hne : UInt256.eq time last.timestamp = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ heq (uInt256_eq_one_eq h).symm)
    have r1 := uniswapV3Pool_block_13311_fallthrough (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [ht]; exact hne) rd
    rw [hmemf] at r1
    simp only [uniswapV3Pool_block_13311_fallthrough_stack] at r1
    have r2 := uniswapV3Pool_block_13326 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_13326_stack] at r2
    obtain ⟨aw2, k2, C2, _, r3, hm2, hobs2, _, hcover2⟩ :=
      oracleTransformMonoX (v := v) (time := time) (tick := tick) (last := last) r2 hm1 hlast
        (by have h := hm.lower; omega) (by rw [hp128]) (by rw [hp128]; omega)
        htime htick hliq (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    have hp256 : (p + (⟨128⟩ : UInt256) + ⟨128⟩).toNat = p.toNat + 256 := by
      rw [uadd_assoc]
      exact uadd_word_ofNat_toNat p 256 (by change _ < 2 ^ 256; omega)
    have hp384 : (p + (⟨128⟩ : UInt256) + ⟨256⟩).toNat = p.toNat + 384 := by
      rw [uadd_assoc]
      exact uadd_word_ofNat_toNat p 384 (by change _ < 2 ^ 256; omega)
    have r4 := uniswapV3Pool_block_13337 (immWords := wordsOf (immStore v)) (by evm_ov) r3
    simp only [uniswapV3Pool_block_13337_stack] at r4
    have r5 := oracleObserveZeroLoadX (v := v) r4 hm2 (by rw [hp384]; omega) hobs2
      (by rw [hp256, hp384]) hcover2 (by evm_ov)
    have r6 := uniswapV3Pool_block_13584 (immWords := wordsOf (immStore v)) (by evm_ov) hret r5
    simp only [oracleObserveZeroResult, oracleObserveZeroMemory, oracleObserveZeroFree, if_neg heq]
    exact ⟨_, _, _, r6, hm2⟩

end Benchmarks.UniswapV3.Pool

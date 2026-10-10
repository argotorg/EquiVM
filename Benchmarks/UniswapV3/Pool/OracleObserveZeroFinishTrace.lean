import Benchmarks.UniswapV3.Pool.OracleObserveZeroLoadTrace
import Benchmarks.UniswapV3.Pool.ObservationReadMemory
import Benchmarks.UniswapV3.Pool.OracleTransform

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveZeroFinishCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret card liquidity index tickRaw secondsAgoRaw timeRaw time : UInt256}
    {tick : Int} {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13311⟩
      ((if (oracleStoredObservation index σ ee).initialized then ⟨1⟩ else ⟨0⟩) ::
        UInt256.ofNat 4294967295 :: p :: (oracleStoredObservation index σ ee).timestamp ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw ::
        ⟨8⟩ :: ret :: R)
      (observationReadHeadMem mem p (oracleStoredObservation index σ ee))
      (oracleReadHeadAw mem aw) rdata σ k C)
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200) (hin : index.toNat < 65535)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    Nonempty (OracleObserveSingleExit v ee g s0 σ rdata ret R time ⟨0⟩ tick index liquidity card
      mem (oracleReadHeadAw mem aw) p C) := by
  let last := oracleStoredObservation index σ ee
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
  obtain ⟨hm1, hlast, hpre1, hcover1⟩ := oracleReadCompletedMemory_cursor last hm (by omega)
  have hs : OracleObserveSingleRun time ⟨0⟩ tick index liquidity card σ ee
      (oracleObserveZeroResult last time tick liquidity).cumulatives := .zero rfl hin
  have ht : UInt256.land timeRaw (UInt256.ofNat 4294967295) = time := htime
  by_cases heq : last.timestamp = time
  · have r1 := uniswapV3Pool_block_13311_taken (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [ht, heq, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    rw [hmem] at r1
    simp only [uniswapV3Pool_block_13311_taken_stack] at r1
    have r2 := oracleObserveZeroLoadX (v := v) r1 hm1 (by rw [hp128]; omega) hlast
      (by rw [hp128]) hcover1 (by evm_ov)
    rw [oracleObserveZeroResult, if_pos heq] at hs
    have hv := oracleStoredValid index σ ee
    obtain ⟨out⟩ := oracleObserveReturnX (v := v) r2 hm1 hcover1 hs hv.cleanTick
      (by rw [wordOfInt_ofNat_toNat]; exact hv.cleanSeconds) hv.tick
      ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hv.seconds⟩ hret (by omega)
    exact ⟨out.lift (by dsimp only [memExpansionCost]; omega)
      (by rw [hp128]; omega) hpre1⟩
  · have hne : UInt256.eq time last.timestamp = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ heq (uInt256_eq_one_eq h).symm)
    have r1 := uniswapV3Pool_block_13311_fallthrough (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [ht]; exact hne) rd
    rw [hmemf] at r1
    simp only [uniswapV3Pool_block_13311_fallthrough_stack] at r1
    have r2 := uniswapV3Pool_block_13326 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_13326_stack] at r2
    obtain ⟨aw2, k2, C2, hC2, r3, hm2, hobs2, hpre2, hcover2⟩ :=
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
    rw [oracleObserveZeroResult, if_neg heq] at hs
    have htime32 : time.toNat < 2 ^ 32 := by
      rw [← htime]
      exact u256LandMaskToNatLtOfToNat _ _ (by decide)
    have hv := oracleTransformedValid last time tick liquidity htime32
    obtain ⟨out⟩ := oracleObserveReturnX (v := v) r5 hm2 hcover2 hs hv.cleanTick
      (by rw [wordOfInt_ofNat_toNat]; exact hv.cleanSeconds) hv.tick
      ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hv.seconds⟩ hret (by omega)
    exact ⟨out.lift (by dsimp only [memExpansionCost] at hC2 ⊢; omega)
      (by rw [hp384]; omega) (hpre1.trans (hpre2.mono (by rw [hp128]; omega)))⟩

theorem oracleObserveZeroFinishMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret card liquidity index tickRaw secondsAgoRaw timeRaw time : UInt256}
    {tick : Int} {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13311⟩
      ((if (oracleStoredObservation index σ ee).initialized then ⟨1⟩ else ⟨0⟩) ::
        UInt256.ofNat 4294967295 :: p :: (oracleStoredObservation index σ ee).timestamp ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw ::
        ⟨8⟩ :: ret :: R)
      (observationReadHeadMem mem p (oracleStoredObservation index σ ee))
      (oracleReadHeadAw mem aw) rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200) (hin : index.toNat < 65535)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    Nonempty (OracleObserveSingleExit v ee g s0 σ rdata ret R time ⟨0⟩ tick index liquidity card
      mem (oracleReadHeadAw mem aw) p C) := by
  exact oracleObserveZeroFinishCursorX (v := v) rd hm.cursor hb hin htime htick hliq hret hov

end Benchmarks.UniswapV3.Pool

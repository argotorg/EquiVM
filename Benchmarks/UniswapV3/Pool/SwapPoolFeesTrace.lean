import Benchmarks.UniswapV3.Pool.SwapPoolFeesSource
import Benchmarks.UniswapV3.Pool.SwapWriteGuard
import Benchmarks.UniswapV3.Pool.SwapFeeGrowthStoreTrace
import Benchmarks.UniswapV3.Pool.SwapProtocolMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapPoolFeesBranchX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨4418⟩ else ⟨4345⟩)
      (p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hfit : s.Fits) (hperm : ee.perm = true) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 8 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨4488⟩ (p :: R)
      mem aw' rdata (swapPoolFeesMap σ ee second s) k' C' ∧ HeapMemory mem aw' free := by
  have hg := SwapStateMemory.load_feeGrowth hs (by change _ < 2 ^ 256; omega)
  have hp := SwapStateMemory.load_protocolFee hs (by change _ < 2 ^ 256; omega)
  have hclean := uint128Word_clean hfit.2.2.2.2.1
  have hb128 : (p + UInt256.ofNat 128).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)]; omega
  have hb160 : (p + UInt256.ofNat 160).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 160 (by change _ < 2 ^ 256; omega)]; omega
  have hm1 := hm.expand32 (p + UInt256.ofNat 128) hb128
  have hm2 := hm1.expand32 (p + UInt256.ofNat 160) hb160
  have hm3 := hm2.expand32 (p + UInt256.ofNat 160) hb160
  cases second
  · by_cases hz : s.protocolFee = ⟨0⟩
    · obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_4345_taken
        (immWords := wordsOf (immStore v)) (by omega) hperm (by
          rw [hp, solcMask128]
          change UInt256.isZero (uint128Word s.protocolFee) ≠ _
          rw [hclean, hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      have r2 := uniswapV3Pool_block_4413 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
      refine ⟨_, k1 + 3, C1 + 12, ?_, hm2⟩
      simpa only [swapPoolFeesMap, flashProtocolMap, hclean, hz, if_true, feeGrowthSlot,
        Bool.false_eq_true, if_false, hg] using r2
    · obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_4345_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hperm (by
          rw [hp, solcMask128]
          change UInt256.isZero (uint128Word s.protocolFee) = _
          rw [hclean]; exact isZero_eq_zero_of_ne hz) rd
      rw [hg] at r1
      obtain ⟨k2, C2, r2⟩ := uniswapV3Pool_block_4372
        (immWords := wordsOf (immStore v)) hov hperm r1
      have r3 := uniswapV3Pool_block_4413 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r2
      refine ⟨_, k2 + 3, C2 + 12, ?_, hm3⟩
      simp only [swapPoolFeesMap, flashProtocolMap, hclean, hz, if_false, feeGrowthSlot,
        Bool.false_eq_true]
      simpa only [hp, protocolFeeUpdateWord, protocolFeesWord, protocolFeesToken0Word,
        uint128Word, solcSlotWordAt, solcSlotWord, Bool.false_eq_true, if_false, solcMask128,
        u256_lor_comm, u256_add_comm, u256_land_comm] using r3
  · by_cases hz : s.protocolFee = ⟨0⟩
    · obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_4418_taken
        (immWords := wordsOf (immStore v)) (by omega) hperm (by
          rw [hp, solcMask128]
          change UInt256.isZero (uint128Word s.protocolFee) ≠ _
          rw [hclean, hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      refine ⟨_, k1, C1, ?_, hm2⟩
      simpa only [swapPoolFeesMap, flashProtocolMap, hclean, hz, if_true, feeGrowthSlot, hg] using
        r1
    · obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_4418_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hperm (by
          rw [hp, solcMask128]
          change UInt256.isZero (uint128Word s.protocolFee) = _
          rw [hclean]; exact isZero_eq_zero_of_ne hz) rd
      rw [hg] at r1
      obtain ⟨k2, C2, r2⟩ := uniswapV3Pool_block_4446
        (immWords := wordsOf (immStore v)) hov hperm r1
      refine ⟨_, k2, C2, ?_, hm3⟩
      simp only [swapPoolFeesMap, flashProtocolMap, hclean, hz, if_false, feeGrowthSlot, if_true]
      simp only [solcMask128] at r2
      simpa only [hp, protocolFeeUpdateWord, protocolFeesWord, protocolFeesToken1Word,
        uint128Word, solcSlotWordAt, solcSlotWord, if_true, solcShift128,
        u256_lor_comm, u256_add_comm, u256_land_comm] using r2

theorem swapPoolFeesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4338⟩
      (swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hsget : frame.locals.get? "state" = some s.value)
    (hg : ∀ second, frame.locals.get? (feeGrowthName second) = none)
    (hp : frame.locals.get? "protocolFees" = none)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hfit : s.Fits) (hperm : ee.perm = true) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 20 ≤ 1024) :
    ExecStmt config frame evm swapTransition.body[16]!
        (.ok frame (swapPoolFeesState evm (!a.zeroForOne) s)) ∧
      SourceState s0 ee (swapPoolFeesMap σ ee (!a.zeroForOne) s)
        (swapPoolFeesState evm (!a.zeroForOne) s) ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨4488⟩
        (swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata (swapPoolFeesMap σ ee (!a.zeroForOne) s) k' C' ∧
        HeapMemory mem aw' free := by
  refine ⟨swapPoolFeesSource evm a.zeroForOne s hf hz hsget hg hp hfit,
    SourceState.swapPoolFees hsource (!a.zeroForOne) s, ?_⟩
  cases hzero : a.zeroForOne
  · have r1 := uniswapV3Pool_block_4338_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 13 ≤ 1024; omega)
      (by change UInt256.isZero a.zeroForOne.toUInt256 ≠ _; rw [hzero]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simpa only [swapLoopWords, swapWords, List.cons_append, List.nil_append,
      hzero, Bool.not_false] using
      swapPoolFeesBranchX (v := v) true s r1 hm hs hfit hperm hb
        (by change R.length + 12 + 8 ≤ 1024; omega)
  · have r1 := uniswapV3Pool_block_4338_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 13 ≤ 1024; omega)
      (by change UInt256.isZero a.zeroForOne.toUInt256 = _; rw [hzero]; decide) rd
    simpa only [swapLoopWords, swapWords, List.cons_append, List.nil_append,
      hzero, Bool.not_true] using
      swapPoolFeesBranchX (v := v) false s r1 hm hs hfit hperm hb
        (by change R.length + 12 + 8 ≤ 1024; omega)

end Benchmarks.UniswapV3.Pool

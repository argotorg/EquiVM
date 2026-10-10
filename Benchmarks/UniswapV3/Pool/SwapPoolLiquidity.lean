import Benchmarks.UniswapV3.Pool.SwapWriteGuard
import Benchmarks.UniswapV3.Pool.SwapIterationStepLoad
import Benchmarks.UniswapV3.Pool.PoolLiquidityStore
import Benchmarks.UniswapV3.Pool.SourceFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapPoolLiquidityX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cache exactWord free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4268⟩
      ([p, exactWord, cache] ++ R) mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hcget : frame.locals.get? "cache" = some c.value)
    (hsget : frame.locals.get? "state" = some s.value)
    (hbase : frame.locals.get? "liquidity" = none)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hcf : c.Fits) (hsf : s.Fits)
    (hperm : ee.perm = true) (hbc : cache.toNat + 192 ≤ 2 ^ 200)
    (hbp : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    ∃ evm' σ' aw' k' C',
      ExecStmt config frame evm swapTransition.body[15]! (.ok frame evm') ∧
      SourceState s0 ee σ' evm' ∧
      RD (deployedRuntime v) ee g s0 ⟨4338⟩
        ([p, exactWord, cache] ++ R) mem aw' rdata σ' k' C' ∧ HeapMemory mem aw' free := by
  have hsl := SwapStateMemory.load_liquidity hs (by change _ < 2 ^ 256; omega)
  have hcl : memLoad (cache + UInt256.ofNat 32) mem = c.liquidityStart :=
    WordArrayMemory.load hc 1 (by change 1 < 6; decide)
      (by change cache.toNat + 192 < 2 ^ 256; omega)
  have hsl' : memLoad (UInt256.ofNat 192 + p) mem = s.liquidity := by
    rw [u256_add_comm]; exact hsl
  have hcl' : memLoad (UInt256.ofNat 32 + cache) mem = c.liquidityStart := by
    rw [u256_add_comm]; exact hcl
  have hs128 := uint128Word_clean hsf.2.2.2.2.2
  have hc128 := uint128Word_clean hcf.2.1
  have hbp192 : (UInt256.ofNat 192 + p).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat p 192 (by change _ < 2 ^ 256; omega)]; omega
  have hbc32 : (UInt256.ofNat 32 + cache).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat cache 32 (by change _ < 2 ^ 256; omega)]; omega
  have hm1 := hm.expand32 (UInt256.ofNat 192 + p) hbp192
  have hm2 := hm1.expand32 (UInt256.ofNat 32 + cache) hbc32
  have he := evalExpr_int_ne
    (evalExpr_structField (cfg := config) (evm := evm) (name := "liquidityStart")
      (evalExpr_var_get hcget) rfl)
    (evalExpr_structField (name := "liquidity") (evalExpr_var_get hsget) rfl)
  change evalExpr? config frame evm
    (.binary .ne (.field (.var "cache") "liquidityStart") (.field (.var "state") "liquidity")) =
    .ok (.bool (decide (Int.ofNat c.liquidityStart.toNat ≠ Int.ofNat s.liquidity.toNat))) at he
  by_cases hl : c.liquidityStart = s.liquidity
  · have r1 := uniswapV3Pool_block_4268_taken (immWords := wordsOf (immStore v))
      (by change R.length + 8 ≤ 1024; omega) (by
        rw [hsl', hcl', solcMask128]
        change UInt256.eq (uint128Word c.liquidityStart) (uint128Word s.liquidity) ≠ _
        rw [hs128, hc128, hl, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [hl, ne_eq, not_true_eq_false, decide_false] at he
    exact ⟨evm, σ, _, _, _, ExecStmt.iteFalse he .nil, hsource, r1, hm2⟩
  · have r1 := uniswapV3Pool_block_4268_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 8 ≤ 1024; omega) (by
        rw [hsl', hcl', solcMask128]
        change UInt256.eq (uint128Word c.liquidityStart) (uint128Word s.liquidity) = _
        rw [hs128, hc128]
        exact uInt256_eq_zero_of_ne (fun h ↦ hl (uInt256_eq_one_eq h))) rd
    have hn : Int.ofNat c.liquidityStart.toNat ≠ Int.ofNat s.liquidity.toNat := by
      intro hh
      exact hl (u256_inj (Int.ofNat_inj.mp hh))
    rw [show decide (Int.ofNat c.liquidityStart.toNat ≠ Int.ofNat s.liquidity.toNat) = true
      from decide_eq_true hn] at he
    have hass := assignPoolLiquidity frame.locals frame.immutables evm
      (Int.ofNat s.liquidity.toNat) hbase
    rw [← frame_eq_of_parts hf rfl, wordOfInt_ofNat_toNat] at hass
    have hex : ExecStmt config frame evm swapTransition.body[15]!
        (.ok frame (storePoolLiquidity evm s.liquidity)) :=
      ExecStmt.iteTrue he (ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_structField (name := "liquidity") (evalExpr_var_get hsget) rfl) hass) .nil)
    obtain ⟨k2, C2, r2⟩ := uniswapV3Pool_block_4302 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 7 ≤ 1024; omega) hperm r1
    have hm3 := hm2.expand32 (p + UInt256.ofNat 192)
      (by rw [u256_add_comm]; exact hbp192)
    have hsrc := hsource.readModifyWrite ⟨4⟩
      (fun old ↦ protocolFeeUpdateWord false old s.liquidity)
    refine ⟨storePoolLiquidity evm s.liquidity, _, _, k2, C2, hex, hsrc, ?_, hm3⟩
    simpa only [hsl, protocolFeeUpdateWord, Bool.false_eq_true, if_false, uint128Word,
      solcMask128, solcSlotWord, u256_land_comm] using r2

end Benchmarks.UniswapV3.Pool

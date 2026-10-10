import Benchmarks.UniswapV3.Pool.SwapIterationPriceStore
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalSwapCrossGuard {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value) :
    evalExpr? config frame evm
      (.binary .eq (.field (.var "state") "sqrtPriceX96")
        (.field (.var "step") "sqrtPriceNextX96")) = .ok (.bool (decide (s.price = d.priceNext))) :=
  evalExpr_word_eq
    (evalExpr_structField (name := "sqrtPriceX96") (evalExpr_var_get hs) rfl)
    (evalExpr_structField (name := "sqrtPriceNextX96") (evalExpr_var_get hd) rfl)

theorem swapCrossGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3637⟩ (q :: p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hprice : s.price.toNat < 2 ^ 160)
    (hnext : d.priceNext.toNat < 2 ^ 160)
    (hbp : p.toNat + 224 ≤ 2 ^ 200) (hbq : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if s.price = d.priceNext then ⟨3672⟩ else ⟨3934⟩)
        (q :: p :: R) mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧
      aw.toNat ≤ aw'.toNat := by
  have hlp : memLoad (UInt256.ofNat 64 + p) mem = s.price := by
    rw [u256_add_comm]
    exact SwapStateMemory.load_price hs (by change _ < 2 ^ 256; omega)
  have hlq : memLoad (UInt256.ofNat 96 + q) mem = d.priceNext := by
    rw [u256_add_comm]
    exact SwapIterationMemory.load_priceNext hd (by change _ < 2 ^ 256; omega)
  have hc : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) s.price = s.price := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hprice
  have hn : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) d.priceNext = d.priceNext := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hnext
  have hb0 : (UInt256.ofNat 96 + q).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat q 96 (by change _ < 2 ^ 256; omega)]
    omega
  have hb1 : (UInt256.ofNat 64 + p).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)]
    omega
  have hm1 := hm.expand32 (UInt256.ofNat 96 + q) hb0
  have hm2 := hm1.expand32 (UInt256.ofNat 64 + p) hb1
  have hmono := (expandedWords_mono (off := UInt256.ofNat 96 + q) (size := ⟨32⟩)
    hm.active hb0).trans (expandedWords_mono (off := UInt256.ofNat 64 + p) (size := ⟨32⟩)
      hm1.active hb1)
  by_cases heq : s.price = d.priceNext
  · have r1 := uniswapV3Pool_block_3637_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hlp, hlq, amountDeltaMask160, hc, hn, heq, uInt256_eq_self]; rfl) rd
    simp only [heq, if_true]
    refine ⟨_, _, _, ?_, r1, hm2, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega
  · have hcmp : UInt256.eq s.price d.priceNext = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ heq (uInt256_eq_one_eq h))
    have r1 := uniswapV3Pool_block_3637_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hlp, hlq, amountDeltaMask160, hc, hn, hcmp]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [heq, if_false]
    refine ⟨_, _, _, ?_, r1, hm2, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool

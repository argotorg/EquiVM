import Benchmarks.UniswapV4PoolManager.PoolSwapScanComputeLocals
import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingPost
import Benchmarks.UniswapV4PoolManager.PoolSwapIterationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapIterationPost {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {remaining calculated fee protocol amount : UInt256}
    (hl : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (htc : int24Canonical r.tick) (hprice : r.price.toNat < 2^160)
    (hlimit : p.priceLimit.toNat < 2^160) (hliq : r.liquidity.toNat < 2^128)
    (he : poolSwapIterationResult f evm id s r p remaining calculated fee protocol amount = .ok ff post) :
    let scan := poolSwapScanStep s evm id r p
    let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
    let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
    let computed := poolSwapComputeStep {scan with tickNext := tickClampWord scan.tickNext} next w
    let result := {r with price := w.next}
    let fees := poolSwapAccountingStep computed result fee protocol
    let result' := poolSwapTickResultWords evm id fees result p.zeroForOne
    PoolSwapLoopLocals ff id fees result' p (poolSwapRemainingAfter computed p.amountSpecified remaining)
      (poolSwapCalculatedAfter computed p.amountSpecified calculated) fee protocol (poolSwapProtocolAmount computed fee protocol amount) ∧
    post.executionEnv = evm.executionEnv ∧ result'.price.toNat < 2^160 ∧
    int24Canonical result'.tick ∧ result'.liquidity.toNat < 2^128 := by
  dsimp only
  let scan := poolSwapScanStep s evm id r p
  let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  let clamped := {scan with tickNext := tickClampWord scan.tickNext}
  let computed := poolSwapComputeStep clamped next w
  let result := {r with price := w.next}
  let f1 := poolSwapComputeFrame (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) scan)
    clamped r p next remaining fee
  unfold poolSwapIterationResult at he
  dsimp only at he
  by_cases hfit : swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  · rw [if_pos hfit] at he
    have hl1 := (hl.scan_step evm).compute_step next
    have hpost := poolSwapAccountingPost (f := f1) (s := computed) (r := result)
      hl1 htc (tickClampWord_canonical scan.tickNext) hliq he
    obtain ⟨hl2, henv, hnewprice, hnewtick, hnewliq⟩ := hpost
    refine ⟨hl2, henv, ?_, hnewtick, hnewliq⟩
    rw [hnewprice]
    exact swapStepWord_next_canonical hprice
      (swapTargetWord_canonical (tickSqrtPrice_lt_160 (tickClampWord_natAbs scan.tickNext)) hlimit) hfit
  · rw [if_neg hfit] at he
    cases he

end Benchmarks.UniswapV4PoolManager

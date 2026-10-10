import Benchmarks.UniswapV4PoolManager.PoolSwapScanMemoryTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapComputeMemoryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapScanComputeAW (aw step state params : UInt256) : UInt256 :=
  poolSwapComputeAW (poolSwapScanAW aw step state params) step state params

theorem poolSwapScanComputeTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {aw step state params id remaining calculated tag x1 fee protocol amount : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : PoolSwapMemoryView mem step state params s r p)
    (htc : int24Canonical r.tick) (hspacing : int24Canonical p.tickSpacing)
    (hprice : r.price.toNat < 2^160) (hlimit : p.priceLimit.toNat < 2^160)
    (hliq : r.liquidity.toNat < 2^128) (hfee : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨19169⟩
      ([remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
        step, poolSlot id, state] ++ R) mem aw rdata evm.accountMap k C) :
    let scan := poolSwapScanStep s evm id r p
    let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
    let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
    (swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee →
      ∃ mem' k' C', C ≤ C' ∧
        RD (deployedRuntime v) I g s0 (if 0 < EVM.signed p.amountSpecified then ⟨19740⟩ else ⟨20320⟩)
          ([remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
            step, poolSlot id, state] ++ R) mem' (poolSwapScanComputeAW aw step state params) rdata evm.accountMap k' C' ∧
        PoolSwapMemoryView mem' step state params
          (poolSwapComputeStep {scan with tickNext := tickClampWord scan.tickNext} next w) {r with price := w.next} p ∧
        MemoryWindowEq mem mem' 64 (min step.toNat state.toNat)) ∧
    (¬swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee →
      RDrev (deployedRuntime v) g s0) := by
  dsimp only
  let scan := poolSwapScanStep s evm id r p
  let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  obtain ⟨mem1, k1, C1, hC1, rd1, hm1, hw1⟩ :=
    poolSwapScanMemoryTrace v (by omega) hI hm htc hspacing hprice h
  have hnext : next.toNat < 2^160 := tickSqrtPrice_lt_160 (tickClampWord_natAbs scan.tickNext)
  have hcompute := poolSwapComputeMemoryTrace v hstack hm1 hprice hlimit hnext hliq hfee rd1
  constructor
  · intro hfit
    obtain ⟨mem2, k2, C2, hC2, rd2, hm2, hw2⟩ := hcompute.1 hfit
    exact ⟨mem2, k2, C2, hC1.trans hC2, rd2, hm2, hw1.trans hw2⟩
  · exact hcompute.2

end Benchmarks.UniswapV4PoolManager

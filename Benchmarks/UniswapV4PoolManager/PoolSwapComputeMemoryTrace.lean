import Benchmarks.UniswapV4PoolManager.PoolSwapComputeWindow
import Benchmarks.UniswapV4PoolManager.PoolSwapComputeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapComputeMemoryTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {aw step state params pool next remaining calculated tag x1 fee protocol amount : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024)
    (hm : PoolSwapMemoryView mem step state params s r p)
    (hprice : r.price.toNat < 2^160) (hlimit : p.priceLimit.toNat < 2^160)
    (hnext : next.toNat < 2^160) (hliq : r.liquidity.toNat < 2^128) (hfee : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨19479⟩
      ([next, solcAddrMask, step, ⟨96⟩, ⟨1⟩, ⟨64⟩,
        UInt256.ofNat (2^128-1), state, fee, UInt256.fromBool (!p.zeroForOne),
        remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
        step, pool, state] ++ R) mem aw rdata σ k C) :
    let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
    (swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee →
      ∃ mem' k' C', C ≤ C' ∧
        RD (deployedRuntime v) I g s0 (if 0 < EVM.signed p.amountSpecified then ⟨19740⟩ else ⟨20320⟩)
          ([remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
            step, pool, state] ++ R) mem' (poolSwapComputeAW aw step state params) rdata σ k' C' ∧
        PoolSwapMemoryView mem' step state params (poolSwapComputeStep s next w) {r with price := w.next} p ∧
        MemoryWindowEq mem mem' 64 (min step.toNat state.toNat)) ∧
    (¬swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee →
      RDrev (deployedRuntime v) g s0) := by
  dsimp only
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  have hdir : UInt256.fromBool (!p.zeroForOne) = (if p.zeroForOne then (⟨0⟩ : UInt256) else ⟨1⟩) := by
    cases p.zeroForOne <;> rfl
  rw [hdir] at h
  have hmStart := hm.compute_start next
  have hmComputed := hmStart.compute_store w
  have hcompute := poolSwapComputeTrace (next := next) (limit := p.priceLimit) (price := r.price)
    (liquidity := r.liquidity) (specified := p.amountSpecified) v p.zeroForOne hstack hnext hlimit hfee
    (by rw [hmStart.price]; exact solcAddrMask_clean hprice)
    (by rw [hmStart.limit]; exact solcAddrMask_clean hlimit)
    (by rw [hmStart.liquidity]; exact u256LandMaskCleanOfToNat _ _ (bits := 128) rfl hliq)
    hmComputed.specified h
  constructor
  · intro hfit
    obtain ⟨k2, C2, hC2, rd2⟩ := hcompute.1 hfit
    rw [← hdir] at rd2
    exact ⟨_, k2, C2, hC2, rd2, hmComputed,
      (hm.compute_start_window next).trans (hmStart.compute_store_window w)⟩
  · exact hcompute.2

end Benchmarks.UniswapV4PoolManager

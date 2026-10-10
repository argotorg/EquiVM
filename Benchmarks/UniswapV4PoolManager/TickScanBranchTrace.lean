import Benchmarks.UniswapV4PoolManager.TickScanLeftReadTrace
import Benchmarks.UniswapV4PoolManager.TickScanLeftNextTrace
import Benchmarks.UniswapV4PoolManager.TickScanRightReadTrace
import Benchmarks.UniswapV4PoolManager.TickScanRightNextTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanBranchTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id compressed spacing step state fee direction x0 x1 params x3 x4 x6 x7 : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (lte : Bool) (hstack : R.length+33 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 (if lte then ⟨19234⟩ else ⟨21109⟩)
      ([compressed, spacing, poolSlot id, step, state, fee, direction, x0, x1, params, x3, x4,
        fee, x6, x7, direction, step, poolSlot id, state] ++ R) mem aw rdata evm.accountMap k C) :
    let chosen := if lte then compressed else compressed+UInt256.ofNat 1
    let masked := tickScanMasked evm id chosen lte
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19401⟩
      ([(decide (masked ≠ ⟨0⟩)).toUInt256, tickScanResultWord chosen spacing masked lte,
        UInt256.ofNat (2^256-887272), step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64,
        UInt256.ofNat (2^128-1), state, fee, direction, x0, x1, params, x3, x4, fee, x6, x7,
        direction, step, poolSlot id, state] ++ R)
      (tickScanMemory mem id chosen)
      (M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64))
      rdata evm.accountMap k' C' := by
  cases lte with
  | true =>
    obtain ⟨k1, C1, hC1, rd1⟩ := tickScanLeftReadTrace v (by simp; omega) hI h
    obtain ⟨k2, C2, hC2, rd2⟩ := tickScanLeftNextTrace v (by simp; omega) rd1
    exact ⟨k2, C2, hC1.trans hC2, rd2⟩
  | false =>
    obtain ⟨k1, C1, hC1, rd1⟩ := tickScanRightReadTrace v (by simp; omega) hI h
    obtain ⟨k2, C2, hC2, rd2⟩ := tickScanRightNextTrace v (by simp; omega) rd1
    exact ⟨k2, C2, hC1.trans hC2, rd2⟩

end Benchmarks.UniswapV4PoolManager

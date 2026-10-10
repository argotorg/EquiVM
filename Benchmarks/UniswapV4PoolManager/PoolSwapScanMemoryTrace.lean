import Benchmarks.UniswapV4PoolManager.PoolSwapComputeWindow
import Benchmarks.UniswapV4PoolManager.PoolSwapScanPriceTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapScanSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapScanMemoryTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {aw step state params id remaining calculated tag x1 fee protocol amount : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+33 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : PoolSwapMemoryView mem step state params s r p)
    (htc : int24Canonical r.tick) (hspacing : int24Canonical p.tickSpacing) (hprice : r.price.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 ⟨19169⟩
      ([remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
        step, poolSlot id, state] ++ R) mem aw rdata evm.accountMap k C) :
    let scan := poolSwapScanStep s evm id r p
    let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
    ∃ mem' k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19479⟩
      ([next, solcAddrMask, step, ⟨96⟩, ⟨1⟩, ⟨64⟩,
        UInt256.ofNat (2^128-1), state, fee, UInt256.fromBool (!p.zeroForOne),
        remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
        step, poolSlot id, state] ++ R) mem' (poolSwapScanAW aw step state params) rdata evm.accountMap k' C' ∧
      PoolSwapMemoryView mem' step state params {scan with tickNext := tickClampWord scan.tickNext} r p ∧
      MemoryWindowEq mem mem' 64 (min step.toNat state.toNat) := by
  dsimp only
  have hdir : UInt256.fromBool (!p.zeroForOne) = (if p.zeroForOne then (⟨0⟩ : UInt256) else ⟨1⟩) := by
    cases p.zeroForOne <;> rfl
  rw [hdir] at h
  have hm0 := hm.scan_start
  obtain ⟨k1, C1, hC1, rd1⟩ := poolSwapScanPriceTrace
    (price := r.price) (tick := r.tick) (spacing := p.tickSpacing) v p.zeroForOne hstack hI
    (by rw [hm.price]; exact solcAddrMask_clean hprice)
    (by rw [hm0.tick]; exact (signextend24_eq_iff _).mpr htc)
    (by rw [hm0.spacing]; exact (signextend24_eq_iff _).mpr hspacing) h
  let compressed := tickScanCompressed r.tick p.tickSpacing p.zeroForOne
  let masked := tickScanMasked evm id compressed p.zeroForOne
  have hmHash := hm0.hash_scratch (tickPositionWord compressed) (poolSlot id+UInt256.ofNat 5)
  have hmScan := hmHash.clamp
    (tickScanResultWord compressed p.tickSpacing masked p.zeroForOne) (decide (masked ≠ ⟨0⟩))
  have hwindow := (hm.scan_start_window.trans
    (hm0.hash_scratch_window (tickPositionWord compressed) (poolSlot id+UInt256.ofNat 5))).trans
    (hmHash.clamp_window (tickScanResultWord compressed p.tickSpacing masked p.zeroForOne) (decide (masked ≠ ⟨0⟩)))
  rw [← hdir] at rd1
  exact ⟨_, k1, C1, hC1, rd1, hmScan, hwindow⟩

end Benchmarks.UniswapV4PoolManager

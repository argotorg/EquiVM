import Benchmarks.UniswapV4PoolManager.PoolSwapStepFillTrace
import Benchmarks.UniswapV4PoolManager.FixedAllocationGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapStepInitAW (aw step : UInt256) : UInt256 :=
  poolSwapStepFillAW (M aw (UInt256.ofNat 64) ⟨32⟩) step

theorem poolSwapStepInitTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id state step params ret packed remaining calculated fee protocol amount : UInt256}
    {zeroForOne : Bool} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hp : memLoad (UInt256.ofNat 64) mem = step) (hf : step.toNat+256 ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨19061⟩
      ([ret, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne),
        packed, poolSlot id, state]++R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ C+Cₘ (poolSwapStepInitAW aw step) ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨19155⟩
      ([remaining, ret, params, calculated, packed, fee, protocol, amount, UInt256.fromBool (!zeroForOne),
        step, poolSlot id, state]++R)
      (poolSwapStepInitMem mem evm id step zeroForOne) (poolSwapStepInitAW aw step) rdata evm.accountMap k' C' := by
  have rd1 := poolManagerBlocks.poolManager_block_19061_fallthrough
    (by change R.length+2+14 ≤ 1024; omega)
    (by rw [hp]; exact fixedAllocationGuard step (UInt256.ofNat solcMaxU64) 256 hf) h
  simp only [poolManagerBlocks.poolManager_block_19061_fallthrough_stack, hp] at rd1
  have hfit : step.toNat+256 < UInt256.size := by
    change step.toNat+256 < 2^256
    change step.toNat+256 ≤ 2^64-1 at hf
    omega
  obtain ⟨k2, C2, hc2, hp2, rd2⟩ := poolSwapStepFillTrace v (by change R.length+15 ≤ 1024; omega) hI hfit rd1
  refine ⟨k2, C2, by omega, ?_, rd2⟩
  dsimp only [poolSwapStepInitAW, memExpansionCost] at hp2 ⊢
  omega

end Benchmarks.UniswapV4PoolManager

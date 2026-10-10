import Benchmarks.UniswapV4PoolManager.PoolSwapCrossPrepareTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapCrossLiquidityTrace
import Benchmarks.UniswapV4PoolManager.TickCrossTrace
import Benchmarks.UniswapV4PoolManager.TickCrossStatic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapCrossMemory (mem : ByteArray) (id state : UInt256) (s : PoolSwapStepWords)
    (evm : State) (zeroForOne : Bool) (liquidity : UInt256) : ByteArray :=
  (poolSwapCrossLiquidity evm id s zeroForOne liquidity).toByteArray.write
    0 (tickCrossMemory mem id s.tickNext) (state+UInt256.ofNat 64).toNat 32

def poolSwapCrossAW (aw step state : UInt256) : UInt256 :=
  M (M (M (M (M (M aw (step+UInt256.ofNat 224) ⟨32⟩) (step+UInt256.ofNat 32) ⟨32⟩)
    ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)) (state+UInt256.ofNat 64) ⟨32⟩

theorem poolSwapCrossTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw step state id liquidity tag x1 params remaining calculated fee protocol amount : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+22 ≤ 1024)
    (hI : evm.executionEnv = I) (htc : int24Canonical s.tickNext) (hlc : liquidity.toNat < 2^128)
    (hg : memLoad (step+UInt256.ofNat 224) mem = s.feeGrowthGlobal)
    (ht : memLoad (step+UInt256.ofNat 32) mem = s.tickNext)
    (hl : memLoad (state+UInt256.ofNat 64) (tickCrossMemory mem id s.tickNext) = liquidity)
    (h : RD (deployedRuntime v) I g s0 ⟨19984⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, poolSlot id, state] ++ R)
      mem aw rdata evm.accountMap k C) :
    if evm.executionEnv.perm = false then RDstatic (deployedRuntime v) g s0
    else if liquidityAddFits liquidity (EVM.signed (poolSwapCrossDelta zeroForOne (poolSwapCrossNet evm id s zeroForOne))) then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19904⟩
        ([tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, poolSlot id, state] ++ R)
        (poolSwapCrossMemory mem id state s evm zeroForOne liquidity) (poolSwapCrossAW aw step state) rdata
        (poolSwapCrossPost evm id s zeroForOne).accountMap k' C'
    else RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, hC1, rd1⟩ := poolSwapCrossPrepareTrace v zeroForOne hstack hI hg h
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact tickCrossStatic (by change R.length+3+18 ≤ 1024; omega) (by rwa [← hI]) rd1
  · rw [if_neg hp]
    have hperm : I.perm = true := by rw [← hI]; exact Bool.eq_true_of_not_eq_false hp
    have hclean : UInt256.signextend (UInt256.ofNat 2) s.tickNext = s.tickNext := (signextend24_eq_iff _).mpr htc
    obtain ⟨k2, C2, hC2, rd2⟩ := tickCrossTrace v (by change R.length+3+18 ≤ 1024; omega) hI hperm ht rd1
    rw [hclean] at rd2
    have hentry : (if UInt256.fromBool (!zeroForOne) = ⟨0⟩ then (⟨20104⟩ : UInt256) else ⟨20082⟩) =
        (if zeroForOne then ⟨20104⟩ else ⟨20082⟩) := by cases zeroForOne <;> decide
    rw [hentry] at rd2
    have htail := poolSwapCrossLiquidityTrace v zeroForOne (by omega) hlc (tickCrossNet_fits ..) hl rd2
    by_cases hfit : liquidityAddFits liquidity (EVM.signed (poolSwapCrossDelta zeroForOne (poolSwapCrossNet evm id s zeroForOne)))
    · rw [if_pos hfit]
      dsimp only [poolSwapCrossNet] at hfit
      rw [if_pos hfit] at htail
      obtain ⟨k3, C3, hC3, rd3⟩ := htail
      exact ⟨k3, C3, (hC1.trans hC2).trans hC3, rd3⟩
    · rw [if_neg hfit]
      dsimp only [poolSwapCrossNet] at hfit
      rw [if_neg hfit] at htail
      exact htail

end Benchmarks.UniswapV4PoolManager

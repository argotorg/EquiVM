import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingSource
import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingMemory
import Benchmarks.UniswapV4PoolManager.PoolSwapAmountTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapAccountingMemory (mem : ByteArray) (step state id : UInt256) (evm : State)
    (s : PoolSwapStepWords) (r : PoolSwapResultWords) (fee protocol : UInt256) (zeroForOne : Bool) : ByteArray :=
  poolSwapTickMemory
    (poolSwapGrowthMemory (poolSwapProtocolMemory mem step s fee protocol) step
      (poolSwapProtocolStep s fee protocol) r.liquidity)
    id state evm (poolSwapAccountingStep s r fee protocol) r zeroForOne

def poolSwapAccountingAW (aw step state specified : UInt256) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (fee protocol : UInt256) : UInt256 :=
  poolSwapTickAW (poolSwapGrowthAW (poolSwapProtocolAW (poolSwapAmountAW aw step specified) step fee protocol)
    step state r.liquidity) step state (poolSwapAccountingStep s r fee protocol) r

theorem poolSwapAccountingTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {aw step state params id remaining calculated tag x1 fee protocol amount : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : PoolSwapMemoryView mem step state params s r p)
    (hfc : fee.toNat < 2^24) (hpc : protocol.toNat < 2^16) (hlc : r.liquidity.toNat < 2^128)
    (htc : int24Canonical s.tickNext) (hprice : r.price.toNat < 2^160)
    (hnc : s.priceNext.toNat < 2^160) (hsc : s.priceStart.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 (if 0 < EVM.signed p.amountSpecified then ⟨19740⟩ else ⟨20320⟩)
      ([remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
        step, poolSlot id, state] ++ R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19964⟩
        ([tag, x1, params, poolSwapRemainingAfter s p.amountSpecified remaining,
          poolSwapCalculatedAfter s p.amountSpecified calculated, fee, protocol,
          poolSwapProtocolAmount s fee protocol amount, UInt256.fromBool (!p.zeroForOne), step, poolSlot id, state] ++ R)
        (poolSwapAccountingMemory mem step state id evm s r fee protocol p.zeroForOne)
        (poolSwapAccountingAW aw step state p.amountSpecified s r fee protocol)
        rdata post.accountMap k' C') (fun _ _ => False)
      (poolSwapAccountingResult f evm id s r p remaining calculated fee protocol amount) := by
  have hamount := poolSwapAmountTrace (R := poolSlot id :: state :: R) v
    (by change R.length+2+15 ≤ 1024; omega) hm.amountIn hm.amountOut hm.feeAmount h
  unfold poolSwapAccountingResult
  by_cases hfit : poolSwapAmountFits s p.amountSpecified calculated
  · rw [if_pos hfit] at hamount ⊢
    obtain ⟨k1, C1, hC1, rd1⟩ := hamount
    have hm1 := hm.protocol fee protocol
    obtain ⟨k2, C2, hC2, rd2⟩ := poolSwapFeeTrace v (by omega) hfc hpc hlc
      hm.amountIn hm.feeAmount hm1.liquidity hm1.feeAmount hm1.growth rd1
    have hm2 := hm1.growth_step
    have he := poolSwapAccountingStep_fields s r fee protocol
    have htick := poolSwapTickTrace
      (f := poolSwapAccountingFrame f s r p.amountSpecified remaining calculated fee protocol amount)
      (s := poolSwapAccountingStep s r fee protocol) v p.zeroForOne hstack hI
      (by rw [he.1]; exact htc) hlc hprice (by rw [he.2.1]; exact hnc) (by rw [he.2.2]; exact hsc)
      hm2.price hm2.priceNext hm2.priceStart hm2.initialized hm2.growth hm2.tickNext
      (hm2.cross_hash id).liquidity (hm2.cross evm id p.zeroForOne).tickNext rd2
    apply blockResultTrace_mono htick
    intro ff post _ hnormal
    obtain ⟨k3, C3, hC3, rd3⟩ := hnormal
    exact ⟨k3, C3, (hC1.trans hC2).trans hC3, rd3⟩
  · rw [if_neg hfit] at hamount ⊢
    exact hamount

theorem PoolSwapMemoryView.accounting {mem : ByteArray} {step state params : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    (h : PoolSwapMemoryView mem step state params s r p)
    (evm : State) (id fee protocol : UInt256) :
    PoolSwapMemoryView (poolSwapAccountingMemory mem step state id evm s r fee protocol p.zeroForOne)
      step state params (poolSwapAccountingStep s r fee protocol)
      (poolSwapTickResultWords evm id (poolSwapAccountingStep s r fee protocol) r p.zeroForOne) p :=
  ((h.protocol fee protocol).growth_step).tick_update evm id p.zeroForOne

end Benchmarks.UniswapV4PoolManager

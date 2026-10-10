import Benchmarks.UniswapV3.Pool.TickUpdateTrace
import Benchmarks.UniswapV3.Pool.TickUpdateRawState
import Benchmarks.UniswapV3.Pool.TickUpdateMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateMaskedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (time maximum : UInt256)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20795⟩ (tickUpdateWords (a.withRaw time maximum) ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.Fits)
    (ht : UInt256.land time (UInt256.ofNat (2 ^ 32 - 1)) = a.time)
    (hmax : uint128Word maximum = a.maxLiquidity) (hm : HeapMemory mem aw p)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 25 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta) ∨
    (liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta ∧
      ((RDrev (deployedRuntime v) g s0 ∧
        ¬ tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat) ∨
       (tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat ∧
        ((RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
         (ee.perm = true ∧
          ((RDrev (deployedRuntime v) g s0 ∧
            ¬ safeCast128Valid (tickUpdateNetResult a evm a.upper)) ∨
           (safeCast128Valid (tickUpdateNetResult a evm a.upper) ∧ ∃ σ' k' C',
            SourceState s0 ee σ' (tickUpdateFinalState a evm) ∧
            RD (deployedRuntime v) ee g s0 ret ((tickUpdateFlipped a evm).toUInt256 :: R)
              (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) aw rdata σ' k' C'))))))) := by
  have h := tickUpdateRawX (v := v) (a.withRaw time maximum) evm hs rd
    (hfit.traceFits.withRaw time maximum) hret hov
  simp only [tickUpdateNetResult_withRaw a evm time maximum _ ht,
    tickUpdateFinalState_withRaw a evm time maximum ht, tickUpdateMemoryWords_eq hm.active] at h
  simpa only [tickUpdateGrossAfter, tickUpdateGrossBefore, tickUpdateFlipped,
    TickUpdateArgs.withRaw, hmax] using h

end Benchmarks.UniswapV3.Pool

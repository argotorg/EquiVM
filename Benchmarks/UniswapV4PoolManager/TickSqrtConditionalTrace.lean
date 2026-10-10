import Benchmarks.UniswapV4PoolManager.TickSqrtWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickSqrtConditionalTrace {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw pc absTick price mask factor : UInt256} {σ : AccountMap}
    (stack : UInt256 → List UInt256)
    (hzero : UInt256.land absTick mask = ⟨0⟩ → ∃ k C,
      RD code I g s0 pc (stack price) mem aw rdata σ k C)
    (hnonzero : UInt256.land absTick mask ≠ ⟨0⟩ → ∃ k C,
      RD code I g s0 pc (stack (UInt256.shiftRight (UInt256.mul price factor) (UInt256.ofNat 128)))
        mem aw rdata σ k C) :
    ∃ k C, RD code I g s0 pc (stack (tickSqrtStage absTick price mask factor)) mem aw rdata σ k C := by
  by_cases hn : UInt256.land absTick mask ≠ ⟨0⟩
  · simpa only [tickSqrtStage, if_pos hn] using hnonzero hn
  · simpa only [tickSqrtStage, if_neg hn] using hzero (not_not.mp hn)

end Benchmarks.UniswapV4PoolManager

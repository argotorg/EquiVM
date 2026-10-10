import Benchmarks.UniswapV3.Pool.TickUpdateBranchTrace
import Benchmarks.UniswapV3.Pool.TickUpdateWriteTrace
import Benchmarks.UniswapV3.Pool.TickUpdateStaticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateFirstWriteStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (tickUpdateFirstWritePC a evm)
      (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 20 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  by_cases hz : tickUpdateGrossBefore a evm = 0
  · by_cases ht : a.tick ≤ a.current
    · simp only [tickUpdateFirstWritePC, if_pos hz, if_pos ht] at rd
      exact tickUpdateOutsideStaticX (v := v) rd hp (by change R.length + 5 + 13 ≤ 1024; omega)
    · simp only [tickUpdateFirstWritePC, if_pos hz, if_neg ht] at rd
      exact tickUpdateInitializedStaticX (v := v) rd hp
        (by change R.length + 13 + 7 ≤ 1024; omega)
  · simp only [tickUpdateFirstWritePC, if_neg hz] at rd
    exact tickUpdateGrossStaticX (v := v) rd hp (by change R.length + 13 + 7 ≤ 1024; omega)

theorem tickUpdateInitializeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 (tickUpdateFirstWritePC a evm)
      (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.TraceFits) (hp : ee.perm = true) (hov : R.length + 22 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (tickUpdateInitializedState a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨21130⟩
        (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ' k' C' := by
  by_cases hz : tickUpdateGrossBefore a evm = 0
  · by_cases ht : a.tick ≤ a.current
    · simp only [tickUpdateFirstWritePC, if_pos hz, if_pos ht] at rd
      obtain ⟨k1, C1, r1⟩ := tickUpdateOutsideX (v := v) a rd hfit hp hov
      have hs1 := SourceState.tickUpdateOutside hs a
      obtain ⟨k2, C2, r2⟩ := tickUpdateInitializedX (v := v) a.tick r1 hp
        (by change R.length + 13 + 7 ≤ 1024; omega)
      refine ⟨_, k2, C2, ?_, r2⟩
      simpa only [tickUpdateInitializedState, if_pos hz, if_pos ht] using
        SourceState.tickHistory hs1 a.tick .initialized ⟨1⟩
    · simp only [tickUpdateFirstWritePC, if_pos hz, if_neg ht] at rd
      obtain ⟨k1, C1, r1⟩ := tickUpdateInitializedX (v := v) a.tick rd hp
        (by change R.length + 13 + 7 ≤ 1024; omega)
      refine ⟨_, k1, C1, ?_, r1⟩
      simpa only [tickUpdateInitializedState, if_pos hz, if_neg ht] using
        SourceState.tickHistory hs a.tick .initialized ⟨1⟩
  · simp only [tickUpdateFirstWritePC, if_neg hz] at rd
    exact ⟨σ, k, C, by simpa only [tickUpdateInitializedState, if_neg hz] using hs, rd⟩

theorem tickUpdateStoresX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 (tickUpdateFirstWritePC a evm)
      (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.TraceFits) (hp : ee.perm = true) (hov : R.length + 22 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (tickUpdateGrossState a evm) ∧
      RD (deployedRuntime v) ee g s0 (if a.upper then ⟨21203⟩ else ⟨21161⟩)
        (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ' k' C' := by
  obtain ⟨σ1, k1, C1, hs1, r1⟩ := tickUpdateInitializeX (v := v) a evm hs rd hfit hp hov
  obtain ⟨k2, C2, r2⟩ := tickUpdateGrossX (v := v) a r1 hp (by omega)
  exact ⟨_, k2, C2, SourceState.tickLiquidity hs1 a.tick false
    (EVM.wordOfInt (tickUpdateGrossAfter a evm)), r2⟩

end Benchmarks.UniswapV3.Pool

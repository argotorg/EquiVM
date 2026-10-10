import Benchmarks.UniswapV3.Pool.TickUpdateCheckedTrace
import Benchmarks.UniswapV3.Pool.TickUpdateInitializeTrace
import Benchmarks.UniswapV3.Pool.TickUpdateFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20795⟩ (tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.TraceFits)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 25 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta) ∨
    (liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta ∧
      ((RDrev (deployedRuntime v) g s0 ∧
        ¬ tickUpdateGrossAfter a evm ≤ Int.ofNat (uint128Word a.maxLiquidity).toNat) ∨
       (tickUpdateGrossAfter a evm ≤ Int.ofNat (uint128Word a.maxLiquidity).toNat ∧
        ((RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
         (ee.perm = true ∧
          ((RDrev (deployedRuntime v) g s0 ∧
            ¬ safeCast128Valid (tickUpdateNetResult a evm a.upper)) ∨
           (safeCast128Valid (tickUpdateNetResult a evm a.upper) ∧ ∃ σ' k' C',
            SourceState s0 ee σ' (tickUpdateFinalState a evm) ∧
            RD (deployedRuntime v) ee g s0 ret ((tickUpdateFlipped a evm).toUInt256 :: R)
              (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) (tickUpdateMemoryWords aw) rdata σ' k' C'))))))) := by
  rcases tickUpdateCheckedRawX (v := v) a evm hs rd hfit hov with hb | ⟨hv, hm⟩
  · exact Or.inl hb
  · refine Or.inr ⟨hv, ?_⟩
    rcases hm with hb | ⟨hm, k1, C1, r1⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hm, ?_⟩
      cases hp : ee.perm
      · exact Or.inl ⟨tickUpdateFirstWriteStaticX (v := v) a evm r1 hp (by omega), rfl⟩
      · refine Or.inr ⟨rfl, ?_⟩
        obtain ⟨σ2, k2, C2, hs2, r2⟩ := tickUpdateStoresX (v := v) a evm hs r1 hfit hp (by omega)
        rcases tickUpdateNetMathX (v := v) a evm hs2 r2 hfit (by omega) with hb | ⟨hn, k3, C3, r3⟩
        · exact Or.inl hb
        · obtain ⟨σ4, k4, C4, hs4, r4⟩ :=
            tickUpdateFinishX (v := v) a evm hs2 r3 hn hp hret (by omega)
          exact Or.inr ⟨hn, σ4, k4, C4, hs4, r4⟩


theorem tickUpdateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20795⟩ (tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.Fits)
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
           (safeCast128Valid (tickUpdateNetResult a evm a.upper) ∧ ∃ σ' k' C' aw',
            SourceState s0 ee σ' (tickUpdateFinalState a evm) ∧
            RD (deployedRuntime v) ee g s0 ret ((tickUpdateFlipped a evm).toUInt256 :: R)
              (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) aw' rdata σ' k' C'))))))) := by
  have h := tickUpdateRawX (v := v) a evm hs rd hfit.traceFits hret hov
  rw [uint128Word_clean hfit.2.2.2.2.2.2] at h
  rcases h with hb | ⟨hv, hm⟩
  · exact Or.inl hb
  · refine Or.inr ⟨hv, ?_⟩
    rcases hm with hb | ⟨hm, hp⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hm, ?_⟩
      rcases hp with hb | ⟨hp, hn⟩
      · exact Or.inl hb
      · refine Or.inr ⟨hp, ?_⟩
        rcases hn with hb | ⟨hn, σ', k', C', hs', r'⟩
        · exact Or.inl hb
        · exact Or.inr ⟨hn, σ', k', C', _, hs', r'⟩

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.TickUpdateBranchTrace
import Benchmarks.UniswapV3.Pool.TickUpdateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateCheckedRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20795⟩ (tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.TraceFits) (hov : R.length + 25 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta) ∨
    (liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta ∧
      ((RDrev (deployedRuntime v) g s0 ∧
        ¬ tickUpdateGrossAfter a evm ≤ Int.ofNat (uint128Word a.maxLiquidity).toNat) ∨
       (tickUpdateGrossAfter a evm ≤ Int.ofNat (uint128Word a.maxLiquidity).toNat ∧ ∃ k' C',
        RD (deployedRuntime v) ee g s0 (tickUpdateFirstWritePC a evm)
          (tickUpdateWorkingWords a evm ++ ret :: R)
          (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) (tickUpdateMemoryWords aw) rdata σ k' C'))) := by
  have hb : Int.ofNat (tickGrossWord σ ee a.tick).toNat = tickUpdateGrossBefore a evm := by
    simp only [tickUpdateGrossBefore, hs.accounts, hs.env]
  have hw : tickGrossWord σ ee a.tick = EVM.wordOfInt (tickUpdateGrossBefore a evm) := by
    rw [tickUpdateGrossBefore_word, hs.accounts, hs.env]
  have hp := tickUpdateLiquidityRawX (v := v) a rd hfit hov
  dsimp only at hp
  rw [hb] at hp
  rcases hp with hrev | ⟨hv, k1, C1, r1⟩
  · exact Or.inl hrev
  · refine Or.inr ⟨hv, ?_⟩
    rw [hw] at r1
    rcases tickUpdateMaxRawX (v := v) r1 (tickUpdateGrossAfter_word_lt a evm)
      (by change R.length + 11 + 10 ≤ 1024; omega) with ⟨hr, hm⟩ | ⟨hm, k2, C2, r2⟩
    · refine Or.inl ⟨hr, ?_⟩
      change ¬ (EVM.wordOfInt (tickUpdateGrossAfter a evm)).toNat ≤ (uint128Word a.maxLiquidity).toNat at hm
      rw [tickUpdateGrossAfter_toNat] at hm
      have ha := tickUpdateGrossAfter_bounds a evm
      change ¬ tickUpdateGrossAfter a evm ≤ ((uint128Word a.maxLiquidity).toNat : Int)
      omega
    · refine Or.inr ⟨?_, ?_⟩
      · change (EVM.wordOfInt (tickUpdateGrossAfter a evm)).toNat ≤ (uint128Word a.maxLiquidity).toNat at hm
        rw [tickUpdateGrossAfter_toNat] at hm
        have ha := tickUpdateGrossAfter_bounds a evm
        change tickUpdateGrossAfter a evm ≤ ((uint128Word a.maxLiquidity).toNat : Int)
        omega
      · obtain ⟨k3, C3, r3⟩ := tickUpdateFirstWriteX (v := v) a evm r2 hfit (by omega)
        exact ⟨k3, C3, r3⟩


theorem tickUpdateCheckedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20795⟩ (tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.Fits) (hov : R.length + 25 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta) ∨
    (liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta ∧
      ((RDrev (deployedRuntime v) g s0 ∧
        ¬ tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat) ∨
       (tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat ∧ ∃ k' C' aw',
        RD (deployedRuntime v) ee g s0 (tickUpdateFirstWritePC a evm)
          (tickUpdateWorkingWords a evm ++ ret :: R)
          (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) aw' rdata σ k' C'))) := by
  have h := tickUpdateCheckedRawX (v := v) a evm hs rd hfit.traceFits hov
  rw [uint128Word_clean hfit.2.2.2.2.2.2] at h
  rcases h with hb | ⟨hv, hm⟩
  · exact Or.inl hb
  · refine Or.inr ⟨hv, ?_⟩
    rcases hm with hb | ⟨hm, k', C', r'⟩
    · exact Or.inl hb
    · exact Or.inr ⟨hm, k', C', _, r'⟩

end Benchmarks.UniswapV3.Pool

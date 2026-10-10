import Benchmarks.UniswapV3.Pool.TickUpdateNetEntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateNetResult_bounds (a : TickUpdateArgs) (evm : EVM.State) (subtract : Bool) :
    -(2 ^ 255 : Int) ≤ tickUpdateNetResult a evm subtract ∧
      tickUpdateNetResult a evm subtract < 2 ^ 255 := by
  have hb := normalizeSint_bounds ⟨256, by decide⟩
    (if subtract then tickUpdateNetBefore a evm - a.delta else tickUpdateNetBefore a evm + a.delta)
  have hp : Int.ofNat (EVM.twoPow ((⟨256, by decide⟩ : ABI.BitWidth).val - 1)) =
      (2 ^ 255 : Int) := by norm_num [EVM.twoPow]
  rw [hp] at hb
  exact hb

theorem tickUpdateNetMathX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (tickUpdateGrossState a evm))
    (rd : RD (deployedRuntime v) ee g s0 (if a.upper then ⟨21203⟩ else ⟨21161⟩)
      (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.TraceFits) (hov : R.length + 24 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ safeCast128Valid (tickUpdateNetResult a evm a.upper)) ∨
    (safeCast128Valid (tickUpdateNetResult a evm a.upper) ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨21236⟩
        (EVM.wordOfInt (tickUpdateNetResult a evm a.upper) ::
          tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k' C') := by
  obtain ⟨k1, C1, r1⟩ := tickUpdateNetEntryX (v := v) a evm hs rd hfit (by omega)
  have hnb := tickUpdateNetBefore_bounds a evm
  have hdb := hfit.2.2.1
  rcases safeSignedMathX (v := v) a.upper (tickUpdateNetBefore a evm) a.delta r1
    (by omega) (by omega) (by omega) (by omega)
    (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
    (by change R.length + 17 + 7 ≤ 1024; omega) with ⟨_, hbad⟩ | ⟨_, k2, C2, r2⟩
  · exact False.elim (hbad (tickUpdateNetMathValid a evm a.upper hdb.1 hdb.2))
  · have r3 := uniswapV3Pool_block_21193 (immWords := wordsOf (immStore v))
      (by change R.length + 18 + 1 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r2
    have hrb := tickUpdateNetResult_bounds a evm a.upper
    rcases safeCast128X (v := v) (tickUpdateNetResult a evm a.upper) r3 hrb.1 hrb.2
      (by cases a.upper <;> rw [uniswapV3PoolPatchedValidJumps v] <;> native_decide)
      (by change R.length + 16 + 5 ≤ 1024; omega) with hrev | ⟨hv, k4, C4, r4⟩
    · exact Or.inl hrev
    · refine Or.inr ⟨hv, ?_⟩
      cases hu : a.upper
      · simp only [tickUpdateNetReturnPC, hu, Bool.false_eq_true, if_false] at r4
        have r5 := uniswapV3Pool_block_21198 (immWords := wordsOf (immStore v))
          (by change R.length + 17 + 1 ≤ 1024; omega)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r4
        exact ⟨_, _, by simpa only [hu] using r5⟩
      · simp only [tickUpdateNetReturnPC, hu, if_true] at r4
        exact ⟨_, _, by simpa only [hu] using r4⟩

end Benchmarks.UniswapV3.Pool

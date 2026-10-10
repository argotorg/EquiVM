import Benchmarks.UniswapV3.Pool.BurnOwedStorage
import Benchmarks.UniswapV3.Pool.BurnFinishSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem burnOwedStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (key : UInt256) (a0 a1 : Int) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9776⟩
      (EVM.wordOfInt a1 :: EVM.wordOfInt a0 :: solcMappingSlot ⟨7⟩ key ::
        burnAmount a1 :: burnAmount a0 :: R) mem aw rdata σ k C)
    (hperm : ee.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (burnOwedState key a0 a1 evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨9833⟩
        (EVM.wordOfInt a1 :: EVM.wordOfInt a0 :: solcMappingSlot ⟨7⟩ key ::
          burnAmount a1 :: burnAmount a0 :: R) mem aw rdata σ' k' C' := by
  obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_9776 (immWords := wordsOf (immStore v)) hov hperm rd
  simp only [solcMask128] at rr
  simp only [solcShift128] at rr
  rw [← burnOwedWord_evm] at rr
  exact ⟨_, kr, Cr, SourceState.burnOwed hs key a0 a1, rr⟩

theorem burnOwedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (key : UInt256) (a0 a1 : Int) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9770⟩
      ((burnHasAmounts a0 a1).toUInt256 :: EVM.wordOfInt a1 :: EVM.wordOfInt a0 ::
        solcMappingSlot ⟨7⟩ key :: burnAmount a1 :: burnAmount a0 :: R) mem aw rdata σ k C)
    (hperm : ee.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (burnFinalState key a0 a1 evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨9833⟩
        (EVM.wordOfInt a1 :: EVM.wordOfInt a0 :: solcMappingSlot ⟨7⟩ key ::
          burnAmount a1 :: burnAmount a0 :: R) mem aw rdata σ' k' C' := by
  cases hh : burnHasAmounts a0 a1
  · rw [hh] at rd
    have rr := uniswapV3Pool_block_9770_taken (immWords := wordsOf (immStore v))
      (by change R.length + 5 + 2 ≤ 1024; omega) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [burnFinalState, hh, Bool.false_eq_true, if_false]
    exact ⟨σ, _, _, hs, rr⟩
  · rw [hh] at rd
    have rr := uniswapV3Pool_block_9770_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 5 + 2 ≤ 1024; omega) (by rfl) rd
    simp only [burnFinalState, hh, if_true]
    exact burnOwedStoreX (v := v) key a0 a1 evm hs rr hperm hov

end Benchmarks.UniswapV3.Pool

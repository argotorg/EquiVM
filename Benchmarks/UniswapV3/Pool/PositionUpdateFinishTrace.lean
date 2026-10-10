import Benchmarks.UniswapV3.Pool.PositionUpdateGrowthTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem positionUpdateOwedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (positionUpdateGrowthState a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨21898⟩
      (positionUpdateWorkingWords a evm p ++ ret :: R) mem aw rdata σ k C)
    (hp : ee.perm = true) (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', SourceState s0 ee (positionUpdateOwedMap a evm σ ee)
        (positionUpdateOwedState a evm
          (positionUpdateOwedState a evm (positionUpdateGrowthState a evm) false) true) ∧
      RD (deployedRuntime v) ee g s0 ⟨21954⟩ (positionUpdateWorkingWords a evm p ++ ret :: R)
        mem aw rdata (positionUpdateOwedMap a evm σ ee) k' C' := by
  simp only [positionUpdateWorkingWords, List.cons_append, List.nil_append] at rd
  obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_21898 (immWords := wordsOf (immStore v))
    (by evm_ov) hp rd
  simp only [solcMask128] at rr
  simp only [solcShift128] at rr
  refine ⟨kr, Cr, SourceState.positionUpdateOwedPair hs a evm, ?_⟩
  exact rr

theorem positionUpdateFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (positionUpdateGrowthState a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨21892⟩
      ((positionUpdateHasFees a evm).toUInt256 :: positionUpdateWorkingWords a evm p ++ ret :: R)
      mem aw rdata σ k C)
    (hp : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 15 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (positionUpdateFinalState a evm) ∧
      RD (deployedRuntime v) ee g s0 ret R mem aw rdata σ' k' C' := by
  cases hf : positionUpdateHasFees a evm
  · rw [hf] at rd
    have r1 := uniswapV3Pool_block_21892_taken (immWords := wordsOf (immStore v))
      (by change R.length + 9 + 2 ≤ 1024; omega) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_21892_taken_stack, positionUpdateWorkingWords,
      List.cons_append, List.nil_append] at r1
    have r2 := uniswapV3Pool_block_21954 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r1
    simp only [positionUpdateFinalState, hf, Bool.false_eq_true, if_false]
    exact ⟨_, _, _, hs, r2⟩
  · rw [hf] at rd
    have r1 := uniswapV3Pool_block_21892_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 9 + 2 ≤ 1024; omega) (by rfl) rd
    obtain ⟨k2, C2, hs2, r2⟩ := positionUpdateOwedX (v := v) a evm hs r1 hp hov
    simp only [positionUpdateWorkingWords, List.cons_append, List.nil_append] at r2
    have r3 := uniswapV3Pool_block_21954 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r2
    simp only [positionUpdateFinalState, hf, if_true]
    exact ⟨_, _, _, hs2, r3⟩

end Benchmarks.UniswapV3.Pool

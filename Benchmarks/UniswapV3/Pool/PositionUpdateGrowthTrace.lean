import Benchmarks.UniswapV3.Pool.PositionUpdateBranchTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem doubleIsZero_wordPositive (word : UInt256) :
    UInt256.isZero (UInt256.isZero word) = (decide (0 < word.toNat)).toUInt256 := by
  by_cases hz : word = ⟨0⟩
  · rw [hz]
    rfl
  · have hp : 0 < word.toNat := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    rw [isZero_eq_zero_of_ne hz, decide_eq_true hp]
    rfl

theorem gtZero_wordPositive (word : UInt256) :
    UInt256.gt word (UInt256.ofNat 0) = (decide (0 < word.toNat)).toUInt256 := by
  by_cases hp : 0 < word.toNat
  · rw [ugt_one (a := word) (b := UInt256.ofNat 0) hp, decide_eq_true hp]
    rfl
  · rw [ugt_zero (a := word) (b := UInt256.ofNat 0) (Nat.le_of_not_gt hp), decide_eq_false hp]
    rfl

theorem positionUpdateFirstFee_flag (a : PositionUpdateArgs) (evm : EVM.State) :
    UInt256.isZero (UInt256.isZero (UInt256.land (positionUpdateFeeRaw a evm false)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) =
      (decide (0 < (positionUpdateOwed a evm false).toNat)).toUInt256 := by
  rw [solcMask128, u256_land_comm]
  exact doubleIsZero_wordPositive _

theorem positionUpdateSecondFee_flag (a : PositionUpdateArgs) (evm : EVM.State) :
    UInt256.gt (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1)) (positionUpdateFeeRaw a evm true)) (UInt256.ofNat 0) =
      (decide (0 < (positionUpdateOwed a evm true).toNat)).toUInt256 := by
  rw [solcMask128]
  exact gtZero_wordPositive _

theorem positionUpdateGrowthX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (positionUpdateLiquidityState a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨21846⟩
      (positionUpdateWorkingWords a evm p ++ ret :: R) mem aw rdata σ k C)
    (hp : ee.perm = true) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', SourceState s0 ee (positionUpdateGrowthMap a σ ee) (positionUpdateGrowthState a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨21892⟩
        ((positionUpdateHasFees a evm).toUInt256 :: positionUpdateWorkingWords a evm p ++ ret :: R)
        mem aw rdata (positionUpdateGrowthMap a σ ee) k' C' := by
  simp only [positionUpdateWorkingWords, List.cons_append, List.nil_append] at rd
  by_cases hf : 0 < (positionUpdateOwed a evm false).toNat
  · have hhas : positionUpdateHasFees a evm = true := by
      simp only [positionUpdateHasFees, decide_eq_true hf, Bool.true_or]
    obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_21846_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hp (by rw [positionUpdateFirstFee_flag a evm, decide_eq_true hf]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨kr, Cr, SourceState.positionUpdateGrowth a hs, ?_⟩
    simpa only [uniswapV3Pool_block_21846_taken_stack, positionUpdateFirstFee_flag a evm,
      decide_eq_true hf, hhas, positionUpdateWorkingWords, List.cons_append, List.nil_append,
      positionUpdateGrowthMap] using rr
  · obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_21846_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hp (by rw [positionUpdateFirstFee_flag a evm, decide_eq_false hf]; rfl) rd
    simp only [uniswapV3Pool_block_21846_fallthrough_stack] at rr
    have rf := uniswapV3Pool_block_21878 (immWords := wordsOf (immStore v)) (by evm_ov) rr
    simp only [uniswapV3Pool_block_21878_stack, positionUpdateSecondFee_flag a evm] at rf
    have hhas : positionUpdateHasFees a evm = decide (0 < (positionUpdateOwed a evm true).toNat) := by
      simp only [positionUpdateHasFees, decide_eq_false hf, Bool.false_or]
    rw [hhas]
    exact ⟨_, _, SourceState.positionUpdateGrowth a hs, rf⟩

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.PositionUpdateWords
import Benchmarks.UniswapV3.Pool.PositionUpdateStorage
import Benchmarks.UniswapV3.Pool.PositionUpdateStaticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def positionUpdateWorkingWords (a : PositionUpdateArgs) (evm : EVM.State) (p : UInt256) : List UInt256 :=
  [positionUpdateFeeRaw a evm true, positionUpdateFeeRaw a evm false,
    EVM.wordOfInt (positionUpdateLiquidityNext a evm), p, a.growth1, a.growth0,
    EVM.wordOfInt a.delta, solcMappingSlot ⟨7⟩ a.key]

def positionUpdateFirstWritePC (a : PositionUpdateArgs) : UInt256 :=
  if a.delta = 0 then ⟨21846⟩ else ⟨21821⟩

theorem positionUpdateFirstWriteX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21807⟩
      (positionUpdateFeeRaw a evm true :: ⟨0⟩ :: positionUpdateFeeRaw a evm false ::
        EVM.wordOfInt (positionUpdateLiquidityNext a evm) :: p :: a.growth1 :: a.growth0 ::
        EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R)
      mem aw rdata σ k C)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (positionUpdateFirstWritePC a)
      (positionUpdateWorkingWords a evm p ++ ret :: R) mem aw rdata σ k' C' := by
  by_cases hz : a.delta = 0
  · have r1 := uniswapV3Pool_block_21807_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [positionUpdateDelta_word a hdlo hdhi, hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_21807_taken_stack,
      positionUpdateFirstWritePC, if_pos hz, positionUpdateWorkingWords, List.cons_append,
      List.nil_append] using r1⟩
  · have hw : EVM.wordOfInt a.delta ≠ ⟨0⟩ := fun h ↦ hz
      ((wordOfInt_zero_iff_signed a.delta (by omega) (by omega)).mp h)
    have hc : UInt256.eq (UInt256.ofNat 0) (EVM.wordOfInt a.delta) = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ hw (uInt256_eq_one_eq h).symm)
    have r1 := uniswapV3Pool_block_21807_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [positionUpdateDelta_word a hdlo hdhi]; exact hc) rd
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_21807_fallthrough_stack,
      positionUpdateFirstWritePC, if_neg hz, positionUpdateWorkingWords, List.cons_append,
      List.nil_append] using r1⟩

theorem positionUpdateFirstWriteStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (positionUpdateFirstWritePC a)
      (positionUpdateWorkingWords a evm p ++ ret :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 13 ≤ 1024) : RDstatic (deployedRuntime v) g s0 := by
  by_cases hz : a.delta = 0
  · simp only [positionUpdateFirstWritePC, if_pos hz, positionUpdateWorkingWords,
      List.cons_append, List.nil_append] at rd
    exact positionUpdateGrowthStaticX (v := v) rd hp (by evm_ov)
  · simp only [positionUpdateFirstWritePC, if_neg hz, positionUpdateWorkingWords,
      List.cons_append, List.nil_append] at rd
    exact positionUpdateLiquidityStaticX (v := v) rd hp (by evm_ov)

theorem positionUpdateLiquidityStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 (positionUpdateFirstWritePC a)
      (positionUpdateWorkingWords a evm p ++ ret :: R) mem aw rdata σ k C)
    (hp : ee.perm = true) (hov : R.length + 13 ≤ 1024) :
    ∃ σ' k' C', SourceState s0 ee σ' (positionUpdateLiquidityState a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨21846⟩ (positionUpdateWorkingWords a evm p ++ ret :: R)
        mem aw rdata σ' k' C' := by
  by_cases hz : a.delta = 0
  · simp only [positionUpdateFirstWritePC, if_pos hz] at rd
    simp only [positionUpdateLiquidityState, if_pos hz]
    exact ⟨σ, k, C, hs, rd⟩
  · simp only [positionUpdateFirstWritePC, if_neg hz, positionUpdateWorkingWords,
      List.cons_append, List.nil_append] at rd
    obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_21821 (immWords := wordsOf (immStore v))
      (by evm_ov) hp rd
    simp only [solcMask128, u256_land_comm (EVM.wordOfInt (positionUpdateLiquidityNext a evm)),
      u256_land_comm (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1)))] at rr
    refine ⟨positionLiquidityMap σ ee a.key (EVM.wordOfInt (positionUpdateLiquidityNext a evm)),
      kr, Cr, ?_, rr⟩
    simpa only [positionUpdateLiquidityState, if_neg hz] using
      SourceState.positionLiquidity hs a.key (EVM.wordOfInt (positionUpdateLiquidityNext a evm))

end Benchmarks.UniswapV3.Pool

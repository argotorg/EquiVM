import Benchmarks.UniswapV3.Pool.MintRepaymentSource
import Benchmarks.UniswapV3.Pool.Balance
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def mintRepayEntryPC (second : Bool) : UInt256 := if second then ⟨6203⟩ else ⟨6116⟩
def mintRepayBalanceReturn (second : Bool) : UInt256 := if second then ⟨6217⟩ else ⟨6137⟩
def mintRepayComparePC (second : Bool) : UInt256 := if second then ⟨6227⟩ else ⟨6147⟩
def mintRepayNextPC (second : Bool) : UInt256 := if second then ⟨6283⟩ else ⟨6203⟩

def mintRepayWords (before0 before1 amount0 amount1 : UInt256) (R : List UInt256) : List UInt256 :=
  before1 :: before0 :: amount1 :: amount0 :: amount1 :: amount0 :: R

def mintRepayEntryWords (second : Bool) (junk0 junk1 junk2 junk3 : UInt256)
    (before0 before1 amount0 amount1 : UInt256) (R : List UInt256) : List UInt256 :=
  if second then mintRepayWords before0 before1 amount0 amount1 R else
    junk0 :: junk1 :: junk2 :: junk3 :: mintRepayWords before0 before1 amount0 amount1 R

theorem mintRepayEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw before0 before1 amount0 amount1 junk0 junk1 junk2 junk3 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (mintRepayEntryPC second)
      (mintRepayEntryWords second junk0 junk1 junk2 junk3 before0 before1 amount0 amount1 R)
      mem aw rdata σ k C) (hov : R.length + 10 ≤ 1024) :
    ((if second then amount1 else amount0) = ⟨0⟩ ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 (mintRepayNextPC second)
        (mintRepayWords before0 before1 amount0 amount1 R) mem aw rdata σ k' C') ∨
    (0 < (if second then amount1 else amount0).toNat ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 (balanceEntry second)
        (mintRepayBalanceReturn second :: mintRepayWords before0 before1 amount0 amount1 R)
        mem aw rdata σ k' C') := by
  cases second with
  | false =>
    by_cases hz : amount0 = ⟨0⟩
    · have rr := uniswapV3Pool_block_6116_taken (immWords := wordsOf (immStore v)) hov
        (by rw [hz]; decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact Or.inl ⟨hz, _, _, rr⟩
    · have hp := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
      have r1 := uniswapV3Pool_block_6116_fallthrough (immWords := wordsOf (immStore v)) hov
        (by rw [ugt_one (a := amount0) (b := UInt256.ofNat 0) hp]; rfl) rd
      simp only [uniswapV3Pool_block_6116_fallthrough_stack] at r1
      have r2 := uniswapV3Pool_block_6130 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      exact Or.inr ⟨hp, _, _, r2⟩
  | true =>
    by_cases hz : amount1 = ⟨0⟩
    · have rr := uniswapV3Pool_block_6203_taken (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 7 ≤ 1024; omega) (by rw [hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact Or.inl ⟨hz, _, _, rr⟩
    · have hp := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
      have r1 := uniswapV3Pool_block_6203_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 7 ≤ 1024; omega) (isZero_eq_zero_of_ne hz) rd
      have r2 := uniswapV3Pool_block_6210 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      exact Or.inr ⟨hp, _, _, r2⟩

theorem mintRepayAddEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw before0 before1 amount0 amount1 after : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (mintRepayBalanceReturn second)
      (after :: mintRepayWords before0 before1 amount0 amount1 R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15885⟩
      ((if second then amount1 else amount0) :: (if second then before1 else before0) ::
        mintRepayComparePC second :: after :: mintRepayWords before0 before1 amount0 amount1 R)
      mem aw rdata σ k' C' := by
  cases second with
  | false =>
    exact ⟨_, _, uniswapV3Pool_block_6137 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
  | true =>
    exact ⟨_, _, uniswapV3Pool_block_6217 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 10 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩

end Benchmarks.UniswapV3.Pool

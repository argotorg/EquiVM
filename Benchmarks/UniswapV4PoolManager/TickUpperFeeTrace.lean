import Benchmarks.UniswapV4PoolManager.TickLowerStoreTrace
import Benchmarks.UniswapV4PoolManager.TickFeeGuardTrace
import Benchmarks.UniswapV4PoolManager.TickGrossWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickUpperNetInput (id tick packed x5 x6 x7 ptr x9 x10 : UInt256) (delta : Int)
    (R : List UInt256) : List UInt256 :=
  packed :: EVM.wordOfInt (tickGrossAfterInt packed delta) :: tickSlot id (EVM.signed tick) ::
    UInt256.fromBool (tickFlipped packed delta) :: x5 :: x6 :: x7 :: ptr :: x9 :: x10 :: tick :: EVM.wordOfInt delta :: R

theorem tickUpperFeeExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick packed x5 x6 x7 ptr x9 x10 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hf : liquidityAddFits (tickGrossWord packed) delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7100⟩
      (EVM.wordOfInt (tickGrossAfterInt packed delta) :: tickUpperLiquidityTail id tick packed x5 x6 x7 ptr x9 x10 delta R)
      mem aw rdata evm.accountMap k C) :
    if tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false then
      RDstatic (deployedRuntime v) g s0 else ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨7132⟩ (tickUpperNetInput id tick packed x5 x6 x7 ptr x9 x10 delta R)
        mem (if Int.ofNat (tickGrossWord packed).toNat = 0 then M aw (UInt256.ofNat 128) ⟨32⟩ else aw) rdata (tickFeesPost evm id packed (EVM.signed tick)).accountMap k' C' := by
  have hclean : UInt256.land (EVM.wordOfInt (tickGrossAfterInt packed delta))
      (UInt256.ofNat 340282366920938463463374607431768211455) = EVM.wordOfInt (tickGrossAfterInt packed delta) :=
    u256LandMaskCleanOfToNat _ _ rfl (tickGrossAfter_bound hf)
  have hflip := tickFlipped_compiled hf
  dsimp only [tickUpperLiquidityTail] at h
  by_cases hz : Int.ofNat (tickGrossWord packed).toNat = 0
  · rw [if_pos hz]
    have hzw : tickGrossWord packed = ⟨0⟩ := by
      apply uint256_toNat_eq_zero
      simp only [Int.ofNat_eq_natCast] at hz
      omega
    have rd1 := poolManagerBlocks.poolManager_block_7100_taken
      (by simp only [List.length_cons]; omega) (by rw [hzw]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_7100_taken_stack, hclean, hflip] at rd1
    have hfees := tickUpperFeeGuardExactTrace v (by simp only [List.length_cons]; omega) hI hm rd1
    by_cases hc : EVM.signed tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id))
    · rw [if_pos hc] at hfees
      simp only [tickFeesNeeded, hz, hc, true_and, and_self, tickFeesPost, if_true]
      exact hfees
    · rw [if_neg hc] at hfees
      simp only [tickFeesNeeded, hz, hc, true_and, false_and, tickFeesPost, if_false]
      exact hfees
  · rw [if_neg hz]
    have hzw : tickGrossWord packed ≠ ⟨0⟩ := by intro hh; apply hz; rw [hh]; rfl
    have rd1 := poolManagerBlocks.poolManager_block_7100_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hzw) h
    simp only [poolManagerBlocks.poolManager_block_7100_fallthrough_stack, hclean, hflip] at rd1
    simp only [tickFeesNeeded, hz, false_and, tickFeesPost, if_false]
    exact ⟨_, _, rd1⟩

theorem tickUpperFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick packed x5 x6 x7 ptr x9 x10 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hf : liquidityAddFits (tickGrossWord packed) delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7100⟩
      (EVM.wordOfInt (tickGrossAfterInt packed delta) :: tickUpperLiquidityTail id tick packed x5 x6 x7 ptr x9 x10 delta R)
      mem aw rdata evm.accountMap k C) :
    if tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false then
      RDstatic (deployedRuntime v) g s0 else ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨7132⟩ (tickUpperNetInput id tick packed x5 x6 x7 ptr x9 x10 delta R)
        mem aw' rdata (tickFeesPost evm id packed (EVM.signed tick)).accountMap k' C' := by
  have hr := tickUpperFeeExactTrace v hstack hI hm hf h
  split_ifs at hr ⊢
  all_goals first | exact hr | (obtain ⟨k', C', rd⟩ := hr; exact ⟨_, k', C', rd⟩)

end Benchmarks.UniswapV4PoolManager

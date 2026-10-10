import Benchmarks.UniswapV4PoolManager.PoolSwapDeltaBranchesTrace
import Benchmarks.UniswapV4PoolManager.WordAbsolute
import Benchmarks.UniswapV4PoolManager.SafeCast256Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapDeltaBranchWord (zeroForOne : Bool) (specified : UInt256) :
    UInt256.eq (UInt256.slt specified ⟨0⟩) (UInt256.isZero (UInt256.fromBool (!zeroForOne))) =
      UInt256.fromBool (!(poolSwapCalculatedFirst zeroForOne specified)) := by
  have he : 2^255 ≤ specified.toNat ↔ EVM.signed specified < 0 := by
    rw [signedNegative_iff]
    omega
  rw [UInt256.slt, wordSltZeroBool]
  simp only [he]
  cases zeroForOne <;> cases hneg : decide (EVM.signed specified < 0) <;>
    simp only [poolSwapCalculatedFirst, hneg] <;> rfl

def poolSwapDeltaAW (aw params : UInt256) (calculatedFirst : Bool) : UInt256 :=
  if calculatedFirst then M (M aw params ⟨32⟩) params ⟨32⟩ else M aw params ⟨32⟩

theorem poolSwapDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw specified remaining params calculated state fee amount ret : UInt256}
    {zeroForOne : Bool} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+11 ≤ 1024)
    (hm : memLoad params mem = specified) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨21716⟩
      ([UInt256.fromBool (!zeroForOne), remaining, params, calculated, state, fee, amount, ret]++R)
      mem aw rdata σ k C) :
    let cf := poolSwapCalculatedFirst zeroForOne specified
    if poolSwapDeltaFits cf specified remaining calculated then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret
        ([state, fee, amount, poolSwapDeltaWord cf specified remaining calculated]++R)
        mem (poolSwapDeltaAW aw params cf) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  cases hc : poolSwapCalculatedFirst zeroForOne specified
  · simp only [poolSwapDeltaAW, Bool.false_eq_true, if_false]
    have rd1 := poolManagerBlocks.poolManager_block_21716_taken
      (by change R.length+5+6 ≤ 1024; omega)
      (by rw [hm, poolSwapDeltaBranchWord, hc]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_21716_taken_stack, hm] at rd1
    have ht := poolSwapDeltaSpecifiedTrace v (by change R.length+4+7 ≤ 1024; omega) rd1
    by_cases hf : poolSwapDeltaFits false specified remaining calculated
    · rw [if_pos hf] at ht ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := ht
      have rd3 := poolManagerBlocks.poolManager_block_21750 (by change R.length+7 ≤ 1024; omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_21750_stack] at rd3
      exact ⟨_, _, by omega, rd3⟩
    · rw [if_neg hf] at ht ⊢
      exact ht
  · simp only [poolSwapDeltaAW, if_true]
    have rd1 := poolManagerBlocks.poolManager_block_21716_fallthrough
      (by change R.length+5+6 ≤ 1024; omega)
      (by rw [hm, poolSwapDeltaBranchWord, hc]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_21716_fallthrough_stack, hm] at rd1
    have ht := poolSwapDeltaCalculatedTrace v (by change R.length+4+7 ≤ 1024; omega) hm rd1
    by_cases hf : poolSwapDeltaFits true specified remaining calculated
    · rw [if_pos hf] at ht ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := ht
      have rd3 := poolManagerBlocks.poolManager_block_21750 (by change R.length+7 ≤ 1024; omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_21750_stack] at rd3
      exact ⟨_, _, by omega, rd3⟩
    · rw [if_neg hf] at ht ⊢
      exact ht

end Benchmarks.UniswapV4PoolManager

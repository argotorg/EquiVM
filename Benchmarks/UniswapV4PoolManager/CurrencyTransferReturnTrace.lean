import Benchmarks.UniswapV4PoolManager.CurrencyTransferSource
import Benchmarks.UniswapV4PoolManager.CurrencyTransferMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_037

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def transferReturnGuard (mem out : ByteArray) (z : Bool) : UInt256 :=
  UInt256.isZero (UInt256.land (UInt256.lor
    (UInt256.land (UInt256.eq (memLoad ⟨0⟩ mem) ⟨1⟩) (UInt256.gt (UInt256.ofNat out.size) ⟨31⟩))
    (UInt256.isZero (UInt256.ofNat out.size))) (if z then ⟨1⟩ else ⟨0⟩))

theorem transferReturnGuard_eq {mem out : ByteArray} {z : Bool}
    (ho : out.size < UInt256.size)
    (hword : 32 ≤ out.size → memLoad ⟨0⟩ mem = returnedBalanceWord out) :
    transferReturnGuard mem out z = if z = true ∧ transferReturnValid out then ⟨0⟩ else ⟨1⟩ := by
  have hs := UInt256.toNat_ofNat_of_lt ho
  have hgt : UInt256.gt (UInt256.ofNat out.size) ⟨31⟩ =
      if 32 ≤ out.size then ⟨1⟩ else ⟨0⟩ := by
    by_cases hlo : 32 ≤ out.size
    · rw [if_pos hlo]
      exact ugt_one (by rw [hs]; change 31 < out.size; omega)
    · rw [if_neg hlo]
      exact ugt_zero (by rw [hs]; change out.size ≤ 31; omega)
  have hzero : UInt256.isZero (UInt256.ofNat out.size) =
      if out.size = 0 then ⟨1⟩ else ⟨0⟩ := by
    have he : UInt256.ofNat out.size = (⟨0⟩ : UInt256) ↔ out.size = 0 :=
      ⟨fun h => by have hh := congrArg UInt256.toNat h; simpa only [hs] using hh,
       fun h => by rw [h]; rfl⟩
    simp only [UInt256.isZero, UInt256.eq0, UInt256.fromBool, Bool.toUInt256, beq_iff_eq, he]
    split <;> rfl
  unfold transferReturnGuard
  rw [hgt, hzero]
  by_cases hlo : 32 ≤ out.size
  · rw [if_pos hlo, if_neg (by omega : out.size ≠ 0), hword hlo]
    by_cases hw : returnedBalanceWord out = ⟨1⟩ <;> cases z <;>
      simp only [UInt256.eq, UInt256.fromBool, hw, decide_true, decide_false, if_true, if_false,
        transferReturnValid, hlo, show out.size ≠ 0 by omega, false_or, true_and,
        and_self, Bool.false_eq_true, false_and] <;> decide
  · rw [if_neg hlo, u256_land_zero_right]
    by_cases hz : out.size = 0 <;> cases z <;>
      simp only [hz, if_true, if_false, transferReturnValid, hlo, false_and, or_false,
        Bool.false_eq_true, true_and, and_self, true_or] <;> decide

theorem currencyTransferTokenReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr currency ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256} {z : Bool}
    (P : ByteArray → Prop) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (ho : out.size < UInt256.size)
    (hword : 32 ≤ out.size → memLoad ⟨0⟩ mem = returnedBalanceWord out)
    (hm : P (currencyTransferCleanMemory mem ptr))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13122⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨64⟩ :: ⟨0⟩ :: ptr :: currency :: ret :: R)
      mem aw out σ k C) :
    (¬ (z = true ∧ transferReturnValid out) ∧ RDrev (deployedRuntime v) g s0) ∨
    (z = true ∧ transferReturnValid out ∧ ∃ mem' aw' k' C',
      P mem' ∧ RD (deployedRuntime v) I g s0 ret R mem' aw' out σ k' C') := by
  have hg := transferReturnGuard_eq (z := z) ho hword
  by_cases hgood : z = true ∧ transferReturnValid out
  · rw [if_pos hgood] at hg
    have rd1 := poolManagerBlocks.poolManager_block_13122_fallthrough (by simp; omega) hg h
    have rd2 := poolManagerBlocks.poolManager_block_13153 (by simp; omega) hret rd1
    exact .inr ⟨hgood.1, hgood.2, _, _, _, _, hm, rd2⟩
  · rw [if_neg hgood] at hg
    have rd1 := poolManagerBlocks.poolManager_block_13122_taken (by simp; omega)
      (by change transferReturnGuard mem out z ≠ ⟨0⟩; rw [hg]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_13155 (by simp; omega)
      (by rw [UInt256.toNat_ofNat_of_lt ho]; change 0 + out.size ≤ out.size; omega) rd1
    exact .inl ⟨hgood, rd2⟩

end Benchmarks.UniswapV4PoolManager

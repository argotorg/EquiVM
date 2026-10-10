import Benchmarks.UniswapV4PoolManager.PoolDonateSource
import Benchmarks.UniswapV4PoolManager.PoolDonateCastTrace
import Benchmarks.UniswapV4PoolManager.PoolDonateGrowthTrace
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolDonateTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id hook key src amount0 amount1 len junk j0 j1 : UInt256}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables)
    (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨10191⟩
      (j0 :: j1 :: hook :: key :: src :: amount1 :: amount0 :: len :: poolSlot id :: id :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
      values = some [.int (EVM.signed (poolDonateDelta amount0 amount1))] ∧
      ∃ j0' j1' k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨10284⟩
        (j0' :: j1' :: id :: hook :: key :: src :: amount1 :: amount0 :: len ::
          poolDonateDelta amount0 amount1 :: ⟨32⟩ :: junk :: R) mem aw rdata post.accountMap k' C')
      (poolDonateResult f evm id amount0 amount1) := by
  have ht := poolDonateCastTrace v hstack hI h
  unfold poolDonateResult
  by_cases hz : poolLiquidityWord evm id = ⟨0⟩
  · rw [if_pos hz] at ht ⊢
    exact ht
  rw [if_neg hz] at ht ⊢
  by_cases hfit : amount0.toNat < 2^127 ∧ amount1.toNat < 2^127
  swap
  · rw [if_neg hfit] at ht ⊢
    exact ht
  rw [if_pos hfit] at ht ⊢
  obtain ⟨k1, C1, hc1, rd1⟩ := ht
  have ht0 := poolDonateGrowth0Trace v hstack hI rd1
  rw [← hI] at ht0
  by_cases hs0 : amount0 ≠ ⟨0⟩ ∧ evm.executionEnv.perm = false
  · rw [if_pos hs0] at ht0
    rw [if_pos (show (amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false from
      ⟨Or.inl hs0.1, hs0.2⟩)]
    exact ht0
  rw [if_neg hs0] at ht0
  obtain ⟨k2, C2, hc2, rd2⟩ := ht0
  rw [hI] at rd2
  have hI1 : (poolDonateStep evm id false amount0 (poolLiquidityWord evm id)).executionEnv = I :=
    (poolDonateStep_executionEnv ..).trans hI
  have ht1 := poolDonateGrowth1Trace v (by omega) hI1 rd2
  rw [← hI] at ht1
  by_cases hs1 : amount1 ≠ ⟨0⟩ ∧ evm.executionEnv.perm = false
  · rw [if_pos hs1] at ht1
    rw [if_pos (show (amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false from
      ⟨Or.inr hs1.1, hs1.2⟩)]
    exact ht1
  rw [if_neg hs1] at ht1
  have hs : ¬((amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false) := by
    rintro ⟨h0 | h1, hp⟩
    · exact hs0 ⟨h0, hp⟩
    · exact hs1 ⟨h1, hp⟩
  rw [if_neg hs]
  obtain ⟨j0', j1', k3, C3, hc3, rd3⟩ := ht1
  rw [hI] at rd3
  exact ⟨(poolDonatePost_executionEnv ..).trans hI, poolDonatePost_σ₀ .., rfl,
    j0', j1', k3, C3, by omega, rd3⟩

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.AfterSwapSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_045
import Benchmarks.UniswapV4PoolManager.EntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def afterSwapEntryResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem rdata : ByteArray) (σ : AccountMap) (hook : AccountAddress)
    (keyPtr paramsPtr delta src len before ret : UInt256) (R : List UInt256) : Prop :=
  if I.source = hook then ∃ aw k C, Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: delta :: R) mem aw rdata σ k C
  else ∃ aw k C, Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 (if afterSwapActive hook then ⟨15936⟩ else ⟨15800⟩)
      (paramsPtr :: len :: src :: keyPtr :: accountWord hook :: EVM.wordOfInt (balanceDeltaAmount1 before) ::
        EVM.wordOfInt (balanceDeltaAmount0 before) :: delta :: ret :: paramsPtr :: R) mem aw rdata σ k C

theorem afterSwapEntryTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw keyPtr paramsPtr delta src len before ret : UInt256} {hook : AccountAddress}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024) (hpaid : Cₘ aw ≤ C+84)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15745⟩
      (accountWord hook :: keyPtr :: paramsPtr :: delta :: src :: len :: before :: ret :: R) mem aw rdata σ k C) :
    afterSwapEntryResult v I g s0 mem rdata σ hook keyPtr paramsPtr delta src len before ret R := by
  have hclean : UInt256.land (accountWord hook) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      accountWord hook := solcAddrMask_clean (accountWord_canonical hook)
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  by_cases hself : I.source = hook
  · rw [afterSwapEntryResult, if_pos hself]
    have rd1 := poolManager_block_15745_taken (by omega)
      (by
        rw [hclean]
        change UInt256.eq (accountWord I.source) (accountWord hook) ≠ UInt256.ofNat 0
        rw [heq.mp hself, u256_eq_refl]
        decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManager_block_16152 (by omega) hret rd1
    exact ⟨_, _, _, by omega, rd2⟩
  · rw [afterSwapEntryResult, if_neg hself]
    have rd1 := poolManager_block_15745_fallthrough (by omega)
      (by rw [hclean]; exact u256_eq_of_ne (fun he => hself (heq.mpr he))) h
    by_cases ha : afterSwapActive hook
    · rw [if_pos ha]
      have rd2 := poolManager_block_15782_taken hstack ha
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      refine ⟨aw, k+15+13, C+49+48, by omega, ?_⟩
      simpa only [balanceDeltaAmount0, balanceDeltaAmount1, wordOfInt_signed] using rd2
    · rw [if_neg ha]
      have hz : UInt256.land (accountWord hook) (UInt256.ofNat 64) = UInt256.ofNat 0 :=
        Classical.not_not.mp ha
      have rd2 := poolManager_block_15782_fallthrough hstack hz rd1
      refine ⟨aw, k+15+13, C+49+48, by omega, ?_⟩
      simpa only [balanceDeltaAmount0, balanceDeltaAmount1, wordOfInt_signed] using rd2

end Benchmarks.UniswapV4PoolManager

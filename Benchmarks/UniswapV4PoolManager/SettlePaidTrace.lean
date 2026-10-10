import Benchmarks.UniswapV4PoolManager.SettlePaidSource
import Benchmarks.UniswapV4PoolManager.AccountDeltaTrace
import Benchmarks.UniswapV4PoolManager.WordReturnTrace
import Benchmarks.UniswapV4PoolManager.Uint256ResultTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_037

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem settlePaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw paid currencyWord : UInt256} {recipient currency : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+12 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : UInt256.land currencyWord solcAddrMask = accountWord currency) (hm : WordReturnMemory mem)
    (h : RD (deployedRuntime v) I g s0 ⟨13427⟩
      (currencyWord :: accountWord recipient :: ⟨12705⟩ :: ⟨1954⟩ :: paid :: ⟨32⟩ :: R)
      mem aw rdata evm.accountMap k C) :
    uint256ResultTrace (deployedRuntime v) g s0 (settlePaidResult f evm recipient currency paid) := by
  rw [settlePaidResult, hI]
  have rdCast := poolManagerBlocks.poolManager_block_13427 (by change R.length+1+8 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hfit : paid.toNat < 2^127
  · rw [if_pos hfit]
    obtain ⟨k1, C1, rdAccount⟩ := uintToInt128Trace v (by change R.length+6+4 ≤ 1024; omega) hfit
      (by rw [deployedRuntime_jumps]; jump_dest) rdCast
    have rdDelta := poolManagerBlocks.poolManager_block_13436 (by change R.length+5+3 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdAccount
    change RD _ _ _ _ ⟨12528⟩
      (currencyWord :: paid :: accountWord recipient :: ⟨12705⟩ :: ⟨1954⟩ :: paid :: ⟨32⟩ :: R)
      _ _ _ _ _ _ at rdDelta
    have hlo : -(2^127 : Int) ≤ Int.ofNat paid.toNat := by simp only [Int.ofNat_eq_natCast]; omega
    have hhi : Int.ofNat paid.toNat < (2^127 : Int) := by simp only [Int.ofNat_eq_natCast]; omega
    have rdDelta' : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (currencyWord :: EVM.wordOfInt (Int.ofNat paid.toNat) :: accountWord recipient :: ⟨12705⟩ :: ⟨1954⟩ :: paid :: ⟨32⟩ :: R)
      mem aw rdata evm.accountMap (k1+4) (C1+15) := by simpa only [wordOfInt_ofNat_toNat] using rdDelta
    have ht := accountDeltaWordTrace v (by change R.length+3+9 ≤ 1024; omega) hI hc hlo hhi
      (by rw [deployedRuntime_jumps]; jump_dest) rdDelta'
    rw [accountDeltaTraceResult] at ht
    by_cases hz : Int.ofNat paid.toNat = 0
    · rw [if_pos hz] at ht ⊢
      obtain ⟨aw', k', C', rdReturn⟩ := ht
      have rdWord := poolManagerBlocks.poolManager_block_12705 (by simp; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdReturn
      exact ⟨paid, rfl, wordReturnTrace v (by omega) hm rdWord⟩
    · rw [if_neg hz] at ht ⊢
      generalize hsum : currencyDeltaValue evm recipient currency + Int.ofNat paid.toNat = next at ht ⊢
      by_cases hs : int256Fits next
      · rw [if_pos hs] at ht ⊢
        by_cases hp : I.perm = false
        · rw [if_pos hp] at ht ⊢
          exact ht
        · rw [if_neg hp] at ht ⊢
          obtain ⟨aw', k', C', rdReturn⟩ := ht
          have rdWord := poolManagerBlocks.poolManager_block_12705 (by simp; omega)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdReturn
          exact ⟨paid, rfl, wordReturnTrace v (by omega) (hm.hash (accountWord recipient) (accountWord currency)) rdWord⟩
      · rw [if_neg hs] at ht ⊢
        exact ht
  · rw [if_neg hfit]
    exact uintToInt128TraceReverts v (by change R.length+6+4 ≤ 1024; omega) hfit rdCast

end Benchmarks.UniswapV4PoolManager

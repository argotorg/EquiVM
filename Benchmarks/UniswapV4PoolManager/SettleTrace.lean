import Benchmarks.UniswapV4PoolManager.SettleSource
import Benchmarks.UniswapV4PoolManager.SettlePaidTrace
import Benchmarks.UniswapV4PoolManager.SettleResetTrace
import Benchmarks.UniswapV4PoolManager.CurrencyBalanceTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The shared `_settle` body, with the public single-word return continuation. -/
theorem settleFunctionTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw ptr : UInt256} {recipient : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (hr : f.locals.get? "recipient" = some (.address recipient))
    (hm : WordReturnMemory mem) (hptr : 96 ≤ ptr.toNat) (hfit : ptr.toNat+63 ≤ solcMaxU64)
    (hgap : ptr.toNat-mem.size < USize.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (h : RD (deployedRuntime v) I g s0 ⟨13357⟩
      (accountWord recipient :: ⟨1954⟩ :: ⟨32⟩ :: R) mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm settleFunction.body result ∧
      uint256ResultTrace (deployedRuntime v) g s0 result := by
  have hc := (syncedCurrency_word evm).symm
  by_cases hz : syncedCurrency evm = AccountAddress.ofNat 0
  · have hzero : UInt256.land (transientWord evm currencySlot) solcAddrMask = ⟨0⟩ :=
      hc.trans ((accountWord_eq_iff _ ⟨0⟩ (by decide)).1 hz)
    have rdNative := poolManagerBlocks.poolManager_block_13357_fallthrough (by change R.length+1+5 ≤ 1024; omega)
      (by change UInt256.land (codeOwnerTransientWord I evm.accountMap currencySlot) solcAddrMask = ⟨0⟩
          rw [← transientWord_accountMap hI]; exact hzero) h
    change RD _ _ _ _ ⟨13421⟩
      (accountWord recipient :: ⟨1954⟩ :: codeOwnerTransientWord I evm.accountMap currencySlot :: ⟨32⟩ :: R)
      _ _ _ _ _ _ at rdNative
    rw [← transientWord_accountMap hI] at rdNative
    have rdPaid := poolManagerBlocks.poolManager_block_13421 (by change R.length+1+5 ≤ 1024; omega) rdNative
    refine ⟨_, settleNativeBody hf hr hz, ?_⟩
    rw [hI]
    exact settlePaidTrace v (by omega) hI hc hm rdPaid
  · have hnword : UInt256.land (transientWord evm currencySlot) solcAddrMask ≠ ⟨0⟩ := by
      rw [hc]
      exact fun he => hz ((accountWord_eq_iff _ ⟨0⟩ (by decide)).2 he)
    have rdValue := poolManagerBlocks.poolManager_block_13357_taken (by change R.length+1+5 ≤ 1024; omega)
      (by change UInt256.land (codeOwnerTransientWord I evm.accountMap currencySlot) solcAddrMask ≠ ⟨0⟩
          rw [← transientWord_accountMap hI]; exact hnword)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ ⟨13442⟩
      (accountWord recipient :: ⟨1954⟩ :: codeOwnerTransientWord I evm.accountMap currencySlot :: ⟨32⟩ :: R)
      _ _ _ _ _ _ at rdValue
    rw [← transientWord_accountMap hI] at rdValue
    by_cases hv : I.weiValue = ⟨0⟩
    · have rdReserves := poolManagerBlocks.poolManager_block_13442_fallthrough (by simp; omega) hv rdValue
      have rdBalance := poolManagerBlocks.poolManager_block_13448 (by change R.length+1+9 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdReserves
      change RD _ _ _ _ ⟨14994⟩
        (transientWord evm currencySlot :: ⟨13497⟩ :: codeOwnerTransientWord I evm.accountMap reservesSlot ::
         ⟨13502⟩ :: accountWord recipient :: ⟨12705⟩ :: ⟨1954⟩ :: transientWord evm currencySlot :: ⟨32⟩ :: R)
        _ _ _ _ _ _ at rdBalance
      rw [← transientWord_accountMap hI] at rdBalance
      obtain ⟨evm', z, out, hcall, hI', _, ho, ht⟩ := currencyBalanceWordTrace v
        (by change R.length+7+10 ≤ 1024; omega) hc hI hσ0 hz hptr hfit hgap hfree
        (by rw [deployedRuntime_jumps]; jump_dest) rdBalance
      refine ⟨settleTokenResult f evm evm' recipient z out,
        settleTokenBody hf hr hz (by rw [hI]; exact hv) (lt_trans ho (by decide)) hcall, ?_⟩
      rw [settleTokenResult, hI']
      rcases ht with ⟨hbad, hrev⟩ | ⟨hztrue, hout, mem', aw', k', C', hmem', hfree', rdSub⟩
      · rw [if_neg hbad]
        exact hrev
      · rw [if_pos ⟨hztrue, hout⟩]
        have rdSubtract := poolManagerBlocks.poolManager_block_13497 (by simp; omega)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdSub
        by_cases hsub : (transientWord evm reservesSlot).toNat ≤ (returnedBalanceWord out).toNat
        · rw [if_pos hsub]
          obtain ⟨k2, C2, rdReset⟩ := checkedSubPass v (by change R.length+5+4 ≤ 1024; omega) hsub
            (by rw [deployedRuntime_jumps]; jump_dest) rdSubtract
          by_cases hp : I.perm = false
          · rw [if_pos hp]
            exact settleResetStaticTrace (by change R.length+1+7 ≤ 1024; omega) hp rdReset
          · rw [if_neg hp]
            have rdPaid := poolManagerBlocks.poolManager_block_13502 (by change R.length+1+7 ≤ 1024; omega)
              (Bool.eq_true_of_not_eq_false hp) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdReset
            have hpostI : (resetCurrencyPost evm').executionEnv = I :=
              (transientStore_executionEnv _ _ _ _).trans hI'
            have hpostMap : (resetCurrencyPost evm').accountMap = tstoreAccountMap I.codeOwner evm'.accountMap currencySlot ⟨0⟩ := by
              simp only [resetCurrencyPost, transientStore_accountMap, hI']
            change RD _ _ _ _ ⟨13427⟩
              (transientWord evm currencySlot :: accountWord recipient :: ⟨12705⟩ :: ⟨1954⟩ ::
               UInt256.sub (returnedBalanceWord out) (transientWord evm reservesSlot) :: ⟨32⟩ :: R)
              _ _ _ (tstoreAccountMap I.codeOwner evm'.accountMap currencySlot ⟨0⟩) _ _ at rdPaid
            rw [← hpostMap] at rdPaid
            exact settlePaidTrace v (by omega) hpostI hc (.of_inBounds hmem' hfree') rdPaid
        · rw [if_neg hsub]
          exact checkedSubReverts v (by change R.length+5+4 ≤ 1024; omega) (Nat.lt_of_not_ge hsub) rdSubtract
    · have rdRevert := poolManagerBlocks.poolManager_block_13442_taken (by simp; omega) hv
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdValue
      exact ⟨.reverted, settleValueReverts hf hz (by rw [hI]; exact hv),
        poolManagerBlocks.poolManager_block_13543 (by simp; omega) rdRevert⟩

end Benchmarks.UniswapV4PoolManager

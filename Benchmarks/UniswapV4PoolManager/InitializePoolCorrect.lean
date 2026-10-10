import Benchmarks.UniswapV4PoolManager.InitializePoolSource
import Benchmarks.UniswapV4PoolManager.InitializePoolTrace
import Benchmarks.UniswapV4PoolManager.InitializeFinishCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem initializePoolCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {key : PoolKeyWords} {price fee : UInt256} {old : Value}
    (v : PoolManagerImmutables) (hI : evm.executionEnv = I)
    (hf : f.contract = contract) (hc : PoolKeyCanonical key)
    (hprice : price.toNat < 2^160) (hfee : fee.toNat < 2^24)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (he : f.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)))
    (ht : f.locals.get? "tick" = some old) (hb : f.locals.get? "_pools" = none)
    (hr : initializePoolTraceResult v I g s0 evm key price fee) :
    ∃ result, ExecFuncBody config f evm (initializeTransition.body.drop 13) result ∧
      signedResultTrace ⟨24, by decide⟩ (deployedRuntime v) g s0 result := by
  unfold initializePoolTraceResult at hr
  by_cases hz : poolSqrtPriceWord evm (poolKeyId key) ≠ ⟨0⟩
  · rw [if_pos hz] at hr
    have hsrc := initializePoolSource (f := f) (evm := evm) (evm' := evm) (z := false) (out := .empty)
      hf hc hprice hfee hk hp he ht hb (fun _ hzero => (hz hzero).elim)
    rw [initializePoolResult, if_pos hz] at hsrc
    exact ⟨.reverted, hsrc, hr⟩
  · rw [if_neg hz] at hr
    cases hresult : tickPriceResult price with
    | none =>
      simp only [hresult] at hr
      have hsrc := initializePoolSource (f := f) (evm := evm) (evm' := evm) (z := false) (out := .empty)
        hf hc hprice hfee hk hp he ht hb (by intro tick _ hsome; rw [hresult] at hsome; contradiction)
      rw [initializePoolResult, if_neg hz, hresult] at hsrc
      exact ⟨.reverted, hsrc, hr⟩
    | some tick =>
      simp only [hresult] at hr
      by_cases hperm : I.perm = false
      · rw [if_pos hperm] at hr
        have hsrc := initializePoolSource (f := f) (evm := evm) (evm' := evm) (z := false) (out := .empty)
          hf hc hprice hfee hk hp he ht hb (by intro _ _ _ htrue; rw [hI, hperm] at htrue; contradiction)
        simp only [initializePoolResult, if_neg hz, hresult, hI, if_pos hperm] at hsrc
        exact ⟨.staticViolation, hsrc, hr⟩
      · rw [if_neg hperm] at hr
        obtain ⟨evm', z, out, hcall, _, _, _, htrace⟩ := hr
        have hcalls : ∀ tick', poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩ →
            tickPriceResult price = some tick' → evm.executionEnv.perm = true →
            hookEnabled evm.executionEnv.source (AccountAddress.ofNat key.hooks.toNat) ⟨4096⟩ →
            callViaEVM (poolInitializePost evm (poolKeyId key) price tick' fee)
              (AccountAddress.ofNat key.hooks.toNat) 0
              (afterInitializePayload evm.executionEnv.source key price tick') (z, evm', out) := by
          intro tick' _ hsome _ hen
          have heq : tick = tick' := Option.some.inj (hresult.symm.trans hsome)
          subst tick'
          simpa only [hI] using hcall (by simpa only [hI] using hen)
        have hsrc := initializePoolSource (f := f) (evm := evm) hf hc hprice hfee hk hp he ht hb hcalls
        refine ⟨_, hsrc, ?_⟩
        simp only [initializePoolResult, if_neg hz, hresult, hI, if_neg hperm]
        exact initializeFinishTrace v ((storageStore_executionEnv _ _ _ _).trans hI)
          (tickPriceResult_canonical hresult) htrace

end Benchmarks.UniswapV4PoolManager

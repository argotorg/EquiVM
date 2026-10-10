import Benchmarks.UniswapV4PoolManager.ModifyLiquidityHooksCorrect
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityValidationTrace
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityDecodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem modifyLiquidityBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {rdata : ByteArray} {aw src len junk : UInt256} {key : PoolKeyWords}
    {p : ModifyLiquidityWords} {k C : Nat} {R : List UInt256} {oldFees oldCaller : Value}
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (him : f.immutables = immStore v)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (he : f.locals.get? "feesAccrued" = some oldFees)
    (hcaller : f.locals.get? "callerDelta" = some oldCaller)
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (haw : aw.toNat ≤ 14) (hsrc : src.toNat+len.toNat ≤ I.calldata.size) (hlen : len.toNat ≤ solcMaxU64)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (h : RD (deployedRuntime v) I g s0 ⟨5394⟩
      ([len, src, ⟨160⟩, ⟨320⟩, junk] ++ R) (modifyLiquidityDecodeMemory key p) aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (modifyLiquidityTransition.body.drop 7) result ∧
      abiResultTrace modifyLiquidityTransition.returnType (deployedRuntime v) g s0 result := by
  have hkey := modifyLiquidityDecodeMemory_key key p
  have hs := modifyLiquidityValidationSource (evm := evm) v hf him hc hk
  have ht := modifyLiquidityValidationTrace v (by omega) hI hkey (by decide) haw h
  rw [modifyLiquidityValidationResult, hI] at hs
  rw [modifyLiquidityValidationTraceResult] at ht
  by_cases hlock : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hlock] at hs ht
    exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  rw [if_neg hlock] at hs ht
  by_cases hdelegate : I.codeOwner = v.original
  swap
  · rw [if_neg hdelegate] at hs ht
    exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  rw [if_pos hdelegate] at hs ht
  by_cases hinit : poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩
  · rw [if_pos hinit] at hs ht
    exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  rw [if_neg hinit] at hs ht
  obtain ⟨aw1, k1, C1, haw1, rd1⟩ := ht
  let vf := modifyLiquidityValidationFrame f key
  have hvf : vf.contract = contract := by
    simp only [vf, modifyLiquidityValidationFrame]
    exact hf
  have hkeep (name : Ident) (h0 : ("__c0" == name) = false) (h1 : ("__c1" == name) = false)
      (h2 : ("id" == name) = false) (h3 : ("__c3" == name) = false) (h4 : ("pool" == name) = false)
      (h5 : (modifyLiquidityCheckAlias == name) = false) (h6 : ("__c4" == name) = false) :
      vf.locals.get? name = f.locals.get? name :=
    (store_get_ne2 _ _ _ h5 h6).trans (store_get_ne5 _ _ _ _ _ _ h0 h1 h2 h3 h4)
  have hvk : vf.locals.get? "key" = some (poolKeyValue key) :=
    (hkeep "key" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hk
  have hvp : vf.locals.get? "params" = some (modifyLiquidityParamsValue p) :=
    (hkeep "params" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp
  have hvb : vf.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (hkeep "hookData" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
  have hve : vf.locals.get? "feesAccrued" = some oldFees :=
    (hkeep "feesAccrued" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans he
  have hvc : vf.locals.get? "callerDelta" = some oldCaller :=
    (hkeep "callerDelta" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcaller
  have hvi : vf.locals.get? "id" = some (wordBytes32Value (poolKeyId key)) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("__c3" == "id") = false)
      (by decide : ("pool" == "id") = false) (by decide : (modifyLiquidityCheckAlias == "id") = false)
      (by decide : ("__c4" == "id") = false)).trans (store_get_self _ _ _)
  have hvs : vf.locals.get? "pool" = some (poolRefValue (poolKeyId key)) :=
    (store_get_ne2 _ _ _ (by decide : (modifyLiquidityCheckAlias == "pool") = false)
      (by decide : ("__c4" == "pool") = false)).trans (store_get_self _ _ _)
  have hfree : memLoad (UInt256.ofNat 64) (poolLookupMemory (modifyLiquidityDecodeMemory key p) (poolKeyId key)) = ⟨448⟩ :=
    (poolLookupMemory_free _ (by rw [modifyLiquidityDecodeMemory_size]; decide)).trans (modifyLiquidityDecodeMemory_free key p)
  have hpaid : Cₘ aw1 ≤ C1+46 := by
    have hm := memoryCost_mono (b := ⟨14⟩) haw1
    have hc14 : Cₘ (⟨14⟩ : UInt256) = 42 := by decide +kernel
    rw [hc14] at hm
    omega
  rcases modifyLiquidityHooksCorrect (f := vf) (free := ⟨448⟩) (keyPtr := ⟨160⟩) (paramsPtr := ⟨320⟩)
      v hstack hI hσ0 hvf hvk hvp hvi hvs hvb hve hvc
      hc hl hu (hkey.poolLookup (poolKeyId key) (by decide))
      ((modifyLiquidityDecodeMemory_params key p).poolLookup (poolKeyId key) (by decide))
      (poolLookupMemory_slotView _ _) (by decide) (by decide) (by decide) (by decide) (by decide)
      hfree hsrc hlen hgas hpaid rd1 with hog | ⟨result, hbody, htrace⟩
  · exact .inl hog
  · exact .inr ⟨result, execBlock_append hs hbody, htrace⟩

end Benchmarks.UniswapV4PoolManager

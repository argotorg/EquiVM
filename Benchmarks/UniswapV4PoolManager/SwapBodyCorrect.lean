import Benchmarks.UniswapV4PoolManager.SwapBeforeCorrect
import Benchmarks.UniswapV4PoolManager.SwapValidationTrace
import Benchmarks.UniswapV4PoolManager.SwapDecodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {rdata : ByteArray} {aw src len junk : UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    {oldDelta : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+49 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (him : f.immutables = immStore v)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hd : f.locals.get? "swapDelta" = some oldDelta)
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (haw : aw.toNat ≤ 13) (hsrc : src.toNat+len.toNat ≤ I.calldata.size) (hcd : I.calldata.size < 2^255)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (h : RD (deployedRuntime v) I g s0 ⟨1488⟩
      ([len, src, ⟨160⟩, ⟨384⟩, ⟨352⟩, ⟨320⟩, junk]++R)
      (swapDecodeMemory key p) aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (swapTransition.body.drop 6) result ∧
      abiResultTrace swapTransition.returnType (deployedRuntime v) g s0 result := by
  have hkey := swapDecodeMemory_key key p
  have hparams := swapDecodeMemory_params key p
  have hs := swapValidationSource (evm := evm) v hf him hc hk hp
  have ht := swapValidationTrace (paramsPtr := UInt256.ofNat 320) v (by omega) hI hkey hparams
    (by decide) (by decide) haw h
  rw [swapValidationResult, hI] at hs
  rw [swapValidationTraceResult] at ht
  by_cases hlock : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hlock] at hs ht
    exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  rw [if_neg hlock] at hs ht
  by_cases hdelegate : I.codeOwner = v.original
  swap
  · rw [if_neg hdelegate] at hs ht
    exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  rw [if_pos hdelegate] at hs ht
  by_cases hzero : p.amountSpecified = ⟨0⟩
  · rw [if_pos hzero] at hs ht
    exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  rw [if_neg hzero] at hs ht
  by_cases hinit : poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩
  · rw [if_pos hinit] at hs ht
    exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  rw [if_neg hinit] at hs ht
  obtain ⟨aw1, k1, C1, haw1, rd1⟩ := ht
  let vf := swapValidationFrame f key
  have hvf : vf.contract = contract := by dsimp only [vf, swapValidationFrame]; exact hf
  have hkeep (name : Ident) (h0 : ("__c0" == name) = false) (h1 : ("__c1" == name) = false)
      (h2 : ("id" == name) = false) (h3 : ("__c3" == name) = false) (h4 : ("pool" == name) = false)
      (h5 : (swapCheckAlias == name) = false) (h6 : ("__c4" == name) = false) :
      vf.locals.get? name = f.locals.get? name :=
    (store_get_ne2 _ _ _ h5 h6).trans (store_get_ne5 _ _ _ _ _ _ h0 h1 h2 h3 h4)
  have hvk : vf.locals.get? "key" = some (poolKeyValue key) :=
    (hkeep "key" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hk
  have hvp : vf.locals.get? "params" = some (swapParamsValue p) :=
    (hkeep "params" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp
  have hvb : vf.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (hkeep "hookData" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
  have hvd : vf.locals.get? "swapDelta" = some oldDelta :=
    (hkeep "swapDelta" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hd
  have hvi : vf.locals.get? "id" = some (wordBytes32Value (poolKeyId key)) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("__c3" == "id") = false)
      (by decide : ("pool" == "id") = false) (by decide : (swapCheckAlias == "id") = false)
      (by decide : ("__c4" == "id") = false)).trans (store_get_self _ _ _)
  have hvs : vf.locals.get? "pool" = some (poolRefValue (poolKeyId key)) :=
    (store_get_ne2 _ _ _ (by decide : (swapCheckAlias == "pool") = false)
      (by decide : ("__c4" == "pool") = false)).trans (store_get_self _ _ _)
  have hfree : memLoad (UInt256.ofNat 64) (twoWordHashMem (poolKeyId key) ⟨6⟩ (swapDecodeMemory key p)) = ⟨416⟩ :=
    (twoWordHashMem_free _ _ (by rw [swapDecodeMemory_size]; decide)).trans (swapDecodeMemory_free key p)
  have hpaid : Cₘ aw1 ≤ C1+120 := by
    have hm := memoryCost_mono (b := ⟨13⟩) haw1
    have hc13 : Cₘ (⟨13⟩ : UInt256) = 39 := by decide +kernel
    rw [hc13] at hm
    omega
  rcases swapBeforeCorrect (f := vf) (free := ⟨416⟩) (keyPtr := ⟨160⟩) (paramsPtr := ⟨320⟩)
      v hstack hI hσ0 hvf hvk hvp hvd hvb hvs hvi
      (hkey.twoWordHash (poolKeyId key) ⟨6⟩ (by decide))
      (hparams.twoWordHash (poolKeyId key) ⟨6⟩ (by decide)) hc hl
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hsrc hcd hgas hpaid hfree rd1 with hog | ⟨result, hbody, htrace⟩
  · exact .inl hog
  · exact .inr ⟨result, execBlock_append hs hbody, htrace⟩

end Benchmarks.UniswapV4PoolManager

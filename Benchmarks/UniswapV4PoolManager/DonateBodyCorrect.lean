import Benchmarks.UniswapV4PoolManager.DonateBeforeCorrect
import Benchmarks.UniswapV4PoolManager.DonateValidationTrace
import Benchmarks.UniswapV4PoolManager.DonatePreludeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {rdata : ByteArray} {aw src len amount0 amount1 junk : UInt256} {key : PoolKeyWords}
    {oldDelta : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+33 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (him : f.immutables = immStore v)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hd : f.locals.get? "delta" = some oldDelta)
    (hc : PoolKeyCanonical key)
    (haw : aw.toNat ≤ 10) (hsrc : src.toNat+len.toNat ≤ I.calldata.size) (hcd : I.calldata.size < 2^255)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (h : RD (deployedRuntime v) I g s0 ⟨10076⟩
      ([len, src, amount0, ⟨160⟩, amount1, junk]++R)
      (poolKeyMemory key) aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (donateTransition.body.drop 5) result ∧
      abiResultTrace donateTransition.returnType (deployedRuntime v) g s0 result := by
  have hkey := poolKeyMemory_view key
  have hs := donateValidationSource (evm := evm) v hf him hc hk
  have ht := donateValidationTrace v (by omega) hI hkey (by decide) haw h
  rw [donateValidationResult, hI] at hs
  rw [donateValidationTraceResult] at ht
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
  let vf := donateValidationFrame f key
  have hvf : vf.contract = contract := by dsimp only [vf, donateValidationFrame]; exact hf
  have hkeep (name : Ident) (h0 : ("__c0" == name) = false) (h1 : ("__c1" == name) = false)
      (h2 : ("poolId" == name) = false) (h3 : ("__c3" == name) = false) (h4 : ("pool" == name) = false)
      (h5 : (donateCheckAlias == name) = false) (h6 : ("__c4" == name) = false) :
      vf.locals.get? name = f.locals.get? name :=
    (store_get_ne2 _ _ _ h5 h6).trans (store_get_ne5 _ _ _ _ _ _ h0 h1 h2 h3 h4)
  have hvk : vf.locals.get? "key" = some (poolKeyValue key) :=
    (hkeep "key" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hk
  have hv0 : vf.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)) :=
    (hkeep "amount0" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0
  have hv1 : vf.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)) :=
    (hkeep "amount1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1
  have hvb : vf.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (hkeep "hookData" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
  have hvd : vf.locals.get? "delta" = some oldDelta :=
    (hkeep "delta" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hd
  have hvi : vf.locals.get? "poolId" = some (wordBytes32Value (poolKeyId key)) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("__c3" == "poolId") = false)
      (by decide : ("pool" == "poolId") = false) (by decide : (donateCheckAlias == "poolId") = false)
      (by decide : ("__c4" == "poolId") = false)).trans (store_get_self _ _ _)
  have hvs : vf.locals.get? "pool" = some (poolRefValue (poolKeyId key)) :=
    (store_get_ne2 _ _ _ (by decide : (donateCheckAlias == "pool") = false)
      (by decide : ("__c4" == "pool") = false)).trans (store_get_self _ _ _)
  have hfree : memLoad (UInt256.ofNat 64) (twoWordHashMem (poolKeyId key) ⟨6⟩ (poolKeyMemory key)) = ⟨320⟩ :=
    (twoWordHashMem_free _ _ (by rw [poolKeyMemory_size]; decide)).trans (poolKeyMemory_load64 key)
  have hpaid : Cₘ aw1 ≤ C1+49 := by
    have hm := memoryCost_mono (b := ⟨10⟩) haw1
    have hc13 : Cₘ (⟨10⟩ : UInt256) = 30 := by decide +kernel
    rw [hc13] at hm
    omega
  rcases donateBeforeCorrect (f := vf) (free := ⟨320⟩) (keyPtr := ⟨160⟩)
      v hstack hI hσ0 hvf hvk hv0 hv1 hvd hvb hvs hvi
      (hkey.twoWordHash (poolKeyId key) ⟨6⟩ (by decide))
      hc (by decide) (by decide) (by decide)
      hsrc hcd hgas hpaid hfree rd1 with hog | ⟨result, hbody, htrace⟩
  · exact .inl hog
  · exact .inr ⟨result, execBlock_append hs hbody, htrace⟩

end Benchmarks.UniswapV4PoolManager

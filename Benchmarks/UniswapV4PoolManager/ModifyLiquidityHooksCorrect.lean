import Benchmarks.UniswapV4PoolManager.ModifyLiquidityPoolFinishCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem modifyLiquidityHooksCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len id junk : UInt256}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {k C : Nat} {R : List UInt256} {oldFees oldCaller : Value}
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hs : f.locals.get? "pool" = some (poolRefValue id))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (he : f.locals.get? "feesAccrued" = some oldFees)
    (hcaller : f.locals.get? "callerDelta" = some oldCaller)
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hslot : MemorySlice mem 128 (wordBytes [poolSlot id]))
    (hkl : 160 ≤ keyPtr.toNat) (hpl : 160 ≤ paramsPtr.toNat)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hfb : free.toNat+4000 ≤ solcMaxU64) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size) (hlen : len.toNat ≤ solcMaxU64)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+46)
    (h : RD (deployedRuntime v) I g s0 ⟨5474⟩
      ([src, paramsPtr, len, keyPtr, id, junk] ++ R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (modifyLiquidityTransition.body.drop 15) result ∧
      abiResultTrace modifyLiquidityTransition.returnType (deployedRuntime v) g s0 result := by
  rcases modifyLiquidityBeforeCorrect v (by omega) hI hσ0 hf hk hp hb hc hl hu hkey hparams hslot
      hkl hpl hkb hpb hfb hfree hsrc hlen hgas hpaid h with hog | ⟨beforeResult, hbefore, ht⟩
  · exact .inl hog
  apply execBlock_trace_append (execBlock_singleton hbefore) ht
  intro ff post _ hh
  obtain ⟨rfl, hbeforetrace⟩ := hh
  let bf : Frame := {f with locals := f.locals.insert "__c5" .unit}
  have hbf : bf.contract = contract := hf
  have hkeep (name : Ident) (hn : ("__c5" == name) = false) : bf.locals.get? name = f.locals.get? name :=
    store_get_ne _ _ hn
  have hbk : bf.locals.get? "key" = some (poolKeyValue key) := (hkeep "key" (by decide)).trans hk
  have hbp : bf.locals.get? "params" = some (modifyLiquidityParamsValue p) := (hkeep "params" (by decide)).trans hp
  have hbs : bf.locals.get? "pool" = some (poolRefValue id) := (hkeep "pool" (by decide)).trans hs
  obtain ⟨poolResult, hpool, hpooltrace⟩ := modifyLiquidityPoolCorrect (f := bf) v hstack hbf hbk hbp hbs
    hc.2.2.2.1 hl hu hkl hpl hbeforetrace
  apply execBlock_trace_append hpool hpooltrace
  intro ff state _ hh
  exact modifyLiquidityPoolFinishCorrect v hstack hbf hbk hbp
    ((hkeep "id" (by decide)).trans hi) ((hkeep "hookData" (by decide)).trans hb)
    ((hkeep "feesAccrued" (by decide)).trans he) ((hkeep "callerDelta" (by decide)).trans hcaller)
    hc hl hu hkl hlen hsrc hgas hh

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.ModifyLiquidityPoolPreludeSource
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityPoolPrepareTrace
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityBeforeCorrect
import Benchmarks.UniswapV4PoolManager.PoolModifyCall
import Benchmarks.UniswapV4PoolManager.PoolModifyPaidTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyPreserveMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityPoolReturnFrame (f : Frame) (id : UInt256) (p : ModifyLiquidityWords)
    (principal fees : UInt256) : Frame :=
  let pre := modifyLiquidityPoolPreludeFrame f id p
  {pre with locals := pre.locals.insert "__c7" (.tuple [.int (EVM.signed principal), .int (EVM.signed fees)])}

def modifyLiquidityAfterPoolTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (before : Frame) (key : PoolKeyWords) (p : ModifyLiquidityWords)
    (keyPtr paramsPtr src len id junk : UInt256) (R : List UInt256) (f : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ ∃ principal fees mem rdata free,
    f = modifyLiquidityPoolReturnFrame before id p principal fees ∧
    PoolKeyView mem keyPtr key ∧ MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)) ∧
    keyPtr.toNat+160 ≤ free.toNat ∧ paramsPtr.toNat+128 ≤ free.toNat ∧
    free.toNat+3600 ≤ solcMaxU64 ∧ memLoad (UInt256.ofNat 64) mem = free ∧ ∃ j0 j1 j2 aw k C, Cₘ aw ≤ C ∧
      RD (deployedRuntime v) I g s0 ⟨6046⟩
        (j0 :: j1 :: j2 :: principal :: poolModifyAmountRest fees paramsPtr id src len keyPtr junk R)
        mem aw rdata post.accountMap k C

theorem modifyLiquidityPoolCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {key : PoolKeyWords} {p : ModifyLiquidityWords}
    {keyPtr paramsPtr src len id junk : UInt256} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hs : f.locals.get? "pool" = some (poolRefValue id))
    (hc : int24Canonical key.tickSpacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkl : 160 ≤ keyPtr.toNat) (hpl : 160 ≤ paramsPtr.toNat)
    (h : modifyLiquidityAfterBeforeTrace v I g s0 evm key p keyPtr paramsPtr src len id junk R) :
    ∃ result, ExecBlock config f evm ((modifyLiquidityTransition.body.drop 16).take 4) result ∧
      blockResultTrace (deployedRuntime v) g s0
        (modifyLiquidityAfterPoolTrace v I g s0 f key p keyPtr paramsPtr src len id junk R)
        (fun _ _ => False) result := by
  obtain ⟨hI, hσ0, mem, rdata, free, hkey, hparams, hslot, hkb, hpb, hfb, hfree,
    x0, x1, aw, k, C, hpaid, rd⟩ := h
  have hsource := modifyLiquidityPoolPreludeSource (evm := evm) hf hp hs
  have hprepare := modifyLiquidityPoolPrepareTrace v (by omega) hc hl hu hkey hparams hpb
    (by omega) hfree hpaid rd
  by_cases hd : signedFits ⟨128, by decide⟩ (EVM.signed p.delta)
  · rw [if_pos hd] at hsource hprepare
    obtain ⟨aw1, k1, C1, hpaid1, rd1⟩ := hprepare
    let pre := modifyLiquidityPoolPreludeFrame f id p
    let pp := modifyLiquidityPoolParams I.source key p
    have hfpre : pre.contract = contract := hf
    have hkpre : pre.locals.get? "key" = some (poolKeyValue key) :=
      (store_get_ne3 _ _ _ _ (by decide : ("principalDelta" == "key") = false)
        (by decide : ("__c6" == "key") = false)
        (by decide : (modifyLiquidityPoolAlias == "key") = false)).trans hk
    have hppre : pre.locals.get? "params" = some (modifyLiquidityParamsValue p) :=
      (store_get_ne3 _ _ _ _ (by decide : ("principalDelta" == "params") = false)
        (by decide : ("__c6" == "params") = false)
        (by decide : (modifyLiquidityPoolAlias == "params") = false)).trans hp
    have hdpre : pre.locals.get? "__c6" = some (.int (EVM.signed p.delta)) :=
      (store_get_ne _ _ (by decide : (modifyLiquidityPoolAlias == "__c6") = false)).trans (store_get_self _ _ _)
    have halias : pre.locals.get? modifyLiquidityPoolAlias = some (poolRefValue id) := store_get_self _ _ _
    have heval : evalExpr? config pre evm modifyLiquidityPoolParamsExpr = .ok (poolModifyParamsValue pp) := by
      rw [modifyLiquidityPoolParams_eval hkpre hppre hdpre, hI]
    have hcall := poolModifyCall hfpre (evalLocalValue halias) heval hl hu hd.1 hd.2 "__c7"
    have hfit : free.toNat+4000 < UInt256.size := by
      change _ ≤ 2^64-1 at hfb
      change _ < 2^256
      omega
    have h192 := uadd_word_ofNat_toNat free 192 (by omega)
    have hptr : (free+UInt256.ofNat 192).toNat+128 < UInt256.size := by omega
    have hret := poolModifyPaidTrace (params := free) (ptr := free+UInt256.ofNat 192) (p := pp)
      (poolModifyCallFrame pre id pp) v hstack hI hσ0 rfl hc hl hu hd
      (hslot.word_load (i := 0) rfl rfl)
      (by have hh := hslot.inBounds; rw [wordBytes_size] at hh; change 128+32*1 ≤ mem.size at hh; omega)
      (by omega) (by omega) (by omega) hpaid1
      (by simpa only [pp, modifyLiquidityPoolParams, wordOfInt_signed] using rd1)
    refine ⟨_, execBlock_append hsource (execBlock_singleton hcall), ?_⟩
    apply blockResultTrace_resumeCall hret
    intro cf post values _ ht
    obtain ⟨hIpost, hσpost, principal, fees, rfl, j0, j1, j2, aw2, k2, C2, hpaid2, rd2⟩ := ht
    have hkey' := hkey.slice.poolModify free (free+UInt256.ofNat 192) id pp evm (by omega)
      (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb)
      (by omega) hptr
    have hparams' := hparams.poolModify free (free+UInt256.ofNat 192) id pp evm (by omega)
      (by simpa only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil] using hpb)
      (by omega) hptr
    have hend := uadd_word_ofNat_toNat (free+UInt256.ofNat 192) 128 hptr
    refine ⟨hIpost, hσpost, principal, fees, _, rdata, (free+UInt256.ofNat 192)+UInt256.ofNat 128,
      rfl, ⟨hkey', hkey.fits⟩, hparams', by omega, by omega, by omega, ?_,
      j0, j1, j2, aw2, k2, C2, hpaid2, rd2⟩
    exact poolModifyMemory_free mem free (free+UInt256.ofNat 192) id pp evm (by omega) (by omega) hptr
  · rw [if_neg hd] at hsource hprepare
    exact ⟨.reverted, execBlock_reverted_append hsource, hprepare⟩

end Benchmarks.UniswapV4PoolManager

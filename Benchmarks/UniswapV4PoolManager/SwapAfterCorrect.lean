import Benchmarks.UniswapV4PoolManager.SwapAfterSource
import Benchmarks.UniswapV4PoolManager.AfterSwapCallCorrect
import Benchmarks.UniswapV4PoolManager.SwapAccountingCorrect
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapAfterCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta src len before junk : UInt256}
    {key : PoolKeyWords} {p : SwapParamsWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hc : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hbefore : f.locals.get? "beforeSwapDelta" = some (.int (EVM.signed before)))
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hcanonical : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hkl : 96 ≤ keyPtr.toNat) (hkb : keyPtr.toNat+160 ≤ free.toNat)
    (hpb : paramsPtr.toNat+96 ≤ free.toNat) (hplo : 96 ≤ paramsPtr.toNat)
    (hfit : free.toNat+len.toNat+512 < UInt256.size) (hroom : free.toNat+64 ≤ solcMaxU64)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨1930⟩
      ([memLoad (keyPtr+UInt256.ofNat 128) mem, solcAddrMask, keyPtr, paramsPtr, delta,
        src, len, before, ⟨1935⟩, keyPtr, ⟨1954⟩, keyPtr+UInt256.ofNat 128, UInt256.ofNat 32, junk]++R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (swapTransition.body.drop 25) result ∧
      abiResultTrace swapTransition.returnType (deployedRuntime v) g s0 result := by
  let hook := AccountAddress.ofNat key.hooks.toNat
  have hw : accountWord hook = key.hooks :=
    (accountWord_fromId key.hooks).trans (solcAddrMask_clean hcanonical.2.2.2.2)
  let f0 := swapAfterStartFrame f
  have hstart : ExecStmt config f evm swapTransition.body[25]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hc0 : f0.contract = contract := by dsimp only [f0, swapAfterStartFrame]; exact hc
  have hk0 : f0.locals.get? "key" = some (poolKeyValue key) :=
    (store_get_ne _ _ (by decide : ("hookDelta" == "key") = false)).trans hk
  have hp0 : f0.locals.get? "params" = some (swapParamsValue p) :=
    (store_get_ne _ _ (by decide : ("hookDelta" == "params") = false)).trans hp
  have hd0 : f0.locals.get? "swapDelta" = some (.int (EVM.signed delta)) :=
    (store_get_ne _ _ (by decide : ("hookDelta" == "swapDelta") = false)).trans hd
  have hb0 : f0.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (store_get_ne _ _ (by decide : ("hookDelta" == "hookData") = false)).trans hb
  have hbefore0 : f0.locals.get? "beforeSwapDelta" = some (.int (EVM.signed before)) :=
    (store_get_ne _ _ (by decide : ("hookDelta" == "beforeSwapDelta") = false)).trans hbefore
  have hh0 : f0.locals.get? "hookDelta" = some (.int 0) := store_get_self _ _ _
  have rd0 := poolManagerBlocks.poolManager_block_1930
    (R := [keyPtr, paramsPtr, delta, src, len, before, UInt256.ofNat 1935,
      keyPtr, UInt256.ofNat 1954, keyPtr+UInt256.ofNat 128, UInt256.ofNat 32, junk]++R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_1930_stack,
    hkey.load (i := 4) rfl, solcAddrMask_clean hcanonical.2.2.2.2] at rd0
  rw [← hw] at rd0
  have hkeyexpr := evalLocalValue (cfg := config) (evm := evm) hk0
  rcases afterSwapCallCorrect (f := f0) (hook := hook) (ret := UInt256.ofNat 1935)
      (R := [keyPtr, UInt256.ofNat 1954, keyPtr+UInt256.ofNat 128, UInt256.ofNat 32, junk]++R)
      v (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hI hσ0 hc0 (evalStructField hkeyexpr (field := "hooks") rfl) hkeyexpr
      (evalLocalValue hp0) (evalLocalValue hd0) (evalLocalValue hb0) (evalLocalValue hbefore0)
      hkey hparams hcanonical hlimit hkb hpb hplo hfit hroom hsrc hgas (by omega) hfree
      (by rw [deployedRuntime_jumps]; jump_dest) "__c7" rd0 with hog | ⟨result, hcall, ht⟩
  · exact .inl hog
  cases result with
  | returned cf post values =>
    obtain ⟨delta', hookDelta, out, data, nextFree, aw1, k1, C1, hIp, hσp, hv, _, rd1, hm⟩ := ht
    subst values
    change ExecStmt config f0 evm swapTransition.body[26]!
      (.ok (swapAfterCallFrame f0 delta' hookDelta) post) at hcall
    have hassign := swapAfterAssignSource (evm := post) (delta := delta') (hook := hookDelta) hd0 hh0
    let ff := swapAfterHookFrame f0 delta' hookDelta
    have hcf : ff.contract = contract := by
      dsimp only [ff, swapAfterHookFrame, tupleLocalsFrame, swapAfterCallFrame]
      exact hc0
    have hkf : ff.locals.get? "key" = some (poolKeyValue key) :=
      (store_get_ne3 _ _ _ _ (by decide : ("__c7" == "key") = false)
        (by decide : ("swapDelta" == "key") = false)
        (by decide : ("hookDelta" == "key") = false)).trans hk0
    have hdf : ff.locals.get? "swapDelta" = some (.int (EVM.signed delta')) :=
      (store_get_ne _ _ (by decide : ("hookDelta" == "swapDelta") = false)).trans (store_get_self _ _ _)
    have hhf : ff.locals.get? "hookDelta" = some (.int (EVM.signed hookDelta)) := store_get_self _ _ _
    have hkey' : PoolKeyView out keyPtr key := ⟨hm.saved _ _ hkey.slice hkl
      (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb), hkey.fits⟩
    obtain ⟨final, hs, htrace⟩ := swapAccountingCorrect (f := ff) v (by omega) hIp hcf hkf hdf hhf hkey' (by omega) rd1
    exact .inr ⟨final, ExecBlock.consNormal hstart (ExecBlock.consNormal hcall (execBlock_append hassign hs)), htrace⟩
  | reverted => exact .inr ⟨.reverted, ExecBlock.consNormal hstart (ExecBlock.consRevert hcall), ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, ExecBlock.consNormal hstart (ExecBlock.consStatic hcall), ht⟩
  | ok | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.SwapBeforeSource
import Benchmarks.UniswapV4PoolManager.SwapPoolCorrect
import Benchmarks.UniswapV4PoolManager.BeforeSwapCallCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapBeforeCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw free src len id keyPtr paramsPtr junk : UInt256}
    {key : PoolKeyWords} {p : SwapParamsWords} {oldDelta : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+49 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hc : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some oldDelta)
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hs : f.locals.get? "pool" = some (poolRefValue id))
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hcanonical : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hkl : 96 ≤ keyPtr.toNat) (hkb : keyPtr.toNat+160 ≤ free.toNat)
    (hpb : paramsPtr.toNat+96 ≤ free.toNat) (hplo : 96 ≤ paramsPtr.toNat)
    (hroom : free.toNat+4000 ≤ solcMaxU64) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hcd : I.calldata.size < 2^255) (hgas : g.toNat < 324518553658429321982441292826060)
    (hpaid : Cₘ aw ≤ C+120) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨1571⟩
      ([len, poolSlot id, paramsPtr+UInt256.ofNat 64, keyPtr, id, src, paramsPtr, junk]++R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (swapTransition.body.drop 15) result ∧
      abiResultTrace swapTransition.returnType (deployedRuntime v) g s0 result := by
  have hfit : free.toNat+len.toNat+480 < UInt256.size := by
    change _ ≤ 2^64-1 at hroom
    change _ < 2^256
    omega
  let f0 := swapBeforeStartFrame f
  let hook := AccountAddress.ofNat key.hooks.toNat
  have hstart := swapBeforeStartSource f evm
  have hc0 : f0.contract = contract := by dsimp only [f0, swapBeforeStartFrame]; exact hc
  have hk0 : f0.locals.get? "key" = some (poolKeyValue key) :=
    (store_get_ne3 _ _ _ _ (by decide : ("beforeSwapDelta" == "key") = false)
      (by decide : ("amountToSwap" == "key") = false) (by decide : ("lpFeeOverride" == "key") = false)).trans hk
  have hp0 : f0.locals.get? "params" = some (swapParamsValue p) :=
    (store_get_ne3 _ _ _ _ (by decide : ("beforeSwapDelta" == "params") = false)
      (by decide : ("amountToSwap" == "params") = false) (by decide : ("lpFeeOverride" == "params") = false)).trans hp
  have hd0 : f0.locals.get? "swapDelta" = some oldDelta :=
    (store_get_ne3 _ _ _ _ (by decide : ("beforeSwapDelta" == "swapDelta") = false)
      (by decide : ("amountToSwap" == "swapDelta") = false) (by decide : ("lpFeeOverride" == "swapDelta") = false)).trans hd
  have hb0 : f0.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (store_get_ne3 _ _ _ _ (by decide : ("beforeSwapDelta" == "hookData") = false)
      (by decide : ("amountToSwap" == "hookData") = false) (by decide : ("lpFeeOverride" == "hookData") = false)).trans hb
  have hs0 : f0.locals.get? "pool" = some (poolRefValue id) :=
    (store_get_ne3 _ _ _ _ (by decide : ("beforeSwapDelta" == "pool") = false)
      (by decide : ("amountToSwap" == "pool") = false) (by decide : ("lpFeeOverride" == "pool") = false)).trans hs
  have hi0 : f0.locals.get? "id" = some (wordBytes32Value id) :=
    (store_get_ne3 _ _ _ _ (by decide : ("beforeSwapDelta" == "id") = false)
      (by decide : ("amountToSwap" == "id") = false) (by decide : ("lpFeeOverride" == "id") = false)).trans hi
  have ha0 : f0.locals.get? "amountToSwap" = some (.int 0) :=
    (store_get_ne _ _ (by decide : ("lpFeeOverride" == "amountToSwap") = false)).trans (store_get_self _ _ _)
  have hbefore0 : f0.locals.get? "beforeSwapDelta" = some (.int 0) :=
    (store_get_ne2 _ _ _ (by decide : ("amountToSwap" == "beforeSwapDelta") = false)
      (by decide : ("lpFeeOverride" == "beforeSwapDelta") = false)).trans (store_get_self _ _ _)
  have hfee0 : f0.locals.get? "lpFeeOverride" = some (.int 0) := store_get_self _ _ _
  have hmask : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) key.hooks =
      accountWord hook := (u256_land_comm _ _).trans (accountWord_fromId key.hooks).symm
  have rd0 := poolManagerBlocks.poolManager_block_1571 (R := junk::R)
    (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_1571_stack, hkey.load (i := 4) rfl, hmask] at rd0
  have hpaid0 : Cₘ (M aw (keyPtr+UInt256.ofNat 128) ⟨32⟩) ≤
      (C+(57+memExpansionCost aw (keyPtr+UInt256.ofNat 128) ⟨32⟩))+63 := by
    dsimp only [memExpansionCost]
    omega
  have hkeyexpr := evalLocalValue (cfg := config) (evm := evm) hk0
  rcases beforeSwapCallCorrect (f := f0) (hook := hook) (ret := UInt256.ofNat 1614)
      (R := [src, len, poolSlot id, paramsPtr+UInt256.ofNat 64, keyPtr, id,
        keyPtr+UInt256.ofNat 128, paramsPtr, junk]++R)
      v (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hI hσ0 hc0 (evalStructField hkeyexpr (field := "hooks") rfl) hkeyexpr
      (evalLocalValue hp0) (evalLocalValue hb0) hkey hparams hcanonical hlimit hkb hpb hkl
      hfit hroom hsrc hgas hpaid0 hfree (by rw [deployedRuntime_jumps]; jump_dest) "__c5" rd0 with
    hog | ⟨result, hcall, ht⟩
  · exact .inl hog
  cases result with
  | returned cf post values =>
    obtain ⟨amount, before, fee, rawFee, out, data, nextFree, aw1, k1, C1,
      hIp, hσp, hv, hfeeBound, hclean, hpaid1, rd1, hm⟩ := ht
    subst values
    change ExecStmt config f0 evm swapTransition.body[18]!
      (.ok (swapBeforeCallFrame f0 amount before fee) post) at hcall
    have hassign := swapBeforeAssignSource (evm := post) (amount := amount) (before := before) (fee := fee)
      ha0 hbefore0 hfee0
    let ff := swapBeforeHookFrame f0 amount before fee
    have hcff : ff.contract = contract := by
      dsimp only [ff, swapBeforeHookFrame, tupleLocalsFrame, swapBeforeCallFrame]
      exact hc0
    have hkff : ff.locals.get? "key" = some (poolKeyValue key) :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("__c5" == "key") = false)
        (by decide : ("amountToSwap" == "key") = false) (by decide : ("beforeSwapDelta" == "key") = false)
        (by decide : ("lpFeeOverride" == "key") = false)).trans hk0
    have hpff : ff.locals.get? "params" = some (swapParamsValue p) :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("__c5" == "params") = false)
        (by decide : ("amountToSwap" == "params") = false) (by decide : ("beforeSwapDelta" == "params") = false)
        (by decide : ("lpFeeOverride" == "params") = false)).trans hp0
    have hdff : ff.locals.get? "swapDelta" = some oldDelta :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("__c5" == "swapDelta") = false)
        (by decide : ("amountToSwap" == "swapDelta") = false) (by decide : ("beforeSwapDelta" == "swapDelta") = false)
        (by decide : ("lpFeeOverride" == "swapDelta") = false)).trans hd0
    have hbff : ff.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("__c5" == "hookData") = false)
        (by decide : ("amountToSwap" == "hookData") = false) (by decide : ("beforeSwapDelta" == "hookData") = false)
        (by decide : ("lpFeeOverride" == "hookData") = false)).trans hb0
    have hsff : ff.locals.get? "pool" = some (poolRefValue id) :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("__c5" == "pool") = false)
        (by decide : ("amountToSwap" == "pool") = false) (by decide : ("beforeSwapDelta" == "pool") = false)
        (by decide : ("lpFeeOverride" == "pool") = false)).trans hs0
    have hiff : ff.locals.get? "id" = some (wordBytes32Value id) :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("__c5" == "id") = false)
        (by decide : ("amountToSwap" == "id") = false) (by decide : ("beforeSwapDelta" == "id") = false)
        (by decide : ("lpFeeOverride" == "id") = false)).trans hi0
    have haff : ff.locals.get? "amountToSwap" = some (.int (EVM.signed amount)) :=
      (store_get_ne2 _ _ _ (by decide : ("beforeSwapDelta" == "amountToSwap") = false)
        (by decide : ("lpFeeOverride" == "amountToSwap") = false)).trans (store_get_self _ _ _)
    have hbeforeff : ff.locals.get? "beforeSwapDelta" = some (.int (EVM.signed before)) :=
      (store_get_ne _ _ (by decide : ("lpFeeOverride" == "beforeSwapDelta") = false)).trans (store_get_self _ _ _)
    have hfeeff : ff.locals.get? "lpFeeOverride" = some (.int (Int.ofNat fee.toNat)) := store_get_self _ _ _
    have hkey1 : PoolKeyView out keyPtr key := ⟨hm.saved _ _ hkey.slice hkl
      (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb), hkey.fits⟩
    have hparams1 := hm.saved _ _ hparams hplo
      (by simpa only [wordBytes_size, swapParamsWordList, List.length_cons, List.length_nil] using hpb)
    have hnlo := hm.lower
    rcases swapPoolCorrect (f := ff) v hstack hIp hσp hcff hkff hpff hdff hbff hbeforeff haff hfeeff
        hsff hiff hkey1 hparams1 hcanonical hlimit hkl (by omega) (by omega) hplo hm.bound
        hsrc hcd hgas hclean hfeeBound hpaid1 hm.freeLoad rd1 with hog | ⟨final, hpool, htrace⟩
    · exact .inl hog
    · exact .inr ⟨final, execBlock_append hstart
        (ExecBlock.consNormal hcall (execBlock_append hassign hpool)), htrace⟩
  | reverted => exact .inr ⟨.reverted, execBlock_append hstart (ExecBlock.consRevert hcall), ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, execBlock_append hstart (ExecBlock.consStatic hcall), ht⟩
  | ok | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager

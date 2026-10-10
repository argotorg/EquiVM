import Benchmarks.UniswapV4PoolManager.SwapWrapperReturn
import Benchmarks.UniswapV4PoolManager.PoolSwapCallCorrect
import Benchmarks.UniswapV4PoolManager.PoolSwapReturnView

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapWrapperBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw id state params callerParams x8 x9 x10 x11 x12 x13 hookPtr junk : UInt256}
    {p : PoolSwapParamsWords} {currency : AccountAddress} {R : List UInt256} {k C : Nat}
    (v : PoolManagerImmutables) (hstack : R.length+49 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hs : f.locals.get? "pool" = some (poolRefValue id))
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hc : f.locals.get? "inputCurrency" = some (.address currency))
    (hm : WordStructView mem params (poolSwapParamsWordList p)) (hparams : 128 ≤ params.toNat)
    (hb : params.toNat+160 ≤ state.toNat) (hfit : state.toNat+352 ≤ solcMaxU64)
    (hfree : memLoad (UInt256.ofNat 64) mem = state) (hspacing : int24Canonical p.tickSpacing)
    (hlimit : p.priceLimit.toNat < 2^160) (hoverride : p.lpFeeOverride.toNat < 2^24)
    (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨18777⟩
      ([poolSlot id, params, ⟨1755⟩, id, UInt256.ofNat 16777215, callerParams, accountWord currency,
        x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32, junk]++R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecFuncBody config f evm swapWrapperFunction.body result ∧
      functionResultTrace (deployedRuntime v) g s0
        (swapWrapperReturn v I g s0 mem rdata state callerParams x8 x9 x10 x11 x12 x13 hookPtr junk R) result := by
  let f1 := valueLocal f swapWrapperAlias (poolRefValue id)
  have halias : ExecStmt config f evm swapWrapperFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letStorage (resolveStorageAlias hs)
  have hparams1 : f1.locals.get? "params" = some (poolSwapParamsValue p) :=
    (store_get_ne _ _ (by decide : (swapWrapperAlias == "params") = false)).trans hp
  rcases poolSwapCallCorrect (f := f1) v (by change R.length+13+36 ≤ 1024; omega) hI hσ0 hf
      (evalLocalValue (store_get_self _ _ _)) (evalLocalValue hparams1)
      hm hparams hb hfit hfree hspacing hlimit hoverride hpaid
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) "__c0" h with hog | ⟨result, hcall, htrace⟩
  · exact .inl hog
  cases result with
  | returned cf post values =>
    have hword : state.toNat+352 < UInt256.size := by
      change _ ≤ 2^64-1 at hfit
      change _ < 2^256
      omega
    have hstate : 96 ≤ state.toNat := by omega
    obtain ⟨r, delta, amount, out, free, aw1, k1, C1, hIp, hσp, hv, _, hp1, rd1, hmem, hprice, htick, hliq⟩ :=
      poolSwapBodyReturn_view hI hσ0 hstate hword htrace
    subst values
    let fee := poolSwapInitialFee evm id p
    let f2 := valueLocal f1 "__c0" (.tuple (poolSwapReturnValues delta fee amount r))
    let f3 := swapWrapperUnpackFrame f2 delta fee amount r
    have hu := swapWrapperUnpackSource (f := f2) (evm := post) (store_get_self _ _ _)
    have hget (name : Ident) (hc0 : ("__c0" == name) = false) (ha : (swapWrapperAlias == name) = false)
        (hd : name ≠ "delta") (hp : name ≠ "amountToProtocol") (he : name ≠ "swapFee") (hr : name ≠ "result") :
        f3.locals.get? name = f.locals.get? name :=
      (swapWrapperUnpack_get f2 delta fee amount r name hd hp he hr).trans (store_get_ne2 _ _ _ ha hc0)
    have hfields : f3.locals.get? "delta" = some (.int (EVM.signed delta)) ∧
        f3.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)) ∧
        f3.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat)) ∧
        f3.locals.get? "result" = some (poolSwapResultValue r) := by
      simp only [f3, swapWrapperUnpackFrame, valueLocal_get, wordLocal_get, beq_iff_eq, String.reduceEq, if_true, if_false]
      exact ⟨True.intro, True.intro, True.intro, True.intro⟩
    have hsTail := swapWrapperTailSource (f := f3) (evm := post)
      ((swapWrapperUnpack_contract ..).trans hf)
      ((hget "id" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi)
      hfields.1 hfields.2.1 hfields.2.2.1 hfields.2.2.2
      ((hget "inputCurrency" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc)
    have hfreeFit : free.toNat+192 < UInt256.size := by
      have h96 := uadd_word_ofNat_toNat state 96 (by omega)
      have h352 := uadd_word_ofNat_toNat state 352 hword
      change _ ≤ 2^64-1 at hfit
      change _ < 2^256
      rcases hmem.freeChoice with hh | hh <;> rw [hh] <;> omega
    have htTail := swapWrapperTailTrace (f := f3) v (by omega) hIp hmem.result hprice hliq htick
      (poolSwapInitialFee_bound evm id p) hfreeFit hmem.freeLoad hstate hp1 rd1
    refine .inr ⟨swapWrapperTailResult f3 post currency delta amount, ?_, ?_⟩
    · exact execFuncBody_prepend (ExecBlock.consNormal halias (ExecBlock.consNormal hcall hu)) hsTail
    · exact functionResultTrace_mono htTail (fun _ _ hh => swapWrapperReturn_of_tail hIp hσp hmem hstate hword hh)
  | reverted =>
    exact .inr ⟨.reverted, .execBlockRevert (ExecBlock.consNormal halias (ExecBlock.consRevert hcall)), htrace⟩
  | staticViolation =>
    exact .inr ⟨.staticViolation, .execBlockStatic (ExecBlock.consNormal halias (ExecBlock.consStatic hcall)), htrace⟩
  | ok | «break» | «continue» => exact False.elim htrace

end Benchmarks.UniswapV4PoolManager

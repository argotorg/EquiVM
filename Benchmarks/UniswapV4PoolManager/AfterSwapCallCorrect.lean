import Benchmarks.UniswapV4PoolManager.AfterSwapBodyCorrect
import Benchmarks.UniswapV4PoolManager.AfterSwapCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
attribute [local irreducible] afterSwapReturn

theorem afterSwapCallCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta src len before ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords} {es ek ep ed eb er : Expr}
    (v : PoolManagerImmutables) (hstack : R.length+26 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hc : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (swapParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.int (EVM.signed delta)))
    (hb : evalExpr? config f evm eb = .ok (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hr : evalExpr? config f evm er = .ok (.int (EVM.signed before)))
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hcanonical : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hplo : 96 ≤ paramsPtr.toNat) (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hroom : free.toNat+64 ≤ solcMaxU64) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+84)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (dest : Ident)
    (h : RD (deployedRuntime v) I g s0 ⟨15745⟩
      (accountWord hook :: keyPtr :: paramsPtr :: delta :: src :: len :: before :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecStmt config f evm (.internalCall "Hooks_afterSwap" [es, ek, ep, ed, eb, er] dest)
        (resumeCallResult f dest result) ∧
      functionResultTrace (deployedRuntime v) g s0 (afterSwapReturn v I g s0 mem free ret R) result := by
  let cf := afterSwapCallFrame f hook key p delta before (I.calldata.extract src.toNat (src.toNat+len.toNat))
  have hcf : cf.contract = contract := by
    dsimp only [cf, afterSwapCallFrame]
    exact hc
  have hself : cf.locals.get? "self" = some (.address hook) := store_get_self _ _ _
  have hkeyarg : cf.locals.get? "key" = some (poolKeyValue key) :=
    (store_get_ne _ _ (by decide : ("self" == "key") = false)).trans (store_get_self _ _ _)
  have hparamsarg : cf.locals.get? "params" = some (swapParamsValue p) :=
    (store_get_ne2 _ _ _ (by decide : ("key" == "params") = false)
      (by decide : ("self" == "params") = false)).trans (store_get_self _ _ _)
  have hdeltaarg : cf.locals.get? "swapDelta" = some (.int (EVM.signed delta)) :=
    (store_get_ne3 _ _ _ _ (by decide : ("params" == "swapDelta") = false)
      (by decide : ("key" == "swapDelta") = false)
      (by decide : ("self" == "swapDelta") = false)).trans (store_get_self _ _ _)
  have hdataarg : cf.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("swapDelta" == "hookData") = false)
      (by decide : ("params" == "hookData") = false) (by decide : ("key" == "hookData") = false)
      (by decide : ("self" == "hookData") = false)).trans (store_get_self _ _ _)
  have hbeforearg : cf.locals.get? "beforeSwapHookReturn" = some (.int (EVM.signed before)) :=
    (store_get_ne5 _ _ _ _ _ _ (by decide : ("hookData" == "beforeSwapHookReturn") = false)
      (by decide : ("swapDelta" == "beforeSwapHookReturn") = false)
      (by decide : ("params" == "beforeSwapHookReturn") = false)
      (by decide : ("key" == "beforeSwapHookReturn") = false)
      (by decide : ("self" == "beforeSwapHookReturn") = false)).trans (store_get_self _ _ _)
  rcases afterSwapBodyCorrect (I := I) (g := g) (s0 := s0) (evm := evm) (f := cf)
      (mem := mem) (rdata := rdata) (aw := aw) (free := free) (keyPtr := keyPtr) (paramsPtr := paramsPtr)
      (key := key) (p := p) (delta := delta) (before := before) (ret := ret) (k := k) (C := C)
      (src := src) (len := len) (hook := hook) (R := R)
      v hstack hI hσ0 hcf hself hkeyarg hparamsarg hdeltaarg hdataarg hbeforearg
      hkey hparams hcanonical hlimit hkb hpb hplo hf hroom hsrc hgas hpaid hfree hret h with
    hog | ⟨result, hbody, htrace⟩
  · exact .inl hog
  · refine .inr ⟨result, ?_, htrace⟩
    exact internalCallFunctionExec (caller := f) (name := "Hooks_afterSwap") (retVar := dest)
      (args := [es, ek, ep, ed, eb, er])
      (argVals := [.address hook, poolKeyValue key, swapParamsValue p, .int (EVM.signed delta),
        .bytes (I.calldata.extract src.toNat (src.toNat+len.toNat)), .int (EVM.signed before)])
      (by simp only [evalExprs?, hs, hk, hp, hd, hb, hr, bind, EvalResult.bind, pure])
      (by rw [hc]; exact afterSwap_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager

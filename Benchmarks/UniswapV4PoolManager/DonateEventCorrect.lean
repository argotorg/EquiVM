import Benchmarks.UniswapV4PoolManager.DonateAfterCorrect
import Benchmarks.UniswapV4PoolManager.DonateEventTrace
import Benchmarks.UniswapV4PoolManager.DonateEventStatic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateEmitSource {f : Frame} {evm : State} {id amount0 amount1 : UInt256}
    (hi : f.locals.get? "poolId" = some (wordBytes32Value id))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat))) :
    ExecStmt config f evm donateTransition.body[18]! (.ok f evm) := by
  apply ExecStmt.emit (vals := [wordBytes32Value id, .address evm.executionEnv.source,
    .int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])
  change evalExprs? config f evm [.var "poolId", .env .caller, .var "amount0", .var "amount1"] = _
  simp only [evalExprs?, evalLocalValue hi, evalLocalValue h0, evalLocalValue h1,
    evalExpr?, envValue, bind, EvalResult.bind, pure]

theorem donateEmitStaticSource {f : Frame} {evm : State} {id amount0 amount1 : UInt256}
    (hi : f.locals.get? "poolId" = some (wordBytes32Value id))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config f evm donateTransition.body[18]! .staticViolation := by
  cases donateEmitSource (evm := evm) hi h0 h1 with
  | emit he => exact ExecStmt.emitStatic he hperm

theorem donateEventCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr src amount0 amount1 len delta id junk : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hi : f.locals.get? "poolId" = some (wordBytes32Value id))
    (hkey : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hkl : 96 ≤ keyPtr.toNat)
    (hfit : free.toNat+len.toNat+448 < UInt256.size) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨10297⟩
      (id :: (keyPtr+UInt256.ofNat 128) :: keyPtr :: src :: amount1 :: amount0 :: len :: delta :: ⟨32⟩ :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (donateTransition.body.drop 18) result ∧
      abiResultTrace donateTransition.returnType (deployedRuntime v) g s0 result := by
  cases hperm : I.perm with
  | false =>
    exact .inr ⟨.staticViolation, ExecBlock.consStatic
      (donateEmitStaticSource hi h0 h1 (by rwa [hI])),
      donateEventStatic (by simp only [List.length_cons]; omega) hperm h⟩
  | true =>
    let hook := AccountAddress.ofNat key.hooks.toNat
    have hw : accountWord hook = key.hooks :=
      (accountWord_fromId key.hooks).trans (solcAddrMask_clean hc.2.2.2.2)
    obtain ⟨aw1, k1, C1, hp1, rd1⟩ := donateEventTrace (hook := hook) v (by omega) hkey hw hkb (by omega) hperm hfree h
    rw [hw] at rd1
    have hfree1 := (donateEventMemory_free mem free amount0 amount1
      (by have := hkey.inBounds; omega) (by omega)).trans hfree
    rcases donateAfterCorrect v hstack hI hσ0 hf hk h0 h1 hd hb
        (hkey.donateEvent free amount0 amount1 hkb) hc hkb (by omega) hfit hsrc hgas
        (by omega) hfree1 rd1 with hog | ⟨result, hs, ht⟩
    · exact .inl hog
    · exact .inr ⟨result, ExecBlock.consNormal (donateEmitSource hi h0 h1) hs, ht⟩

end Benchmarks.UniswapV4PoolManager

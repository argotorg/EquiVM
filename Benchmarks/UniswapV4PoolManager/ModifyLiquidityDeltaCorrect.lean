import Benchmarks.UniswapV4PoolManager.ModifyLiquidityDeltaSource
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityEventTrace
import Benchmarks.UniswapV4PoolManager.BalanceDeltaAddCostTrace
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityEventFrame (f : Frame) (principal fees : UInt256) : Frame :=
  {f with locals := (modifyLiquidityDeltaFrame f principal fees).locals.insert "hookDelta" (.int 0)}

theorem modifyLiquidityEventFrame_contract (f : Frame) (principal fees : UInt256) :
    (modifyLiquidityEventFrame f principal fees).contract = f.contract := by
  simp only [modifyLiquidityEventFrame]

theorem modifyLiquidityDeltaCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr paramsPtr principal fees src len id junk j0 j1 j2 : UInt256}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {k C : Nat} {R : List UInt256}
    {oldPrincipal oldFees oldCaller : Value}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hf : f.contract = contract)
    (hI : evm.executionEnv = I)
    (ht : f.locals.get? "__c7" = some (.tuple [.int (EVM.signed principal), .int (EVM.signed fees)]))
    (hprincipal : f.locals.get? "principalDelta" = some oldPrincipal)
    (hfees : f.locals.get? "feesAccrued" = some oldFees)
    (hcaller : f.locals.get? "callerDelta" = some oldCaller)
    (hid : f.locals.get? "id" = some (wordBytes32Value id))
    (hparams : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : key.hooks.toNat < 2^160) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hfit : free.toNat+128 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨6046⟩
      ([j0, j1, j2, principal, paramsPtr, id, fees, src, len, ⟨6222⟩, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ result,
      ExecBlock config f evm ((modifyLiquidityTransition.body.drop 20).take 6) result ∧
      blockResultTrace (deployedRuntime v) g s0 (fun f' post =>
        f' = modifyLiquidityEventFrame f principal fees ∧ post = evm ∧ ∃ aw' k' C', Cₘ aw' ≤ C' ∧
          RD (deployedRuntime v) I g s0 ⟨14427⟩
            ([key.hooks, keyPtr, paramsPtr, balanceDeltaCombineWord false principal fees, fees, src, len,
              ⟨6222⟩, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
            (modifyLiquidityEventMemory mem free p) aw' rdata post.accountMap k' C')
        (fun _ _ => False) result := by
  have hs := modifyLiquidityDeltaSource (evm := evm) hf ht hprincipal hfees hcaller
  have hr := balanceDeltaAddCostTrace (R := [src, len, ⟨6222⟩, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
    f v (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) h
  by_cases hsum : balanceDeltaCombineFits false principal fees
  · rw [if_pos hsum] at hs
    rw [balanceDeltaCombineResult, if_pos hsum] at hr
    obtain ⟨_, _, k1, C1, hcost, rd1⟩ := hr
    have hdframeid : (modifyLiquidityDeltaFrame f principal fees).locals.get? "id" = some (wordBytes32Value id) :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("principalDelta" == "id") = false)
        (by decide : ("feesAccrued" == "id") = false) (by decide : ("totalDelta" == "id") = false)
        (by decide : ("callerDelta" == "id") = false)).trans hid
    have hdframeparams : (modifyLiquidityDeltaFrame f principal fees).locals.get? "params" = some (modifyLiquidityParamsValue p) :=
      (store_get_ne4 _ _ _ _ _ (by decide : ("principalDelta" == "params") = false)
        (by decide : ("feesAccrued" == "params") = false) (by decide : ("totalDelta" == "params") = false)
        (by decide : ("callerDelta" == "params") = false)).trans hparams
    rcases modifyLiquidityEventTrace v hstack hk hp hc hl hu hkb hpb hfit hfree
        (Nat.le_trans hpaid hcost) rd1 with hstatic | hnext
    · exact ⟨.staticViolation, execBlock_append hs
        (modifyLiquidityEventStaticSource hdframeid hdframeparams (by rw [hI]; exact hstatic.1)), hstatic.2⟩
    · exact ⟨_, execBlock_append hs (modifyLiquidityEventSource hdframeid hdframeparams),
        rfl, rfl, hnext⟩
  · rw [if_neg hsum] at hs
    rw [balanceDeltaCombineResult, if_neg hsum] at hr
    exact ⟨.reverted, execBlock_reverted_append hs, hr⟩

end Benchmarks.UniswapV4PoolManager

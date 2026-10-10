import Benchmarks.UniswapV4PoolManager.AccountPoolCallTrace
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityReturnTrace
import Benchmarks.UniswapV4PoolManager.ABIResultTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem modifyLiquidityCallerCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr caller fees discard junk : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hI : evm.executionEnv = I) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hc : f.locals.get? "callerDelta" = some (.int (EVM.signed caller)))
    (he : f.locals.get? "feesAccrued" = some (.int (EVM.signed fees)))
    (hkey : PoolKeyView mem keyPtr key) (hkl : 96 ≤ keyPtr.toNat)
    (hfit : free.toNat+64 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨6231⟩
      ([discard, keyPtr, ⟨6240⟩, fees, caller, UInt256.ofNat 64, junk] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecBlock config f evm (modifyLiquidityTransition.body.drop 30) result ∧
      abiResultTrace modifyLiquidityTransition.returnType (deployedRuntime v) g s0 result := by
  have rd := poolManagerBlocks.poolManager_block_6231 (R := [UInt256.ofNat 64, junk] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have ht := accountPoolCallTrace (ret := ⟨6240⟩) (target := I.source)
    (R := [fees, caller, UInt256.ofNat 64, junk] ++ R) f "__c9" v
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hI hkey (by omega)
    (by rw [deployedRuntime_jumps]; jump_dest) rd
  have hs := accountPoolCall hf (evalLocalValue (evm := evm) hk) (evalLocalValue hc)
    (show evalExpr? config f evm (.env .caller) = .ok (.address I.source) by
      simp only [evalExpr?, envValue, hI, pure]) "__c9"
  change ExecStmt config f evm modifyLiquidityTransition.body[30]!
    (resumeCallResult f "__c9" (accountPoolResult (accountPoolCalleeFrame f key caller I.source) evm key caller I.source)) at hs
  generalize hx : resumeCallResult f "__c9"
    (accountPoolResult (accountPoolCalleeFrame f key caller I.source) evm key caller I.source) = result at hs ht
  cases result with
  | ok ff post =>
      obtain ⟨rfl, rfl, aw1, k1, C1, rd1⟩ := ht
      have hreturn : ExecStmt config {f with locals := f.locals.insert "__c9" .unit}
          (accountPoolPost evm key caller I.source) modifyLiquidityTransition.body[31]!
          (.returned {f with locals := f.locals.insert "__c9" .unit} (accountPoolPost evm key caller I.source)
            (some [.int (EVM.signed caller), .int (EVM.signed fees)])) := by
        apply ExecStmt.return
        have hc' := evalLocalValue (cfg := config) (f := {f with locals := f.locals.insert "__c9" .unit})
          (evm := accountPoolPost evm key caller I.source)
          ((store_get_ne _ _ (by decide : ("__c9" == "callerDelta") = false)).trans hc)
        have he' := evalLocalValue (cfg := config) (f := {f with locals := f.locals.insert "__c9" .unit})
          (evm := accountPoolPost evm key caller I.source)
          ((store_get_ne _ _ (by decide : ("__c9" == "feesAccrued") = false)).trans he)
        simp only [evalExprs?, hc', he', bind, EvalResult.bind, pure]
      have hr := modifyLiquidityReturnTrace (R := junk :: R) v (by simp only [List.length_cons]; omega) hfit
        ((accountPoolMemory_load _ _ _ _ (UInt256.ofNat 64) (by decide)
          (by have := hkey.inBounds; change 96 ≤ mem.size; omega)).trans hfree) rd1
      exact ⟨_, ExecBlock.consNormal hs (ExecBlock.consReturn hreturn),
        wordBytes [caller, fees], hr, returnEquiv.returned rfl (signedPairReturnEncoding caller fees)⟩
  | reverted => exact ⟨.reverted, ExecBlock.consRevert hs, ht⟩
  | staticViolation => exact ⟨.staticViolation, ExecBlock.consStatic hs, ht⟩
  | returned | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager

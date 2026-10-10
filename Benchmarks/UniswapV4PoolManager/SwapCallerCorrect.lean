import Benchmarks.UniswapV4PoolManager.AccountPoolCallTrace
import Benchmarks.UniswapV4PoolManager.WordReturnSparseTrace
import Benchmarks.UniswapV4PoolManager.SignedResultTrace
import Benchmarks.UniswapV4PoolManager.SignedWordBounds
import Benchmarks.UniswapV4PoolManager.ABIResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapCallerCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw keyPtr delta discard ignored junk : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+19 ≤ 1024)
    (hI : evm.executionEnv = I) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hkey : PoolKeyView mem keyPtr key) (hkl : 64 ≤ keyPtr.toNat)
    (h : RD (deployedRuntime v) I g s0 ⟨1944⟩
      ([discard, ignored, keyPtr, ⟨1954⟩, delta, UInt256.ofNat 32, junk] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecBlock config f evm (swapTransition.body.drop 30) result ∧
      abiResultTrace swapTransition.returnType (deployedRuntime v) g s0 result := by
  have rd := poolManagerBlocks.poolManager_block_1944 (R := [UInt256.ofNat 32, junk] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have ht := accountPoolCallTrace (ret := ⟨1954⟩) (target := I.source)
    (R := [delta, UInt256.ofNat 32, junk] ++ R) f "__c8" v
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hI hkey hkl
    (by rw [deployedRuntime_jumps]; jump_dest) rd
  have hs := accountPoolCall hf (evalLocalValue (evm := evm) hk) (evalLocalValue hd)
    (show evalExpr? config f evm (.env .caller) = .ok (.address I.source) by
      simp only [evalExpr?, envValue, hI, pure]) "__c8"
  change ExecStmt config f evm swapTransition.body[30]!
    (resumeCallResult f "__c8" (accountPoolResult (accountPoolCalleeFrame f key delta I.source) evm key delta I.source)) at hs
  generalize hx : resumeCallResult f "__c8"
    (accountPoolResult (accountPoolCalleeFrame f key delta I.source) evm key delta I.source) = result at hs ht
  cases result with
  | ok ff post =>
      obtain ⟨rfl, rfl, aw1, k1, C1, rd1⟩ := ht
      have hreturn : ExecStmt config {f with locals := f.locals.insert "__c8" .unit}
          (accountPoolPost evm key delta I.source) swapTransition.body[31]!
          (.returned {f with locals := f.locals.insert "__c8" .unit} (accountPoolPost evm key delta I.source)
            (some [.int (EVM.signed delta)])) := by
        apply ExecStmt.return
        have hd' := evalLocalValue (cfg := config) (f := {f with locals := f.locals.insert "__c8" .unit})
          (evm := accountPoolPost evm key delta I.source)
          ((store_get_ne _ _ (by decide : ("__c8" == "swapDelta") = false)).trans hd)
        simp only [evalExprs?, hd', bind, EvalResult.bind, pure]
      have hr := wordReturnSparseTrace (R := junk :: R) v (by simp only [List.length_cons]; omega) rd1
      exact ⟨_, ExecBlock.consNormal hs (ExecBlock.consReturn hreturn), delta.toByteArray, hr,
        returnEquiv_of_encode (signedReturnEncoding ⟨256, by decide⟩ delta (signedWord_fits delta))⟩
  | reverted => exact ⟨.reverted, ExecBlock.consRevert hs, ht⟩
  | staticViolation => exact ⟨.staticViolation, ExecBlock.consStatic hs, ht⟩
  | returned | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager

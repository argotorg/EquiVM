import Benchmarks.UniswapV4PoolManager.SwapCallerCorrect
import Benchmarks.UniswapV4PoolManager.TickPriceSelectSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapAccountingCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw keyPtr delta hookDelta junk : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024)
    (hI : evm.executionEnv = I) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hh : f.locals.get? "hookDelta" = some (.int (EVM.signed hookDelta)))
    (hkey : PoolKeyView mem keyPtr key) (hkl : 64 ≤ keyPtr.toNat)
    (h : RD (deployedRuntime v) I g s0 ⟨1935⟩
      ([hookDelta, delta, keyPtr, ⟨1954⟩, keyPtr+UInt256.ofNat 128, UInt256.ofNat 32, junk] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecBlock config f evm (swapTransition.body.drop 29) result ∧
      abiResultTrace swapTransition.returnType (deployedRuntime v) g s0 result := by
  have hcond := evalNeSignedWords (cfg := config) (evm := evm) (evalLocalValue hh)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (EVM.signed (⟨0⟩ : UInt256))) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hz : hookDelta = (⟨0⟩ : UInt256)
  · have rd := poolManagerBlocks.poolManager_block_1935_fallthrough
      (R := [UInt256.ofNat 32, junk] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hz h
    have hs : ExecStmt config f evm swapTransition.body[29]! (.ok f evm) :=
      ExecStmt.iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hcond) ExecBlock.nil
    obtain ⟨result, hbody, ht⟩ := swapCallerCorrect v (by omega) hI hf hk hd hkey hkl rd
    exact ⟨result, ExecBlock.consNormal hs hbody, ht⟩
  · have rd1 := poolManagerBlocks.poolManager_block_1935_taken
      (R := [UInt256.ofNat 32, junk] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hz
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_1962
      (R := [⟨1954⟩, delta, UInt256.ofNat 32, junk] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    let hook := AccountAddress.ofNat key.hooks.toNat
    change RD (deployedRuntime v) I g s0 ⟨13906⟩
      ([keyPtr, hookDelta, UInt256.land (memLoad (keyPtr+UInt256.ofNat 128) mem) solcAddrMask,
        ⟨1996⟩, keyPtr, ⟨1954⟩, delta, UInt256.ofNat 32, junk] ++ R) _ _ _ _ _ _ at rd2
    rw [hkey.load (i := 4) rfl, ← accountWord_fromId] at rd2
    have ht := accountPoolCallTrace (ret := ⟨1996⟩) (target := hook)
      (R := [keyPtr, ⟨1954⟩, delta, UInt256.ofNat 32, junk] ++ R) f "ignored" v
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hI hkey hkl
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    have hkexpr := evalLocalValue (cfg := config) (evm := evm) hk
    have hcall := accountPoolCall hf hkexpr (evalLocalValue hh)
      (evalStructField hkexpr (field := "hooks") rfl) "ignored"
    have hs : ExecStmt config f evm swapTransition.body[29]!
        (resumeCallResult f "ignored" (accountPoolResult (accountPoolCalleeFrame f key hookDelta hook) evm key hookDelta hook)) :=
      ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hcond) (execBlock_singleton hcall)
    generalize hx : resumeCallResult f "ignored"
      (accountPoolResult (accountPoolCalleeFrame f key hookDelta hook) evm key hookDelta hook) = result at hs ht
    cases result with
    | ok ff post =>
        obtain ⟨rfl, rfl, aw1, k1, C1, rd3⟩ := ht
        have rd4 := poolManagerBlocks.poolManager_block_1996 (R := R)
          (by omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
        have hI' := (accountPoolPost_env evm key hookDelta hook).trans hI
        have hf' : ({f with locals := f.locals.insert "ignored" .unit} : Frame).contract = contract := hf
        have hk' := (store_get_ne _ .unit (by decide : ("ignored" == "key") = false)).trans hk
        have hd' := (store_get_ne _ .unit (by decide : ("ignored" == "swapDelta") = false)).trans hd
        obtain ⟨result, hbody, htrace⟩ := swapCallerCorrect v (by omega) hI' hf' hk' hd'
          (hkey.accountPool hookDelta hook hkl) hkl rd4
        exact ⟨result, ExecBlock.consNormal hs hbody, htrace⟩
    | reverted => exact ⟨.reverted, ExecBlock.consRevert hs, ht⟩
    | staticViolation => exact ⟨.staticViolation, ExecBlock.consStatic hs, ht⟩
    | returned | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.ModifyLiquidityCallerCorrect
import Benchmarks.UniswapV4PoolManager.TickPriceSelectSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem modifyLiquidityAccountingCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr caller fees hookDelta junk : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+22 ≤ 1024)
    (hI : evm.executionEnv = I) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hc : f.locals.get? "callerDelta" = some (.int (EVM.signed caller)))
    (he : f.locals.get? "feesAccrued" = some (.int (EVM.signed fees)))
    (hh : f.locals.get? "hookDelta" = some (.int (EVM.signed hookDelta)))
    (hkey : PoolKeyView mem keyPtr key) (hkl : 96 ≤ keyPtr.toNat)
    (hfit : free.toNat+64 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨6222⟩
      ([hookDelta, caller, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecBlock config f evm (modifyLiquidityTransition.body.drop 29) result ∧
      abiResultTrace modifyLiquidityTransition.returnType (deployedRuntime v) g s0 result := by
  have hcond := evalNeSignedWords (cfg := config) (evm := evm) (evalLocalValue hh)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (EVM.signed (⟨0⟩ : UInt256))) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hz : hookDelta = (⟨0⟩ : UInt256)
  · have rd := poolManagerBlocks.poolManager_block_6222_fallthrough
      (R := [UInt256.ofNat 64, junk] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hz h
    have hs : ExecStmt config f evm modifyLiquidityTransition.body[29]! (.ok f evm) :=
      ExecStmt.iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hcond) ExecBlock.nil
    obtain ⟨result, hbody, ht⟩ := modifyLiquidityCallerCorrect v (by omega) hI hf hk hc he hkey hkl hfit hfree rd
    exact ⟨result, ExecBlock.consNormal hs hbody, ht⟩
  · have rd1 := poolManagerBlocks.poolManager_block_6222_taken
      (R := [UInt256.ofNat 64, junk] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hz
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_6252
      (R := [⟨6240⟩, fees, caller, UInt256.ofNat 64, junk] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    let hook := AccountAddress.ofNat key.hooks.toNat
    change RD (deployedRuntime v) I g s0 ⟨13906⟩
      ([keyPtr, hookDelta, UInt256.land (memLoad (keyPtr+UInt256.ofNat 128) mem) solcAddrMask,
        ⟨6290⟩, keyPtr, ⟨6240⟩, fees, caller, UInt256.ofNat 64, junk] ++ R) _ _ _ _ _ _ at rd2
    rw [hkey.load (i := 4) rfl, ← accountWord_fromId] at rd2
    have ht := accountPoolCallTrace (ret := ⟨6290⟩) (target := hook)
      (R := [keyPtr, ⟨6240⟩, fees, caller, UInt256.ofNat 64, junk] ++ R) f "ignored" v
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hI hkey (by omega)
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    have hkexpr := evalLocalValue (cfg := config) (evm := evm) hk
    have hcall := accountPoolCall hf hkexpr (evalLocalValue hh)
      (evalStructField hkexpr (field := "hooks") rfl) "ignored"
    have hs : ExecStmt config f evm modifyLiquidityTransition.body[29]!
        (resumeCallResult f "ignored" (accountPoolResult (accountPoolCalleeFrame f key hookDelta hook) evm key hookDelta hook)) :=
      ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hcond) (execBlock_singleton hcall)
    generalize hx : resumeCallResult f "ignored"
      (accountPoolResult (accountPoolCalleeFrame f key hookDelta hook) evm key hookDelta hook) = result at hs ht
    cases result with
    | ok ff post =>
        obtain ⟨rfl, rfl, aw1, k1, C1, rd3⟩ := ht
        have rd4 := poolManagerBlocks.poolManager_block_6290 (R := R)
          (by omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
        have hI' := (accountPoolPost_env evm key hookDelta hook).trans hI
        have hf' : ({f with locals := f.locals.insert "ignored" .unit} : Frame).contract = contract := hf
        have hk' := (store_get_ne _ .unit (by decide : ("ignored" == "key") = false)).trans hk
        have hc' := (store_get_ne _ .unit (by decide : ("ignored" == "callerDelta") = false)).trans hc
        have he' := (store_get_ne _ .unit (by decide : ("ignored" == "feesAccrued") = false)).trans he
        have hfree' := (accountPoolMemory_load mem key hookDelta hook (UInt256.ofNat 64) (by decide)
          (by have := hkey.inBounds; change 96 ≤ mem.size; omega)).trans hfree
        obtain ⟨result, hbody, htrace⟩ := modifyLiquidityCallerCorrect v (by omega) hI' hf' hk' hc' he'
          (hkey.accountPool hookDelta hook (by omega)) hkl hfit hfree' rd4
        exact ⟨result, ExecBlock.consNormal hs hbody, htrace⟩
    | reverted => exact ⟨.reverted, ExecBlock.consRevert hs, ht⟩
    | staticViolation => exact ⟨.staticViolation, ExecBlock.consStatic hs, ht⟩
    | returned | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager

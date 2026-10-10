import Benchmarks.UniswapV4PoolManager.Values
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev noDelegateCallFunction : FunctionDecl := contract.functions[8]!
theorem noDelegateCall_lookup : lookupCallable? contract "checkNotDelegateCall" =
    some noDelegateCallFunction.toCallable := rfl

theorem noDelegateCallBody {f : Frame} {evm : EVM.State} (v : PoolManagerImmutables)
    (him : f.immutables = immStore v) :
    ExecFuncBody config f evm noDelegateCallFunction.body
      (if evm.executionEnv.codeOwner = v.original then .returned f evm none else .reverted) := by
  have horig : evalExpr? config f evm (.immutable "original") = .ok (.address v.original) := by
    simp only [evalExpr?, him, immStore_get_original, EvalResult.ofOption]
  have hc := evalNeAddress (show evalExpr? config f evm (.env .this) =
      .ok (.address evm.executionEnv.codeOwner) from by simp only [evalExpr?, envValue, pure]) horig
  by_cases he : evm.executionEnv.codeOwner = v.original
  · rw [if_pos he]
    simp only [he, ne_eq, not_true_eq_false, decide_false] at hc
    exact .execBlockOK (ExecBlock.consNormal (ExecStmt.iteFalse hc ExecBlock.nil) ExecBlock.nil)
  · rw [if_neg he]
    rw [decide_eq_true he] at hc
    exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue hc
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))

theorem noDelegateCallCall {f : Frame} {evm : EVM.State} (v : PoolManagerImmutables)
    (hf : f.contract = contract) (him : f.immutables = immStore v) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "checkNotDelegateCall" [] retVar)
      (if evm.executionEnv.codeOwner = v.original then
        .ok {f with locals := f.locals.insert retVar .unit} evm else .reverted) := by
  have hb := noDelegateCallBody (f := {f with locals := ∅}) (evm := evm) v him
  have hl : lookupCallable? f.contract "checkNotDelegateCall" = some noDelegateCallFunction.toCallable := by
    rw [hf]; exact noDelegateCall_lookup
  by_cases he : evm.executionEnv.codeOwner = v.original
  · rw [if_pos he] at hb ⊢
    exact internalCallFunctionReturn (argVals := []) (by simp only [evalExprs?, pure]) hl rfl hb
  · rw [if_neg he] at hb ⊢
    exact internalCallFunctionRevert (argVals := []) (by simp only [evalExprs?, pure]) hl rfl hb

theorem noDelegateCallTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+3 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13583⟩ (ret :: R) mem aw rdata σ k C) :
    if I.codeOwner = v.original then ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have heq : accountWord I.codeOwner = accountWord v.original ↔ I.codeOwner = v.original := by
    simpa only [accountWord_address] using
      (accountWord_eq_iff I.codeOwner (accountWord v.original) (accountWord_canonical v.original)).symm
  have hcond : UInt256.sub (UInt256.ofNat I.codeOwner.val)
      (UInt256.land (wordsOf (immStore v) "original")
        (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) = ⟨0⟩ ↔
      I.codeOwner = v.original := by
    rw [wordsOf_immStore_original]
    change UInt256.sub (accountWord I.codeOwner) (UInt256.land (accountWord v.original) solcAddrMask) = ⟨0⟩ ↔ _
    rw [solcAddrMask_clean (accountWord_canonical v.original), u256_sub_eq_zero_iff_eq]
    exact heq
  by_cases he : I.codeOwner = v.original
  · rw [if_pos he]
    have rd1 := poolManagerBlocks.poolManager_block_13583_fallthrough
      (by simp only [List.length_cons]; omega) (hcond.mpr he) h
    exact ⟨_, _, poolManagerBlocks.poolManager_block_13645 (by omega) hret rd1⟩
  · rw [if_neg he]
    have rd1 := poolManagerBlocks.poolManager_block_13583_taken
      (by simp only [List.length_cons]; omega) (fun hh => he (hcond.mp hh))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_13646 (by simp only [List.length_cons]; omega) rd1

end Benchmarks.UniswapV4PoolManager

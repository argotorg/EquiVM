import Benchmarks.UniswapV4PoolManager.TransientSource
import Benchmarks.UniswapV4PoolManager.SignedWords
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_036

/-! The checked uint256-to-int128 helper in the source and bytecode. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem uintToInt128Function_lookup :
    lookupCallable? contract "SafeCast_toInt128_uint256" = some uintToInt128Function.toCallable := rfl

abbrev int128BoundExpr : Expr := .binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1) (.intLit 127)

theorem int128Bound_eval {f : Frame} {evm : EVM.State} :
    evalExpr? config f evm int128BoundExpr = .ok (.int (Int.ofNat (2^127))) := by
  simp only [int128BoundExpr, evalExpr?, bind, EvalResult.bind, pure]
  rfl

theorem uintToInt128BodyExec {f : Frame} {evm : EVM.State} {w : UInt256}
    (hx : f.locals.get? "x" = some (.int (Int.ofNat w.toNat))) :
    ExecFuncBody config f evm uintToInt128Function.body
      (if w.toNat < 2^127 then .returned f evm (some [.int (Int.ofNat w.toNat)]) else .reverted) := by
  have hguard : evalExpr? config f evm (.binary .ge (.var "x") int128BoundExpr) =
      .ok (.bool (decide (2^127 ≤ w.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hx, int128Bound_eval]
    simp only [bind, EvalResult.bind, evalBinaryOp?, ge_iff_le, Int.ofNat_eq_natCast, Int.ofNat_le]
  by_cases hfit : w.toNat < 2^127
  · rw [if_pos hfit]
    apply ExecFuncBody.execBlockRet
    refine ExecBlock.consNormal (ExecStmt.iteFalse
      (hguard.trans (by rw [decide_eq_false (by omega)])) ExecBlock.nil) (ABlock.start.returns ?_)
    have he := evalExpr_cast_int (intType := .sint ⟨128, by decide⟩)
      (evalExpr_cast_int (intType := .sint ⟨256, by decide⟩) (evalLocalValue (cfg := config) (evm := evm) hx))
    rw [normalizeInt_sint256_word_of_lt w (by change w.toNat < 2^255; omega)] at he
    rw [normalizeSignedSelf ⟨128, by decide⟩ (Int.ofNat w.toNat)
      (by change -(170141183460469231731687303715884105728 : Int) ≤ Int.ofNat w.toNat; simp only [Int.ofNat_eq_natCast]; omega)
      (by change Int.ofNat w.toNat < (170141183460469231731687303715884105728 : Int); simp only [Int.ofNat_eq_natCast]; omega)] at he
    exact he
  · rw [if_neg hfit]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert
      (ExecStmt.iteTrue (hguard.trans (by rw [decide_eq_true (by omega)]))
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?]; rfl)))))

theorem uintToInt128Call {f : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat w.toNat)))
    (hfit : w.toNat < 2^127) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "SafeCast_toInt128_uint256" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (Int.ofNat w.toNat))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat w.toNat)])
    (value := some [.int (Int.ofNat w.toNat)])
    (evalExprs?_singleton he) (by rw [hf]; exact uintToInt128Function_lookup) rfl
  have h := uintToInt128BodyExec (evm := evm) (f := {f with locals := (∅ : Store).insert "x" (.int (Int.ofNat w.toNat))})
    (store_get_self _ _ _)
  rwa [if_pos hfit] at h

theorem uintToInt128CallReverts {f : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat w.toNat)))
    (hfit : ¬w.toNat < 2^127) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "SafeCast_toInt128_uint256" [e] retVar) .reverted := by
  apply internalCallFunctionRevert (argVals := [.int (Int.ofNat w.toNat)])
    (evalExprs?_singleton he) (by rw [hf]; exact uintToInt128Function_lookup) rfl
  have h := uintToInt128BodyExec (evm := evm) (f := {f with locals := (∅ : Store).insert "x" (.int (Int.ofNat w.toNat))})
    (store_get_self _ _ _)
  rwa [if_neg hfit] at h

theorem uintToInt128Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw w ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 4 ≤ 1024) (hfit : w.toNat < 2^127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12458⟩ (w :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (w :: R) mem aw rdata σ k' C' := by
  have hg : UInt256.isZero (UInt256.lt w ⟨2^127⟩) = ⟨0⟩ := by
    change UInt256.isZero (UInt256.fromBool (decide (w < (⟨2^127⟩ : UInt256)))) = ⟨0⟩
    rw [decide_eq_true (show w < (⟨2^127⟩ : UInt256) from hfit)]; decide
  have hnext := poolManagerBlocks.poolManager_block_12458_fallthrough (by simp only [List.length_cons]; omega) hg h
  have hdone := poolManagerBlocks.poolManager_block_12483 (by omega) hret hnext
  change RD (deployedRuntime v) I g s0 ret (UInt256.signextend ⟨15⟩ w :: R) mem aw rdata σ _ _ at hdone
  rw [signextend128_of_lt w hfit] at hdone
  exact ⟨_, _, hdone⟩

theorem uintToInt128TraceReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw w : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 3 ≤ 1024) (hfit : ¬w.toNat < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨12458⟩ (w :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hg : UInt256.isZero (UInt256.lt w ⟨2^127⟩) ≠ ⟨0⟩ := by
    change UInt256.isZero (UInt256.fromBool (decide (w < (⟨2^127⟩ : UInt256)))) ≠ ⟨0⟩
    rw [decide_eq_false (show ¬w < (⟨2^127⟩ : UInt256) from hfit)]; decide
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12488) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hnext := poolManagerBlocks.poolManager_block_12458_taken hstack hg hj h
  exact poolManagerBlocks.poolManager_block_12488 (by simp only [List.length_cons]; omega) hnext

end Benchmarks.UniswapV4PoolManager

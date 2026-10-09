import Benchmarks.CompoundIII.Comet.Unsigned256

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem unsigned256_call_revert (frame : Frame) (evm : EVM.State) (n : Int)
    (expr : Expr) (ret : Ident) (hf : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int n)) (hneg : n < 0) :
    ExecStmt config frame evm (.internalCall "unsigned256" [expr] ret) .reverted := by
  let entry : Frame := { frame with locals := (∅ : Store).insert "n" (.int n) }
  have hn : evalExpr? config entry evm (.var "n") = .ok (.int n) := by
    simp only [evalExpr?, entry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  have hc : evalExpr? config entry evm (.binary .ge (.var "n") (.intLit 0)) =
      .ok (.bool false) := by
    simp only [evalExpr?, hn, pure, bind, EvalResult.bind, evalBinaryOp?]
    rw [decide_eq_false (by omega)]
  have hb : ExecFuncBody config entry evm unsigned256Callable.body .reverted :=
    ExecFuncBody.execBlockRevert (ABlock.start.requireRevert hc)
  exact ExecStmt.internalCallRevert (callee := unsigned256Callable)
    (argVals := [.int n]) (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hf]; exact unsigned256Callable_lookup) rfl hb

theorem cometUnsigned256Revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hn : UInt256.slt n ⟨0⟩ ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 ⟨17954⟩ (n :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_17954_taken
    (immWords := wordsOf (immStore v)) (by omega) hn
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometWithExtendedAssetList_block_17936 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 3 ≤ 1024; omega) r1

end Benchmarks.CompoundIII.Comet

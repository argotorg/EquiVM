import Benchmarks.CompoundIII.Comet.SignedWord
import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_080

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

def unsigned256Callable : CallableDecl :=
  { params := [⟨"n", .elem (.int (.sint ⟨256, by decide⟩))⟩], returnType := [abiUInt256],
    body := [.require (.binary .ge (.var "n") (.intLit 0)),
      .return [.cast (.var "n") (.elem (.int (.uint ⟨256, by decide⟩)))]] }

theorem unsigned256Callable_lookup :
    lookupCallable? contract "unsigned256" = some unsigned256Callable := rfl

theorem unsigned256_call_ok (frame : Frame) (evm : EVM.State) (n : UInt256)
    (expr : Expr) (ret : Ident) (hf : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int (Int.ofNat n.toNat))) :
    ExecStmt config frame evm (.internalCall "unsigned256" [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int (Int.ofNat n.toNat)) } evm) := by
  let entry : Frame := { frame with locals := (∅ : Store).insert "n" (.int (Int.ofNat n.toNat)) }
  have hn : evalExpr? config entry evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
    simp only [evalExpr?, entry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  have hb : ExecFuncBody config entry evm unsigned256Callable.body
      (.returned entry evm (some [.int (Int.ofNat n.toNat)])) := by
    apply ExecFuncBody.execBlockRet
    apply (ABlock.start.requireStep ?_).returns
    · have hc := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) hn
      simpa only [normalizeInt_uint256_word] using hc
    · simp [evalExpr?, hn, pure, bind, EvalResult.bind, evalBinaryOp?]
  exact ExecStmt.internalCallReturn (callee := unsigned256Callable)
    (argVals := [.int (Int.ofNat n.toNat)])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hf]; exact unsigned256Callable_lookup) rfl hb

theorem cometUnsigned256 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hn : UInt256.slt n ⟨0⟩ = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17954⟩ (n :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (n :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_17954_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega) hn h
  exact ⟨_, _, cometWithExtendedAssetList_block_17963 (immWords := wordsOf (immStore v))
    (by omega) hret r1⟩

end Benchmarks.CompoundIII.Comet

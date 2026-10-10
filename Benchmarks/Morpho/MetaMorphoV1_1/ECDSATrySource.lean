import Benchmarks.Morpho.MetaMorphoV1_1.EcrecoverABI
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! Source execution of signature recovery, including high-s and failed-call branches. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def ecdsaHalfOrder : Nat :=
  57896044618658097711785492504343953926418782139537452191302581570759080747168

def ecdsaTryFunction : FunctionDecl := contract.functions[70]!

def ecdsaFrame (imms : Store) (hash sigV sigR sigS : UInt256) : Frame :=
  ⟨contract, ((((∅ : Store).insert "s" (wordBytes32Value sigS)).insert
    "r" (wordBytes32Value sigR)).insert "v" (uint256Value sigV)).insert
      "hash" (wordBytes32Value hash), imms⟩

def ecdsaInputFrame (imms : Store) (hash sigV sigR sigS : UInt256) : Frame :=
  { ecdsaFrame imms hash sigV sigR sigS with
    locals := ((ecdsaFrame imms hash sigV sigR sigS).locals.insert "precompile"
      (.address (AccountAddress.ofNat 1))).insert "input"
        (.bytes (ecrecoverInput hash sigV sigR sigS)) }

def ecdsaCallFrame (imms : Store) (hash sigV sigR sigS : UInt256) (ok : Bool)
    (out : ByteArray) : Frame :=
  { ecdsaInputFrame imms hash sigV sigR sigS with
    locals := ((ecdsaInputFrame imms hash sigV sigR sigS).locals.insert "ok" (.bool ok)).insert
      "output" (.bytes out) }

def ecdsaHighExpr : Expr :=
  .binary .gt (.cast (.var "s") (.elem (.int (.uint ⟨256, by decide⟩))))
    (.intLit (Int.ofNat ecdsaHalfOrder))

theorem ecdsaHighSource (evm : State) (imms : Store) (hash sigV sigR sigS : UInt256) :
    evalExpr? config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaHighExpr =
      .ok (.bool (decide (ecdsaHalfOrder < sigS.toNat))) := by
  have hs := evalExpr_bytes32ToUint
    (show evalExpr? config (ecdsaFrame imms hash sigV sigR sigS) evm (.var "s") =
      .ok (wordBytes32Value sigS) by
      simp [evalExpr?, ecdsaFrame, Std.HashMap.getElem_insert, EvalResult.ofOption])
  rw [ecdsaHighExpr, evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [hs, evalExpr?, uint256Value, bind, EvalResult.bind, pure, evalBinaryOp?,
    Int.ofNat_eq_natCast, Int.ofNat_lt]

theorem ecdsaTryHighBody (evm : State) (imms : Store) (hash sigV sigR sigS : UInt256)
    (hhigh : ecdsaHalfOrder < sigS.toNat) :
    ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaTryFunction.body
      (.returned (ecdsaFrame imms hash sigV sigR sigS) evm
        (some [.address (AccountAddress.ofNat 0), .int 3, wordBytes32Value sigS])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn (ExecStmt.iteTrue (by
    simpa only [hhigh, decide_true] using ecdsaHighSource evm imms hash sigV sigR sigS) ?_)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExpr?, ecdsaFrame, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure, castValue?]

theorem ecdsaTryPrefix {evm evm' : State} (imms : Store) (hash sigV sigR sigS : UInt256)
    (ok : Bool) (out : ByteArray) {result : ExecResult}
    (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (ok, evm', out) false)
    (htail : ExecBlock config (ecdsaCallFrame imms hash sigV sigR sigS ok out) evm'
      (ecdsaTryFunction.body.drop 4) result) :
    ExecBlock config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaTryFunction.body result := by
  apply ExecBlock.consNormal (ExecStmt.iteFalse (by
    simpa only [hlow, decide_false] using ecdsaHighSource evm imms hash sigV sigR sigS)
      ExecBlock.nil)
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .address (AccountAddress.ofNat 1)) ?_) ?_
  · simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?, EvalResult.ofOption]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl (ecrecoverInputSource
    (hash := hash) (sigV := sigV) (sigR := sigR) (sigS := sigS) ?_ ?_ ?_ ?_)) ?_
  · simp [evalExpr?, ecdsaFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · simp [evalExpr?, ecdsaFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · simp [evalExpr?, ecdsaFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · simp [evalExpr?, ecdsaFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  apply ExecBlock.consNormal _ htail
  have hr : evalExpr? config (ecdsaInputFrame imms hash sigV sigR sigS) evm
      (.var "precompile") = .ok (.address (AccountAddress.ofNat 1)) := by
    simp [evalExpr?, ecdsaInputFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  have hv : evalExpr? config (ecdsaInputFrame imms hash sigV sigR sigS) evm (.intLit 0) =
      .ok (.int 0) := by simp only [evalExpr?, pure]
  have hd : evalExpr? config (ecdsaInputFrame imms hash sigV sigR sigS) evm (.var "input") =
      .ok (.bytes (ecrecoverInput hash sigV sigR sigS)) := by
    simp only [evalExpr?, ecdsaInputFrame, store_get_self, EvalResult.ofOption]
  cases ok
  · exact ExecStmt.lowLevelCallFailure hr hv hd hcall
  · exact ExecStmt.lowLevelCallSuccess hr hv hd hcall

theorem ecdsaTryCallFailed {evm evm' : State} (imms : Store) (hash sigV sigR sigS : UInt256)
    (out : ByteArray) (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (false, evm', out) false) :
    ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaTryFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ecdsaTryPrefix imms hash sigV sigR sigS false out hlow hcall
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simp [evalExpr?, ecdsaCallFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1

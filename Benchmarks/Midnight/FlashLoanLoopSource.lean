import Benchmarks.Midnight.FlashLoanSource
import Benchmarks.Midnight.CollateralSourceFrame
import Benchmarks.Midnight.SafeTransferSource

/-! Source loop conditions, array arguments, and index updates for flash loans. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanLoopCondition : Expr :=
  .binary .lt (.var "i") (.arrayLength .localVar { base := "tokens" })

def flashLoanLoopPost : List Stmt :=
  [.assign .localVar { base := "i" }
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "i") (.intLit 1)))]

def flashLoanLoopArguments (isFrom : Bool) : List Expr :=
  [.index (.var "tokens") (.var "i"), .var "callback"] ++
    (if isFrom then [.env .this] else []) ++ [.index (.var "assets") (.var "i")]

def flashLoanLoopBody (isFrom : Bool) : List Stmt :=
  [.internalCall (if isFrom then "SafeTransferLib_safeTransferFrom" else "SafeTransferLib_safeTransfer")
    (flashLoanLoopArguments isFrom) (if isFrom then "__c2" else "__c0")]

def flashLoanSetIndex (frame : Frame) (i : Nat) : Frame :=
  { frame with locals := frame.locals.insert "i" (.int (Int.ofNat i)) }

theorem flashLoanLoop_shape (isFrom : Bool) :
    flashLoanTransition.body[if isFrom then 8 else 5]! =
      .for [.letDecl "i" (some Model.u256) (.intLit 0)]
        flashLoanLoopCondition flashLoanLoopPost (flashLoanLoopBody isFrom) := by
  cases isFrom <;> rfl

theorem flashLoanSetIndex_spec {frame : Frame} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data) (i : Nat) :
    FlashLoanSourceFrame (flashLoanSetIndex frame i) tokens assets callback data :=
  hf.insert "i" (.int (Int.ofNat i)) (by decide)

theorem flashLoanSetIndex_get (frame : Frame) (i : Nat) :
    (flashLoanSetIndex frame i).locals.get? "i" = some (.int (Int.ofNat i)) := by
  exact store_get_self _ _ _

theorem flashLoanLoopStatement (isFrom : Bool) {frame : Frame} {evm : State}
    {result : ExecResult}
    (h : ExecForLoop config (flashLoanSetIndex frame 0) evm flashLoanLoopCondition
      flashLoanLoopPost (flashLoanLoopBody isFrom) result) :
    ExecStmt config frame evm flashLoanTransition.body[if isFrom then 8 else 5]! result := by
  rw [flashLoanLoop_shape]
  apply ExecStmt.for (ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil) h
  simp [evalExpr?, pure, Int.ofNat_eq_natCast]

theorem flashLoanLoopCondition_eval {frame : Frame} {evm : EVM.State}
    {tokens assets : List UInt256} {callback : AccountAddress} {data : ByteArray} {i : Nat}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) :
    evalExpr? config frame evm flashLoanLoopCondition = .ok (.bool (decide (i < tokens.length))) := by
  simp only [flashLoanLoopCondition, evalExpr?, hi, hf.tokens, readLocalPath?,
    addressWordArrayValues, List.length_map, EvalResult.ofOption, bind, pure,
    EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

theorem flashLoanLoopPost_exec {frame : Frame} {evm : EVM.State} {i : Nat}
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) (hb : i + 1 < UInt256.size) :
    ExecBlock config frame evm flashLoanLoopPost (.ok (flashLoanSetIndex frame (i + 1)) evm) := by
  apply ExecBlock.consNormal (execLocalAssign hi ?_) ExecBlock.nil
  have hin : (UInt256.ofNat i).toNat = i := ulit_toNat' _ (by omega)
  have he := checkedAddSourceOk (cfg := config) (stele := frame) (evm := evm)
    (a := UInt256.ofNat i) (b := UInt256.ofNat 1)
    (by simp only [evalExpr?, hi, EvalResult.ofOption, hin])
    (lhs := .var "i") (rhs := .intLit 1) (by simp only [evalExpr?, pure]; rfl)
    (by simpa only [hin, show (UInt256.ofNat 1).toNat = 1 from rfl] using hb)
  change evalExpr? config frame evm _ = .ok (.int (UInt256.ofNat i + UInt256.ofNat 1).toNat) at he
  rw [uadd_word_ofNat_toNat _ _ (by rw [hin]; exact hb), hin] at he
  exact he

theorem flashLoanTokenIndex_eval {frame : Frame} {evm : EVM.State}
    {tokens assets : List UInt256} {callback : AccountAddress} {data : ByteArray} {i : Nat}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) (ht : i < tokens.length) :
    evalExpr? config frame evm (.index (.var "tokens") (.var "i")) =
      .ok (.address (AccountAddress.ofNat tokens[i].toNat)) := by
  simp only [evalExpr?, hf.tokens, hi, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?]
  rw [if_pos (by simpa only [addressWordArrayValues, List.length_map,
    Int.ofNat_eq_natCast, Int.natCast_nonneg, true_and, Int.ofNat_lt] using ht)]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  rw [lookupNth_get _ i (by simpa only [addressWordArrayValues, List.length_map] using ht)]
  simp only [addressWordArrayValues, List.getElem_map]
  rfl

theorem flashLoanAssetIndex_eval {frame : Frame} {evm : EVM.State}
    {tokens assets : List UInt256} {callback : AccountAddress} {data : ByteArray} {i : Nat}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) (ha : i < assets.length) :
    evalExpr? config frame evm (.index (.var "assets") (.var "i")) =
      .ok (.int (Int.ofNat assets[i].toNat)) := by
  simp only [evalExpr?, hf.assets, hi, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?]
  rw [if_pos (by simpa only [wordArrayValues, List.length_map,
    Int.ofNat_eq_natCast, Int.natCast_nonneg, true_and, Int.ofNat_lt] using ha)]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  rw [lookupNth_get _ i (by simpa only [wordArrayValues, List.length_map] using ha)]
  simp only [wordArrayValues, List.getElem_map]
  rfl

theorem flashLoanLoopArguments_eval (isFrom : Bool) {frame : Frame} {evm : EVM.State}
    {tokens assets : List UInt256} {callback : AccountAddress} {data : ByteArray} {i : Nat}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i)))
    (ht : i < tokens.length) (ha : i < assets.length) :
    evalExprs? config frame evm (flashLoanLoopArguments isFrom) =
      .ok (safeTransferArguments isFrom (AccountAddress.ofNat tokens[i].toNat)
        (if isFrom then callback else evm.executionEnv.source)
        (if isFrom then evm.executionEnv.codeOwner else callback) assets[i]) := by
  have ht' := flashLoanTokenIndex_eval hf hi ht (evm := evm)
  have ha' := flashLoanAssetIndex_eval hf hi ha (evm := evm)
  have hc : evalExpr? config frame evm (.var "callback") = .ok (.address callback) := by
    simp only [evalExpr?, hf.callback, EvalResult.ofOption]
  cases isFrom <;>
    simp only [flashLoanLoopArguments, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append, evalExprs?, ht', ha', hc,
      bind, pure, EvalResult.bind, safeTransferArguments, safeTransferCallArgs]
  simp only [evalExpr?, envValue, pure]

end Benchmarks.Midnight

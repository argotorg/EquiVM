import Benchmarks.UniswapV3.Pool.OracleGrowStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleGrowFunction : FunctionDecl := contract.functions[6]!

theorem oracleGrowLookup :
    lookupCallable? contract "Oracle_grow" = some oracleGrowFunction.toCallable := rfl

def oracleGrowLocals (current next : UInt256) : Store :=
  ((∅ : Store).insert "next" (.int (Int.ofNat next.toNat))).insert "current" (.int (Int.ofNat current.toNat))

def oracleGrowFrame (imms : Store) (current next : UInt256) : Frame :=
  { contract := contract, locals := oracleGrowLocals current next, immutables := imms }

def oracleGrowLoopFrame (imms : Store) (current next : UInt256) (i : Nat) : Frame :=
  { (oracleGrowFrame imms current next) with
    locals := (oracleGrowLocals current next).insert "i" (.int (Int.ofNat i)) }

theorem oracleGrowBind (current next : UInt256) :
    bindParams? oracleGrowFunction.params [.int (Int.ofNat current.toNat), .int (Int.ofNat next.toNat)] =
      some (oracleGrowLocals current next) := rfl

def oracleGrowCondition : Expr := .binary .lt (.var "i") (.var "next")
def oracleGrowPost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩ (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨16, by decide⟩))))]
def oracleGrowBody : List Stmt :=
  [.assign .storage ⟨"observations", [.aindex (.var "i"), .field "blockTimestamp"]⟩ (.intLit 1)]

theorem evalOracleGrowPositive (imms : Store) (evm : EVM.State) (current next : UInt256) :
    evalExpr? config (oracleGrowFrame imms current next) evm
      (.binary .gt (.var "current") (.intLit 0)) = .ok (.bool (decide (0 < current.toNat))) := by
  exact evalExpr_uint256_var_positive evm "current" current (by simp [oracleGrowFrame, oracleGrowLocals])

theorem evalOracleGrowSkip (imms : Store) (evm : EVM.State) (current next : UInt256) :
    evalExpr? config (oracleGrowFrame imms current next) evm
      (.binary .le (.var "next") (.var "current")) = .ok (.bool (decide (next.toNat ≤ current.toNat))) := by
  simp [evalExpr?, oracleGrowFrame, oracleGrowLocals, bind, EvalResult.bind, evalBinaryOp?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem evalOracleGrowCondition (imms : Store) (evm : EVM.State) (locals : Store) (next : UInt256) (i : Nat)
    (hn : locals.get? "next" = some (.int (Int.ofNat next.toNat)))
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm oracleGrowCondition =
      .ok (.bool (decide (i < next.toNat))) := by
  rw [Std.HashMap.get?_eq_getElem?] at hn hi
  simp [evalExpr?, oracleGrowCondition, hn, hi, bind, EvalResult.bind, evalBinaryOp?, EvalResult.ofOption]

theorem oracleGrowStep (imms : Store) (evm : EVM.State) (locals : Store) (i : Nat)
    (hi : i < 65535) (hget : locals.get? "i" = some (.int (Int.ofNat i)))
    (hbase : locals.get? "observations" = none) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm oracleGrowBody
      (.ok {contract := contract, locals := locals, immutables := imms}
        (storeObservationTimestampOne evm (UInt256.ofNat i))) := by
  unfold oracleGrowBody
  refine ExecBlock.consNormal (ExecStmt.assign (value := .int 1)
    (by simp only [evalExpr?, pure]) ?_) ExecBlock.nil
  apply assignObservationTimestampOne _ _ _ "i" (UInt256.ofNat i) hbase
  · rw [ulit_toNat' i (by change i < 2 ^ 256; omega)]; exact hget
  · rw [ulit_toNat' i (by change i < 2 ^ 256; omega)]; exact hi

-- LIBRARY CANDIDATE: a bounded increment survives an unsigned narrowing cast.
theorem evalExpr_uint_increment {cfg : Config} {frame : Frame} {evm : EVM.State} {expr : Expr}
    (width : ABI.BitWidth) (i : Nat)
    (heval : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat i))) (hb : i + 1 < 2 ^ width.val) :
    evalExpr? cfg frame evm (.cast (.binary .add expr (.intLit 1)) (.elem (.int (.uint width)))) =
      .ok (.int (Int.ofNat (i + 1))) := by
  have hn : normalizeInt (.uint width) (Int.ofNat i + 1) = Int.ofNat (i + 1) := by
    rw [normalizeInt_uint_eq_self _ _ (by change 0 ≤ (i : Int) + 1; omega) (by
      simp only [EVM.twoPow, Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat]
      exact_mod_cast hb)]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
  simp only [evalExpr?, heval, bind, EvalResult.bind, pure, evalBinaryOp?, castValue?, hn, EvalResult.ofOption]

theorem oracleGrowIncrement (imms : Store) (evm : EVM.State) (locals : Store) (i : Nat)
    (hi : i < 65535) (hget : locals.get? "i" = some (.int (Int.ofNat i))) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm oracleGrowPost
      (.ok { contract := contract, locals := locals.insert "i" (.int (Int.ofNat (i + 1))),
             immutables := imms } evm) := by
  have heval := evalExpr_uint_increment (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms})
    ⟨16, by decide⟩ i (evalExpr_var_get hget) (by change i + 1 < 65536; omega)
  exact ExecBlock.consNormal (ExecStmt.assign heval (assignLocalVarBase_frame hget)) ExecBlock.nil

theorem oracleGrowLoop (imms : Store) (evm : EVM.State) (locals : Store) (next : UInt256) (i count : Nat)
    (hnext : next.toNat < 2 ^ 16) (hsum : i + count = next.toNat)
    (hn : locals.get? "next" = some (.int (Int.ofNat next.toNat)))
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) (hbase : locals.get? "observations" = none) :
    ∃ locals', ExecForLoop config {contract := contract, locals := locals, immutables := imms} evm
      oracleGrowCondition oracleGrowPost oracleGrowBody
      (.ok {contract := contract, locals := locals', immutables := imms} (oracleGrowState evm i count)) ∧
      locals'.get? "next" = some (.int (Int.ofNat next.toNat)) := by
  induction count generalizing evm locals i with
  | zero =>
      have heq : i = next.toNat := by omega
      refine ⟨locals, ExecForLoop.falseDone ?_, hn⟩
      simpa only [heq, Nat.lt_irrefl, decide_false] using evalOracleGrowCondition imms evm locals next i hn hi
  | succ count ih =>
      have hib : i < 65535 := by change next.toNat < 65536 at hnext; omega
      have hn' : (locals.insert "i" (.int (Int.ofNat (i + 1)))).get? "next" =
          some (.int (Int.ofNat next.toNat)) := by
        simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hn
      have hi' : (locals.insert "i" (.int (Int.ofNat (i + 1)))).get? "i" =
          some (.int (Int.ofNat (i + 1))) := by simp
      have hb' : (locals.insert "i" (.int (Int.ofNat (i + 1)))).get? "observations" = none := by
        simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hbase
      obtain ⟨locals', hloop, hnFinal⟩ := ih (storeObservationTimestampOne evm (UInt256.ofNat i))
        (locals.insert "i" (.int (Int.ofNat (i + 1)))) (i + 1) (by omega) hn' hi' hb'
      refine ⟨locals', ExecForLoop.iterate ?_ (oracleGrowStep imms evm locals i hib hi hbase)
        (oracleGrowIncrement imms _ locals i hib hi) hloop, hnFinal⟩
      simpa only [show i < next.toNat by omega, decide_true] using
        evalOracleGrowCondition imms evm locals next i hn hi

def oracleGrowResult (current next : UInt256) : UInt256 :=
  if current.toNat < next.toNat then next else current

theorem oracleGrowRevertsZero (imms : Store) (evm : EVM.State) (next : UInt256) :
    ExecFuncBody config (oracleGrowFrame imms ⟨0⟩ next) evm oracleGrowFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa using evalOracleGrowPositive imms evm ⟨0⟩ next

theorem oracleGrowReturns (imms : Store) (evm : EVM.State) (current next : UInt256)
    (hpos : 0 < current.toNat) (hnext : next.toNat < 2 ^ 16) :
    ∃ frame, ExecFuncBody config (oracleGrowFrame imms current next) evm oracleGrowFunction.body
      (.returned frame (oracleGrowState evm current.toNat (next.toNat - current.toNat))
        (some [.int (Int.ofNat (oracleGrowResult current next).toNat)])) := by
  by_cases hgrow : current.toNat < next.toNat
  · obtain ⟨localsFinal, hloop, hgetFinal⟩ := oracleGrowLoop imms evm
      (oracleGrowLoopFrame imms current next current.toNat).locals next current.toNat
      (next.toNat - current.toNat) hnext (by omega)
      (by simp [oracleGrowLoopFrame, oracleGrowLocals, Std.HashMap.getElem_insert])
      (by simp [oracleGrowLoopFrame]) (by simp [oracleGrowLoopFrame, oracleGrowLocals])
    refine ⟨{contract := contract, locals := localsFinal, immutables := imms}, ?_⟩
    apply ExecFuncBody.execBlockRet
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [hpos, decide_true] using evalOracleGrowPositive imms evm current next
    refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
    · simpa only [show ¬ next.toNat ≤ current.toNat by omega, decide_false] using
        evalOracleGrowSkip imms evm current next
    refine ExecBlock.consNormal (ExecStmt.for ?_ hloop) ?_
    · exact ExecBlock.consNormal (ExecStmt.letDecl (name := "i") (ty := some (.elem (.int (.uint ⟨16, by decide⟩)))) (value := .int (Int.ofNat current.toNat))
        (evalExpr_var_get (by simp [oracleGrowFrame, oracleGrowLocals]))) ExecBlock.nil
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [oracleGrowResult, if_pos hgrow, evalExprs?, evalExpr?, hgetFinal,
      bind, EvalResult.bind, pure, EvalResult.ofOption]
  · have hcount : next.toNat - current.toNat = 0 := by omega
    refine ⟨oracleGrowFrame imms current next, ?_⟩
    rw [hcount, oracleGrowState, oracleGrowResult, if_neg hgrow]
    apply ExecFuncBody.execBlockRet
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [hpos, decide_true] using evalOracleGrowPositive imms evm current next
    apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
    · simpa only [show next.toNat ≤ current.toNat by omega, decide_true] using
        evalOracleGrowSkip imms evm current next
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp [evalExprs?, evalExpr?, oracleGrowFrame, oracleGrowLocals, bind, EvalResult.bind, pure, EvalResult.ofOption, Std.HashMap.getElem_insert]

end Benchmarks.UniswapV3.Pool

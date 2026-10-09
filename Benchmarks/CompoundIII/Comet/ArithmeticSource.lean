import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: division by zero propagates a source revert.
theorem divSourceZero {cfg solm evm lhs rhs a}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int a))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int 0)) :
    evalExpr? cfg solm evm (.binary .div lhs rhs) = .revert := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, ↓reduceIte]

def mulFactorWord (n factor : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul n factor) ⟨1000000000000000000⟩

def mulFactorCallable : CallableDecl :=
  { params := [⟨"n", .elem (.int (.uint ⟨256, by decide⟩))⟩,
      ⟨"factor", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body := [.return [.binary .div
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "n") (.var "factor")))
      (.intLit 1000000000000000000)]] }

def mulFactorLocals (n factor : UInt256) : Store :=
  ((∅ : Store).insert "factor" (.int factor.toNat)).insert "n" (.int n.toNat)

theorem mulFactorCallable_lookup :
    lookupCallable? contract "mulFactor" = some mulFactorCallable := rfl

theorem mulFactorCallable_result (evm : EVM.State) (imms : Store) (n factor : UInt256) :
    let frame : Frame := { contract := contract, locals := mulFactorLocals n factor, immutables := imms }
    if n.toNat * factor.toNat < UInt256.size then
      ExecFuncBody config frame evm mulFactorCallable.body
        (.returned frame evm (some [.int (mulFactorWord n factor).toNat]))
    else ExecFuncBody config frame evm mulFactorCallable.body .reverted := by
  dsimp only
  let frame : Frame :=
    { contract := contract, locals := mulFactorLocals n factor, immutables := imms }
  have hn : evalExpr? config frame evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
    simp only [evalExpr?, frame, mulFactorLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hf : evalExpr? config frame evm (.var "factor") = .ok (.int (Int.ofNat factor.toNat)) := by
    simp only [evalExpr?, frame, mulFactorLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  split_ifs with hfit
  · apply ExecFuncBody.execBlockRet
    apply ABlock.start.returns
    exact divSourceOk (checkedMulSourceOk hn hf hfit)
      (by norm_num [evalExpr?, pure, UInt256.toNat, UInt256.size]) (by decide)
  · apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert
    apply ExecStmt.returnRevert
    have hmul := checkedMulSourceOverflow hn hf (by omega)
    change evalExprs? config frame evm _ = _
    simp only [evalExprs?, evalExpr?, hmul, bind, EvalResult.bind]

theorem mulFactor_call_ok (frame : Frame) (evm : EVM.State) (n factor : UInt256)
    (nExpr factorExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hn : evalExpr? config frame evm nExpr = .ok (.int n.toNat))
    (hf : evalExpr? config frame evm factorExpr = .ok (.int factor.toNat))
    (hfit : n.toNat * factor.toNat < UInt256.size) :
    ExecStmt config frame evm (.internalCall "mulFactor" [nExpr, factorExpr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int (mulFactorWord n factor).toNat) } evm) := by
  have hb := mulFactorCallable_result evm frame.immutables n factor
  rw [if_pos hfit] at hb
  exact ExecStmt.internalCallReturn (callee := mulFactorCallable) (locals := mulFactorLocals n factor)
    (cfg := config) (solm := frame) (evm := evm)
    (args := [nExpr, factorExpr]) (argVals := [.int n.toNat, .int factor.toNat])
    (by simp only [evalExprs?, hn, hf, pure, bind, EvalResult.bind])
    (by rw [hc]; exact mulFactorCallable_lookup) rfl (by simpa only [hc] using hb)

theorem mulFactor_call_revert (frame : Frame) (evm : EVM.State) (n factor : UInt256)
    (nExpr factorExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hn : evalExpr? config frame evm nExpr = .ok (.int n.toNat))
    (hf : evalExpr? config frame evm factorExpr = .ok (.int factor.toNat))
    (hfit : ¬ n.toNat * factor.toNat < UInt256.size) :
    ExecStmt config frame evm (.internalCall "mulFactor" [nExpr, factorExpr] ret) .reverted := by
  have hb := mulFactorCallable_result evm frame.immutables n factor
  rw [if_neg hfit] at hb
  exact ExecStmt.internalCallRevert (callee := mulFactorCallable) (locals := mulFactorLocals n factor)
    (cfg := config) (solm := frame) (evm := evm)
    (args := [nExpr, factorExpr]) (argVals := [.int n.toNat, .int factor.toNat])
    (by simp only [evalExprs?, hn, hf, pure, bind, EvalResult.bind])
    (by rw [hc]; exact mulFactorCallable_lookup) rfl (by simpa only [hc] using hb)

def safe64Callable : CallableDecl :=
  { params := [⟨"n", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨64, by decide⟩))]
    body := [.require (.binary .le (.var "n") (.intLit 18446744073709551615)),
      .return [.cast (.var "n") (.elem (.int (.uint ⟨64, by decide⟩)))]] }

theorem safe64Callable_lookup :
    lookupCallable? contract "safe64" = some safe64Callable := rfl

theorem safe64Callable_result (evm : EVM.State) (imms : Store) (n : UInt256) :
    let frame : Frame :=
      { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
    if n.toNat < 2^64 then
      ExecFuncBody config frame evm safe64Callable.body
        (.returned frame evm (some [.int n.toNat]))
    else ExecFuncBody config frame evm safe64Callable.body .reverted := by
  dsimp only
  let frame : Frame :=
    { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
  have hn : evalExpr? config frame evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
    simp only [evalExpr?, frame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hcond := naturalLeSource hn (cfg := config) (frame := frame) (evm := evm)
    (rhs := .intLit 18446744073709551615) (b := 18446744073709551615)
    (by simp [evalExpr?, pure])
  split_ifs with hfit
  · apply ExecFuncBody.execBlockRet
    have hg := hcond.trans (show _ = .ok (.bool true) by rw [decide_eq_true (by omega)])
    apply (ABlock.start.requireStep hg).returns
    have he := evalExpr_cast_int (intType := .uint ⟨64, by decide⟩) hn
    have hnorm : normalizeInt (.uint ⟨64, by decide⟩) (Int.ofNat n.toNat) = Int.ofNat n.toNat :=
      normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (by
        change (n.toNat : Int) < (2^64 : Nat)
        exact_mod_cast hfit)
    rw [hnorm] at he
    exact he
  · apply ExecFuncBody.execBlockRevert
    apply ABlock.start.requireRevert
    change evalExpr? config frame evm _ = _
    exact hcond.trans (by rw [decide_eq_false (by omega)])

theorem safe64_call_ok (frame : Frame) (evm : EVM.State) (n : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hn : evalExpr? config frame evm expr = .ok (.int n.toNat)) (hfit : n.toNat < 2^64) :
    ExecStmt config frame evm (.internalCall "safe64" [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int n.toNat) } evm) := by
  have hb := safe64Callable_result evm frame.immutables n
  rw [if_pos hfit] at hb
  exact ExecStmt.internalCallReturn (callee := safe64Callable)
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.int n.toNat])
    (by simp only [evalExprs?, hn, pure, bind, EvalResult.bind])
    (by rw [hc]; exact safe64Callable_lookup) rfl (by simpa only [hc] using hb)

theorem safe64_call_revert (frame : Frame) (evm : EVM.State) (n : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hn : evalExpr? config frame evm expr = .ok (.int n.toNat)) (hfit : ¬ n.toNat < 2^64) :
    ExecStmt config frame evm (.internalCall "safe64" [expr] ret) .reverted := by
  have hb := safe64Callable_result evm frame.immutables n
  rw [if_neg hfit] at hb
  exact ExecStmt.internalCallRevert (callee := safe64Callable)
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.int n.toNat])
    (by simp only [evalExprs?, hn, pure, bind, EvalResult.bind])
    (by rw [hc]; exact safe64Callable_lookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet

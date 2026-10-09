import Benchmarks.Morpho.MorphoBlue.MarketFrame
import Benchmarks.Morpho.MorphoBlue.MarketWrites
import Benchmarks.Morpho.MorphoBlue.TaylorSource
import Benchmarks.Morpho.MorphoBlue.MarketStorageCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- GENERALIZES evalExpr_checkedSub256_revert to frames containing immutables.
theorem evalCheckedSubUnderflow {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat))) (hlt : x.toNat < y.toNat) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨256, by decide⟩) (.binary .sub ex ey)) = .revert := by
  simp only [evalExpr?, hx, hy, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; left; omega)]

-- LIBRARY CANDIDATE: source equality against zero for a machine-word integer.
theorem evalWordEqZero {cfg : Config} {frame : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm e = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? cfg frame evm (.binary .eq e (.intLit 0)) = .ok (.bool (decide (w = ⟨0⟩))) := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro h
    exact uint256_toNat_eq_zero (Int.ofNat.inj h)
  · intro h
    rw [h]
    rfl

abbrev accrueInterestFunction : FunctionDecl := contract.functions[1]!

def accrueStart (p : MarketParamsWords) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "id" (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id))).insert
      "marketParams" p.value }

def accrueElapsed (σ : AccountMap) (I : ExecutionEnv) (p : MarketParamsWords) : UInt256 :=
  UInt256.sub (UInt256.ofNat I.header.timestamp) (marketFieldWord σ I p.id 4)

def accrueAfterElapsed (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) : Frame :=
  { accrueStart p imms with locals := (accrueStart p imms).locals.insert "elapsed" (.int (Int.ofNat elapsed.toNat)) }

theorem accrueStart_locals (p : MarketParamsWords) (imms : Store) :
    MarketLocals p (accrueStart p imms).locals := by
  constructor
  · simp only [accrueStart, store_get_self]
  · simp only [accrueStart, store_get_ne (k := "marketParams") (a := "id") _ _ (by decide), store_get_self]
  · simp [accrueStart]
  · simp [accrueStart]
  · simp [accrueStart]

theorem accrueElapsed_locals (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) :
    MarketLocals p (accrueAfterElapsed p imms elapsed).locals :=
  (accrueStart_locals p imms).insert "elapsed" _ (by decide)

theorem accrue_eval_elapsed (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) (evm : EVM.State) :
    evalExpr? config (accrueAfterElapsed p imms elapsed) evm (.var "elapsed") =
      .ok (.int (Int.ofNat elapsed.toNat)) := by
  simp only [evalExpr?, accrueAfterElapsed, store_get_self, EvalResult.ofOption]

theorem morphoAccrueSourceUnderflow (p : MarketParamsWords) (evm : EVM.State) (imms : Store)
    (hunder : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat) :
    ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.letDeclRevert
  exact evalCheckedSubUnderflow (by simp only [evalExpr?, envValue, pure])
    ((accrueStart_locals p imms).evalField imms evm ⟨4, by decide⟩) hunder

theorem morphoAccrueSourceElapsed (p : MarketParamsWords) (evm : EVM.State) (imms : Store)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ABlock config evm (accrueStart p imms) accrueInterestFunction.body
      (accrueAfterElapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p))
      (accrueInterestFunction.body.drop 1) := by
  exact ABlock.start.letStep (evalExpr_uint256_sub (by simp only [evalExpr?, envValue, pure])
    ((accrueStart_locals p imms).evalField imms evm ⟨4, by decide⟩) htime)

theorem morphoAccrueSourceZeroElapsed (p : MarketParamsWords) (evm : EVM.State) (imms : Store)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hz : accrueElapsed evm.accountMap evm.executionEnv p = ⟨0⟩) :
    ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body
      (.returned (accrueAfterElapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p)) evm (some [])) := by
  apply ExecFuncBody.execBlockRet
  apply (morphoAccrueSourceElapsed p evm imms htime).run
  apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ (ExecBlock.consReturn (ExecStmt.return rfl)))
  simpa only [hz, decide_true] using evalWordEqZero
    (accrue_eval_elapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p) evm)

theorem morphoAccrueSourceNonzeroElapsed (p : MarketParamsWords) (evm : EVM.State) (imms : Store)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hn : accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩) :
    ABlock config evm (accrueStart p imms) accrueInterestFunction.body
      (accrueAfterElapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p))
      (accrueInterestFunction.body.drop 2) := by
  apply advancePureBlock (morphoAccrueSourceElapsed p evm imms htime)
  apply ExecStmt.iteFalse ?_ ExecBlock.nil
  simpa only [decide_eq_false hn] using evalWordEqZero
    (accrue_eval_elapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p) evm)

theorem morphoAccrueTimestampAssign (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (h : MarketLocals p locals) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      accrueInterestFunction.body[3]!
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storeMarketLastUpdate evm p.id (halfWord false (UInt256.ofNat evm.executionEnv.header.timestamp)))) := by
  exact ExecStmt.assign (evalCastUint128 (by simp only [evalExpr?, envValue, pure]))
    (assignMarketLastUpdate evm locals imms (.var "id") p.id _ (halfWord_bound false _) h.market (h.evalId imms evm))

theorem morphoAccrueSourceNoIrm (p : MarketParamsWords) (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hn : accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩) (hi0 : p.irm = ⟨0⟩) :
    ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body
      (.returned (accrueAfterElapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p))
        (storeMarketLastUpdate evm p.id (halfWord false (UInt256.ofNat evm.executionEnv.header.timestamp))) none) := by
  apply ExecFuncBody.execBlockOK
  apply (morphoAccrueSourceNonzeroElapsed p evm imms htime hn).run
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
  · exact ExecBlock.consNormal
      (morphoAccrueTimestampAssign p _ imms evm (accrueElapsed_locals p imms _)) ExecBlock.nil
  · simpa only [hi0, ne_eq, not_true_eq_false, decide_false] using
      (accrueElapsed_locals p imms _).evalIrmNonzero hc imms evm

theorem morphoAccrueSourceNoIrmStatic (p : MarketParamsWords) (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hn : accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩) (hi0 : p.irm = ⟨0⟩)
    (hp : evm.executionEnv.perm = false) :
    ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply (morphoAccrueSourceNonzeroElapsed p evm imms htime hn).run
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
  · exact ExecBlock.consStatic (execStmt_assign_static
      (morphoAccrueTimestampAssign p _ imms evm (accrueElapsed_locals p imms _)) hp)
  · simpa only [hi0, ne_eq, not_true_eq_false, decide_false] using
      (accrueElapsed_locals p imms _).evalIrmNonzero hc imms evm

end Benchmarks.Morpho.MorphoBlue

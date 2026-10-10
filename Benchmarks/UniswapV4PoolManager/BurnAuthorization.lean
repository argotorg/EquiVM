import Benchmarks.UniswapV4PoolManager.TransferFromSource

/-! The authorization and allowance step of the internal ERC6909 burn helper. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev burnFromFunction : FunctionDecl := contract.functions[47]!

structure BurnFromArgs (f : Frame) (sender id amount : UInt256) : Prop where
  contract_eq : f.contract = contract
  from_get : f.locals.get? "from" = some (.address (AccountAddress.ofNat sender.toNat))
  id_get : f.locals.get? "id" = some (.int (Int.ofNat id.toNat))
  amount_get : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))
  operator_get : f.locals.get? "isOperator" = none
  allowance_get : f.locals.get? "allowance" = none

def burnAllowedFrame (f : Frame) (allowed : UInt256) : Frame :=
  {f with locals := f.locals.insert "senderAllowance" (.int (Int.ofNat allowed.toNat))}

theorem burnAllowedFrame_args {f : Frame} {sender id amount : UInt256}
    (h : BurnFromArgs f sender id amount) (allowed : UInt256) :
    BurnFromArgs (burnAllowedFrame f allowed) sender id amount := by
  refine ⟨h.contract_eq, ?_, ?_, ?_, ?_, ?_⟩
  · exact (store_get_ne _ _ (by decide : ("senderAllowance" == "from") = false)).trans h.from_get
  · exact (store_get_ne _ _ (by decide : ("senderAllowance" == "id") = false)).trans h.id_get
  · exact (store_get_ne _ _ (by decide : ("senderAllowance" == "amount") = false)).trans h.amount_get
  · exact (store_get_ne _ _ (by decide : ("senderAllowance" == "isOperator") = false)).trans h.operator_get
  · exact (store_get_ne _ _ (by decide : ("senderAllowance" == "allowance") = false)).trans h.allowance_get

def burnAuthCond : Expr :=
  .binary .and (.binary .ne (.var "from") (.var "sender"))
    (.unary .not (.storage {base := "isOperator", steps := [.mindex (.var "from"), .mindex (.var "sender")]}))

theorem burnAuthCond_eval {f : Frame} {evm : EVM.State} {sender id amount : UInt256}
    (h : BurnFromArgs f sender id amount) (hcs : sender.toNat < EVM.addressModulus)
    (hc : f.locals.get? "sender" = some (.address evm.executionEnv.source)) :
    evalExpr? config f evm burnAuthCond = .ok (.bool (decide (transferFromNeedsAllowance evm sender))) := by
  have hs := evalLocalValue (cfg := config) (evm := evm) h.from_get
  have hcaller := evalLocalValue (cfg := config) (evm := evm) hc
  have hop := isOperatorRead sender (accountWord evm.executionEnv.source) h.contract_eq hcs
    (accountWord_canonical _) h.operator_get hs (by simpa only [accountWord_address] using hcaller)
  rw [wordToElemBool] at hop
  have hn := evalAndBool (evalNeAddress hs hcaller) (evalNotBool hop)
  have heq : AccountAddress.ofNat sender.toNat ≠ evm.executionEnv.source ↔
      accountWord evm.executionEnv.source ≠ sender := by
    rw [ne_comm]
    exact (accountWord_eq_iff evm.executionEnv.source sender hcs).not
  simpa only [transferFromNeedsAllowance, heq, Bool.not_not, Bool.decide_and] using hn

def burnAuthResult (f : Frame) (evm : EVM.State) (sender id amount : UInt256) : ExecResult :=
  if transferFromNeedsAllowance evm sender then
    let allowed := transferFromAllowed evm sender id
    let f' := burnAllowedFrame f allowed
    if allowed = maxAllowanceWord then .ok f' evm else
    if amount.toNat ≤ allowed.toNat then
      if evm.executionEnv.perm = false then .staticViolation
      else .ok f' (transferFromAllowancePost evm sender id amount)
    else .reverted
  else .ok f evm

theorem burnAuthExec {f : Frame} {evm : EVM.State} {sender id amount : UInt256}
    (h : BurnFromArgs f sender id amount) (hcs : sender.toNat < EVM.addressModulus)
    (hc : f.locals.get? "sender" = some (.address evm.executionEnv.source)) :
    ExecStmt config f evm burnFromFunction.body[1]! (burnAuthResult f evm sender id amount) := by
  have hg := burnAuthCond_eval h hcs hc
  by_cases hneed : transferFromNeedsAllowance evm sender
  · rw [burnAuthResult, if_pos hneed]
    apply ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hneed]))
    have hcaller : evalExpr? config f evm (.var "sender") =
        .ok (.address (AccountAddress.ofNat (accountWord evm.executionEnv.source).toNat)) := by
      rw [accountWord_address]; exact evalLocalValue hc
    have hread := allowanceRead sender (accountWord evm.executionEnv.source) id h.contract_eq hcs
      (accountWord_canonical _) h.allowance_get (evalLocalValue h.from_get) hcaller (evalLocalValue h.id_get)
    refine ExecBlock.consNormal (ExecStmt.letDecl hread) ?_
    let allowed := transferFromAllowed evm sender id
    let f' := burnAllowedFrame f allowed
    have ha := burnAllowedFrame_args h allowed
    have hallowed : f'.locals.get? "senderAllowance" = some (.int (Int.ofNat allowed.toNat)) := store_get_self _ _ _
    have hc' : f'.locals.get? "sender" = some (.address evm.executionEnv.source) :=
      (store_get_ne _ _ (by decide : ("senderAllowance" == "sender") = false)).trans hc
    have hcond : evalExpr? config f' evm (.binary .ne (.var "senderAllowance")
        (.intLit 115792089237316195423570985008687907853269984665640564039457584007913129639935)) =
        .ok (.bool (decide (allowed ≠ maxAllowanceWord))) :=
      evalNeWords (evalLocalValue hallowed) (by simp only [evalExpr?]; rfl)
    by_cases hmax : allowed = maxAllowanceWord
    · rw [if_pos hmax]
      exact ExecBlock.consNormal (ExecStmt.iteFalse
        (hcond.trans (by rw [decide_eq_false (not_not.mpr hmax)])) ExecBlock.nil) ExecBlock.nil
    · rw [if_neg hmax]
      have hcondTrue := hcond.trans (by rw [decide_eq_true hmax])
      by_cases hsub : amount.toNat ≤ allowed.toNat
      · rw [if_pos hsub]
        have heval := evalExpr_uint256_sub (cfg := config) (evm := evm)
          (evalLocalValue hallowed) (evalLocalValue ha.amount_get) hsub
        have hwrite := allowanceWrite (evm := evm) (e1 := .var "sender")
          sender (accountWord evm.executionEnv.source) id (UInt256.sub allowed amount)
          ha.contract_eq hcs (accountWord_canonical _) ha.allowance_get (evalLocalValue ha.from_get)
          (by rw [accountWord_address]; exact evalLocalValue hc') (evalLocalValue ha.id_get)
        by_cases hp : evm.executionEnv.perm = false
        · rw [if_pos hp]
          exact ExecBlock.consStatic (ExecStmt.iteTrue hcondTrue
            (ExecBlock.consStatic (ExecStmt.assignStatic heval hwrite hp)))
        · rw [if_neg hp]
          exact ExecBlock.consNormal (ExecStmt.iteTrue hcondTrue
            (ExecBlock.consNormal (ExecStmt.assign heval hwrite) ExecBlock.nil)) ExecBlock.nil
      · rw [if_neg hsub]
        exact ExecBlock.consRevert (ExecStmt.iteTrue hcondTrue
          (ExecBlock.consRevert (ExecStmt.assignExprRevert
            (checkedSubSourceUnderflow (evalLocalValue hallowed) (evalLocalValue ha.amount_get) (Nat.lt_of_not_ge hsub)))))
  · rw [burnAuthResult, if_neg hneed]
    exact ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hneed])) ExecBlock.nil

end Benchmarks.UniswapV4PoolManager

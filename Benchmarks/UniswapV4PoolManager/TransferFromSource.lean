import Benchmarks.UniswapV4PoolManager.BalanceTransfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

structure TransferFromArgs (f : Frame) (sender receiver id amount : UInt256) : Prop where
  contract_eq : f.contract = contract
  sender_get : f.locals.get? "sender" = some (.address (AccountAddress.ofNat sender.toNat))
  receiver_get : f.locals.get? "receiver" = some (.address (AccountAddress.ofNat receiver.toNat))
  id_get : f.locals.get? "id" = some (.int (Int.ofNat id.toNat))
  amount_get : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))
  balance_get : f.locals.get? "balanceOf" = none
  operator_get : f.locals.get? "isOperator" = none
  allowance_get : f.locals.get? "allowance" = none

def transferFromNeedsAllowance (evm : EVM.State) (sender : UInt256) : Prop :=
  accountWord evm.executionEnv.source ≠ sender ∧
    operatorWord evm sender (accountWord evm.executionEnv.source) = ⟨0⟩

instance (evm : EVM.State) (sender : UInt256) : Decidable (transferFromNeedsAllowance evm sender) :=
  inferInstanceAs (Decidable (_ ∧ _))

def transferFromAuthCond : Expr :=
  .binary .and (.binary .ne (.env .caller) (.var "sender"))
    (.unary .not (.storage {base := "isOperator", steps := [.mindex (.var "sender"), .mindex (.env .caller)]}))

abbrev transferFromAuthStmt : Stmt := transferFromTransition.body[3]!

abbrev maxAllowanceWord : UInt256 := ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩

def transferFromAllowed (evm : EVM.State) (sender id : UInt256) : UInt256 :=
  allowanceWord evm sender (accountWord evm.executionEnv.source) id

def transferFromAllowedFrame (f : Frame) (allowed : UInt256) : Frame :=
  {f with locals := f.locals.insert "allowed" (.int (Int.ofNat allowed.toNat))}

def transferFromAllowancePost (evm : EVM.State) (sender id amount : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (allowanceSlot sender (accountWord evm.executionEnv.source) id)
    (UInt256.sub (transferFromAllowed evm sender id) amount)

def transferFromAuthResult (f : Frame) (evm : EVM.State) (sender id amount : UInt256) : ExecResult :=
  if transferFromNeedsAllowance evm sender then
    let allowed := transferFromAllowed evm sender id
    let f' := transferFromAllowedFrame f allowed
    if allowed = maxAllowanceWord then .ok f' evm else
    if amount.toNat ≤ allowed.toNat then
      if evm.executionEnv.perm = false then .staticViolation
      else .ok f' (transferFromAllowancePost evm sender id amount)
    else .reverted
  else .ok f evm

theorem transferFromAllowedFrame_args {f : Frame} {sender receiver id amount : UInt256}
    (h : TransferFromArgs f sender receiver id amount) (allowed : UInt256) :
    TransferFromArgs (transferFromAllowedFrame f allowed) sender receiver id amount := by
  refine ⟨h.contract_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (store_get_ne _ _ (by decide : ("allowed" == "sender") = false)).trans h.sender_get
  · exact (store_get_ne _ _ (by decide : ("allowed" == "receiver") = false)).trans h.receiver_get
  · exact (store_get_ne _ _ (by decide : ("allowed" == "id") = false)).trans h.id_get
  · exact (store_get_ne _ _ (by decide : ("allowed" == "amount") = false)).trans h.amount_get
  · exact (store_get_ne _ _ (by decide : ("allowed" == "balanceOf") = false)).trans h.balance_get
  · exact (store_get_ne _ _ (by decide : ("allowed" == "isOperator") = false)).trans h.operator_get
  · exact (store_get_ne _ _ (by decide : ("allowed" == "allowance") = false)).trans h.allowance_get

theorem transferFromAuthCond_eval {f : Frame} {evm : EVM.State} {sender receiver id amount : UInt256}
    (h : TransferFromArgs f sender receiver id amount) (hcs : sender.toNat < EVM.addressModulus) :
    evalExpr? config f evm transferFromAuthCond = .ok (.bool (decide (transferFromNeedsAllowance evm sender))) := by
  have hs := evalLocalValue (cfg := config) (evm := evm) h.sender_get
  have hc : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
    simp only [evalExpr?, envValue, pure]
  have hop := isOperatorRead sender (accountWord evm.executionEnv.source) h.contract_eq hcs
    (accountWord_canonical _) h.operator_get hs (by simpa only [accountWord_address] using hc)
  rw [wordToElemBool] at hop
  have hne := evalNeAddress hc hs
  have hn := evalAndBool hne (evalNotBool hop)
  simpa only [transferFromNeedsAllowance, ne_eq,
    accountWord_eq_iff evm.executionEnv.source sender hcs,
    Bool.not_not, Bool.decide_and] using hn

theorem transferFromAuthExec {f : Frame} {evm : EVM.State} {sender receiver id amount : UInt256}
    (h : TransferFromArgs f sender receiver id amount) (hcs : sender.toNat < EVM.addressModulus) :
    ExecStmt config f evm transferFromAuthStmt (transferFromAuthResult f evm sender id amount) := by
  have hg := transferFromAuthCond_eval (evm := evm) h hcs
  by_cases hneed : transferFromNeedsAllowance evm sender
  · rw [transferFromAuthResult, if_pos hneed]
    apply ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hneed]))
    have hc : evalExpr? config f evm (.env .caller) =
        .ok (.address (AccountAddress.ofNat (accountWord evm.executionEnv.source).toNat)) := by
      rw [accountWord_address]; simp only [evalExpr?, envValue, pure]
    have hread := allowanceRead sender (accountWord evm.executionEnv.source) id h.contract_eq hcs
      (accountWord_canonical _) h.allowance_get (evalLocalValue h.sender_get) hc (evalLocalValue h.id_get)
    refine ExecBlock.consNormal (ExecStmt.letDecl hread) ?_
    let allowed := transferFromAllowed evm sender id
    let f' := transferFromAllowedFrame f allowed
    have ha := transferFromAllowedFrame_args h allowed
    have hallowed : f'.locals.get? "allowed" = some (.int (Int.ofNat allowed.toNat)) := store_get_self _ _ _
    have hcond : evalExpr? config f' evm (.binary .ne (.var "allowed")
        (.intLit 115792089237316195423570985008687907853269984665640564039457584007913129639935)) =
        .ok (.bool (decide (allowed ≠ maxAllowanceWord))) :=
      evalNeWords (evalLocalValue hallowed) (by simp only [evalExpr?]; rfl)
    by_cases hmax : allowed = maxAllowanceWord
    · rw [if_pos hmax]
      exact ExecBlock.consNormal (ExecStmt.iteFalse (hcond.trans (by simp only [hmax, ne_eq, not_true_eq_false, decide_false])) ExecBlock.nil) ExecBlock.nil
    · rw [if_neg hmax]
      have hcondTrue := hcond.trans (by rw [decide_eq_true hmax])
      by_cases hsub : amount.toNat ≤ allowed.toNat
      · rw [if_pos hsub]
        have heval := evalExpr_uint256_sub (cfg := config) (evm := evm)
          (evalLocalValue hallowed) (evalLocalValue ha.amount_get) hsub
        have hwrite := allowanceWrite (evm := evm) (e1 := .env .caller)
          sender (accountWord evm.executionEnv.source) id (UInt256.sub allowed amount)
          ha.contract_eq hcs (accountWord_canonical _) ha.allowance_get (evalLocalValue ha.sender_get)
          (by rw [accountWord_address]; simp only [evalExpr?, envValue, pure]) (evalLocalValue ha.id_get)
        by_cases hperm : evm.executionEnv.perm = false
        · rw [if_pos hperm]
          exact ExecBlock.consStatic (ExecStmt.iteTrue hcondTrue
            (ExecBlock.consStatic (ExecStmt.assignStatic heval hwrite hperm)))
        · rw [if_neg hperm]
          exact ExecBlock.consNormal (ExecStmt.iteTrue hcondTrue
            (ExecBlock.consNormal (ExecStmt.assign heval hwrite) ExecBlock.nil)) ExecBlock.nil
      · rw [if_neg hsub]
        exact ExecBlock.consRevert (ExecStmt.iteTrue hcondTrue
          (ExecBlock.consRevert (ExecStmt.assignExprRevert
            (checkedSubSourceUnderflow (evalLocalValue hallowed) (evalLocalValue ha.amount_get) (Nat.lt_of_not_ge hsub)))))
  · rw [transferFromAuthResult, if_neg hneed]
    exact ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hneed])) ExecBlock.nil

theorem transferFromBodyAfterAuth {evm evm' : EVM.State} {locals imms : Store} {f' : Frame}
    {sender receiver id amount : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcs : sender.toNat < EVM.addressModulus) (hcr : receiver.toNat < EVM.addressModulus)
    (h : TransferFromArgs f' sender receiver id amount)
    (hauth : ExecStmt config (calldataFrame contract locals imms evm) evm transferFromAuthStmt (.ok f' evm')) :
    ExecTransitionBody config contract evm locals transferFromTransition.body
      (balanceTransferResult f' evm' sender receiver id amount) imms := by
  have hblock := balanceTransferBlockExec f' evm' (.var "sender") sender receiver id amount
    h.contract_eq hcs hcr (fun _ _ => evalLocalValue h.sender_get)
    h.receiver_get h.id_get h.amount_get h.balance_get
  exact execFuncBody_of_terminal (nonpayableCalldataBlock hwv hhi (ExecBlock.consNormal hauth hblock))
    (balanceTransferResult_terminal _ _ _ _ _ _)

theorem transferFromBodyAuthReverts {evm : EVM.State} {locals imms : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : ExecStmt config (calldataFrame contract locals imms evm) evm transferFromAuthStmt .reverted) :
    ExecTransitionBody config contract evm locals transferFromTransition.body .reverted imms :=
  ExecFuncBody.execBlockRevert (nonpayableCalldataBlock hwv hhi (ExecBlock.consRevert hauth))

theorem transferFromBodyAuthStatic {evm : EVM.State} {locals imms : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : ExecStmt config (calldataFrame contract locals imms evm) evm transferFromAuthStmt .staticViolation) :
    ExecTransitionBody config contract evm locals transferFromTransition.body .staticViolation imms :=
  ExecFuncBody.execBlockStatic (nonpayableCalldataBlock hwv hhi (ExecBlock.consStatic hauth))

end Benchmarks.UniswapV4PoolManager

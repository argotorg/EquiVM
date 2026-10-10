import Benchmarks.UniswapV4PoolManager.Storage
import Benchmarks.UniswapV4PoolManager.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

abbrev transferEventTopic : UInt256 :=
  ⟨12321100111876247508947093339659643082128333458080942937726384708603157317721⟩

-- LIBRARY CANDIDATE: lift a terminal block result to a function-body result.
def terminalResult (result : ExecResult) : Prop :=
  match result with
  | .returned _ _ _ | .reverted | .staticViolation => True
  | _ => False

theorem execFuncBody_of_terminal {cfg : Config} {f : Frame} {evm : EVM.State}
    {stmts : List Stmt} {result : ExecResult}
    (h : ExecBlock cfg f evm stmts result) (ht : terminalResult result) :
    ExecFuncBody cfg f evm stmts result := by
  cases result with
  | returned => exact ExecFuncBody.execBlockRet h
  | reverted => exact ExecFuncBody.execBlockRevert h
  | staticViolation => exact ExecFuncBody.execBlockStatic h
  | _ => exact False.elim ht

def balanceTransferDebited (evm : EVM.State) (sender id amount : UInt256) : EVM.State :=
  balancePost evm sender id (UInt256.sub (balanceWord evm sender id) amount)

def balanceTransferPost (evm : EVM.State) (sender receiver id amount : UInt256) : EVM.State :=
  balancePost (balanceTransferDebited evm sender id amount) receiver id
    (balanceWord (balanceTransferDebited evm sender id amount) receiver id + amount)

def balanceTransferBlock (senderExpr : Expr) : List Stmt :=
  let senderRef : StorageRef := {base := "balanceOf", steps := [.mindex senderExpr, .mindex (.var "id")]}
  let receiverRef : StorageRef := {base := "balanceOf", steps := [.mindex (.var "receiver"), .mindex (.var "id")]}
  [.assign .storage senderRef (.inRange (.uint ⟨256, by decide⟩)
      (.binary .sub (.storage senderRef) (.var "amount"))),
   .assign .storage receiverRef (.inRange (.uint ⟨256, by decide⟩)
      (.binary .add (.storage receiverRef) (.var "amount"))),
   .emit "Transfer" [.env .caller, senderExpr, .var "receiver", .var "id", .var "amount"],
   .return [.boolLit true]]

def balanceTransferResult (f : Frame) (evm : EVM.State) (sender receiver id amount : UInt256) : ExecResult :=
  if amount.toNat ≤ (balanceWord evm sender id).toNat then
    if evm.executionEnv.perm = false then .staticViolation else
    if (balanceWord (balanceTransferDebited evm sender id amount) receiver id).toNat + amount.toNat < UInt256.size then
      .returned f (balanceTransferPost evm sender receiver id amount) (some [.bool true])
    else .reverted
  else .reverted

theorem balanceTransferResult_terminal (f : Frame) (evm : EVM.State) (sender receiver id amount : UInt256) :
    terminalResult (balanceTransferResult f evm sender receiver id amount) := by
  unfold balanceTransferResult
  split
  · split
    · trivial
    · split <;> trivial
  · trivial

theorem balanceTransferBlockExec (f : Frame) (evm : EVM.State) (senderExpr : Expr)
    (sender receiver id amount : UInt256) (hf : f.contract = contract)
    (hcs : sender.toNat < EVM.addressModulus) (hcr : receiver.toNat < EVM.addressModulus)
    (hs : ∀ e : EVM.State, e.executionEnv = evm.executionEnv →
      evalExpr? config f e senderExpr = .ok (.address (AccountAddress.ofNat sender.toNat)))
    (hr : f.locals.get? "receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hi : f.locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "balanceOf" = none) :
    ExecBlock config f evm (balanceTransferBlock senderExpr)
      (balanceTransferResult f evm sender receiver id amount) := by
  have hread := balanceOfRead sender id hf hcs hb (hs evm rfl) (evalLocalValue hi)
  by_cases hsub : amount.toNat ≤ (balanceWord evm sender id).toNat
  · have heval := evalExpr_uint256_sub hread (evalLocalValue ha) hsub
    have hwrite := balanceOfWrite sender id (UInt256.sub (balanceWord evm sender id) amount)
      hf hcs hb (hs evm rfl) (evalLocalValue hi)
    by_cases hperm : evm.executionEnv.perm = false
    · rw [balanceTransferResult, if_pos hsub, if_pos hperm]
      exact ExecBlock.consStatic (ExecStmt.assignStatic heval hwrite hperm)
    · have hrread := balanceOfRead (evm := balanceTransferDebited evm sender id amount) receiver id hf hcr hb
        (evalLocalValue hr) (evalLocalValue hi)
      by_cases hadd : (balanceWord (balanceTransferDebited evm sender id amount) receiver id).toNat + amount.toNat < UInt256.size
      · rw [balanceTransferResult, if_pos hsub, if_neg hperm, if_pos hadd]
        refine ExecBlock.consNormal (ExecStmt.assign heval hwrite) ?_
        refine ExecBlock.consNormal (ExecStmt.assign
          (checkedAddSourceOk hrread (evalLocalValue ha) hadd)
          (balanceOfWrite receiver id _ hf hcr hb (evalLocalValue hr) (evalLocalValue hi))) ?_
        have henv : (balanceTransferPost evm sender receiver id amount).executionEnv = evm.executionEnv :=
          (balancePost_env _ _ _ _).trans (balancePost_env _ _ _ _)
        have hsender := hs (balanceTransferPost evm sender receiver id amount) henv
        refine ExecBlock.consNormal (ExecStmt.emit
          (vals := [.address evm.executionEnv.source, .address (AccountAddress.ofNat sender.toNat),
            .address (AccountAddress.ofNat receiver.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)]) ?_) ?_
        · change evalExprs? config f (balanceTransferPost evm sender receiver id amount)
            [.env .caller, senderExpr, .var "receiver", .var "id", .var "amount"] = _
          simp only [evalExprs?, hsender, evalExpr?, hr, hi, ha, EvalResult.ofOption, bind,
            EvalResult.bind, envValue, pure, henv]
        · exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]))
      · rw [balanceTransferResult, if_pos hsub, if_neg hperm, if_neg hadd]
        refine ExecBlock.consNormal (ExecStmt.assign heval hwrite) ?_
        exact ExecBlock.consRevert (ExecStmt.assignExprRevert
          (checkedAddSourceOverflow hrread (evalLocalValue ha) (Nat.le_of_not_gt hadd)))
  · rw [balanceTransferResult, if_neg hsub]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (checkedSubSourceUnderflow hread (evalLocalValue ha) (Nat.lt_of_not_ge hsub)))

end Benchmarks.UniswapV4PoolManager

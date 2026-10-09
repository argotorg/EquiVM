import Benchmarks.Morpho.MorphoBlue.AccruePublicSource
import Benchmarks.Morpho.MorphoBlue.AccrueMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev senderAuthorizedFunction : FunctionDecl := contract.functions[6]!

def senderAuthorizedWord (σ : AccountMap) (ee : ExecutionEnv) (account : UInt256) : UInt256 :=
  if solcSourceWord ee = account then UInt256.ofNat 1 else
    UInt256.land (solcSlotWordAt (authorizationSlot account (solcSourceWord ee)) σ ee) (UInt256.ofNat 255)

def senderAuthorizedFrame (account : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store).insert "onBehalf" (.address (AccountAddress.ofNat account.toNat)) }

theorem senderAuthorized_eval_account (account : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (senderAuthorizedFrame account imms) evm (.var "onBehalf") =
      .ok (.address (AccountAddress.ofNat account.toNat)) := by
  simp only [evalExpr?, senderAuthorizedFrame, store_get_self, EvalResult.ofOption]

theorem morphoSenderAuthorizedBody (account : UInt256) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus) :
    ExecFuncBody config (senderAuthorizedFrame account imms) evm senderAuthorizedFunction.body
      (.returned (senderAuthorizedFrame account imms) evm
        (some [wordToElem .bool (senderAuthorizedWord evm.accountMap evm.executionEnv account)])) := by
  have ha := senderAuthorized_eval_account account imms evm
  have hg : evalExpr? config (senderAuthorizedFrame account imms) evm
      (.binary .eq (.env .caller) (.var "onBehalf")) =
      .ok (.bool (decide (solcSourceWord evm.executionEnv = account))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalCallerWord config _ evm, ha]
    simp only [bind, pure, EvalResult.bind, evalBinaryOp?]
    rw [canonicalAddress_beq _ _ (solcSourceWord_canonical _) hc]
  apply ExecFuncBody.execBlockRet
  by_cases heq : solcSourceWord evm.executionEnv = account
  · rw [senderAuthorizedWord, if_pos heq]
    rw [decide_eq_true heq] at hg
    apply ExecBlock.consReturn (ExecStmt.iteTrue hg ?_)
    exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, wordToElem, pure, bind, EvalResult.bind, UInt256.ofNat]; decide +kernel))
  · rw [senderAuthorizedWord, if_neg heq]
    rw [decide_eq_false heq] at hg
    apply ExecBlock.consNormal (ExecStmt.iteFalse hg ExecBlock.nil)
    apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
    exact evalMorphoIsAuthorized evm _ imms (.var "onBehalf") (.env .caller) account
      (solcSourceWord evm.executionEnv) (by simp [senderAuthorizedFrame]) ha
      (evalCallerWord config _ evm) hc (solcSourceWord_canonical _)

theorem morphoSenderAuthorizedCall (account : UInt256) (imms locals : Store) (evm : EVM.State)
    (args : List Expr) (retVar : Ident) (hc : account.toNat < EVM.addressModulus)
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok [.address (AccountAddress.ofNat account.toNat)]) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_isSenderAuthorized" args retVar)
      (.ok { contract := contract,
             locals := locals.insert retVar (wordToElem .bool (senderAuthorizedWord evm.accountMap evm.executionEnv account)),
             immutables := imms } evm) :=
  internalCallFunctionReturn (callee := senderAuthorizedFunction)
    (value := some [wordToElem .bool (senderAuthorizedWord evm.accountMap evm.executionEnv account)])
    he rfl rfl (morphoSenderAuthorizedBody account imms evm hc)

end Benchmarks.Morpho.MorphoBlue

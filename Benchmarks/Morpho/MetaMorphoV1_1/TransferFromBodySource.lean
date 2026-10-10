import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceCalls
import Benchmarks.Morpho.MetaMorphoV1_1.TransferInternalSource

/-! Public delegated transfer, preserving the allowance write before the balance reads. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def transferFromPublicFrame (evm : State) (locals imms : Store) : Frame :=
  ⟨contract, (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert "spender"
    (.address evm.executionEnv.source), imms⟩

def transferFromSpentFrame (evm : State) (locals imms : Store) : Frame :=
  { transferFromPublicFrame evm locals imms with
    locals := (transferFromPublicFrame evm locals imms).locals.insert "__c1" .unit }

def transferFromTransferTail : List Stmt :=
  [.internalCall "_transfer" [.var "from", .var "to", .var "value"] "__c2",
    .return [.boolLit true]]

def transferFromPublicTail : List Stmt :=
  [.internalCall "_spendAllowance" [.var "from", .var "spender", .var "value"] "__c1"] ++
    transferFromTransferTail

theorem transferFromPublicPrefix (evm : State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, locals, imms⟩ transferFromTransition.body
      (transferFromPublicFrame evm locals imms) transferFromPublicTail := by
  refine ⟨fun h ↦ ?_⟩
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (msgSenderCall _ imms evm "spender") h

theorem transferFromSpendArgs (evm : State) (locals imms : Store)
    (sender : AccountAddress) (value : UInt256)
    (hf : locals.get? "from" = some (.address sender))
    (hv : locals.get? "value" = some (uint256Value value)) :
    evalExprs? config (transferFromPublicFrame evm locals imms) evm
      [.var "from", .var "spender", .var "value"] =
      .ok [.address sender, .address evm.executionEnv.source, uint256Value value] := by
  simp only [Std.HashMap.get?_eq_getElem?] at hf hv
  simp [evalExprs?, evalExpr?, transferFromPublicFrame, Std.HashMap.getElem?_insert, hf, hv,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem transferFromTransferArgs (evm evm' : State) (locals imms : Store)
    (sender recipient : AccountAddress) (value : UInt256)
    (hf : locals.get? "from" = some (.address sender))
    (ht : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value)) :
    evalExprs? config (transferFromSpentFrame evm locals imms) evm'
      [.var "from", .var "to", .var "value"] =
      .ok [.address sender, .address recipient, uint256Value value] := by
  simp only [Std.HashMap.get?_eq_getElem?] at hf ht hv
  simp [evalExprs?, evalExpr?, transferFromSpentFrame, transferFromPublicFrame,
    Std.HashMap.getElem?_insert, hf, ht, hv, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem transferFromAfterSpend (evm : State) (locals imms : Store)
    (sender : AccountAddress) (value : UInt256) {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hf : locals.get? "from" = some (.address sender))
    (hv : locals.get? "value" = some (uint256Value value))
    (hs : spendAllowanceAllowed evm sender evm.executionEnv.source value)
    (htail : ExecBlock config (transferFromSpentFrame evm locals imms)
      (spendAllowanceState evm sender evm.executionEnv.source value)
      transferFromTransferTail result) :
    ExecBlock config ⟨contract, locals, imms⟩ evm transferFromTransition.body result := by
  apply (transferFromPublicPrefix evm locals imms hwv hhi).run
  exact ExecBlock.consNormal (spendAllowanceCall
    (transferFromSpendArgs evm locals imms sender value hf hv) hs) htail

theorem transferFromBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (sender recipient : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hf : locals.get? "from" = some (.address sender))
    (ht : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value))
    (hs : spendAllowanceAllowed evm sender evm.executionEnv.source value)
    (hg : transferAllowed (spendAllowanceState evm sender evm.executionEnv.source value)
      sender recipient value) :
    ExecTransitionBody config contract evm locals transferFromTransition.body
      (.returned { transferFromSpentFrame evm locals (immStore v) with
        locals := (transferFromSpentFrame evm locals (immStore v)).locals.insert "__c2" .unit }
        (balanceMoveState (spendAllowanceState evm sender evm.executionEnv.source value)
          sender recipient value) [Value.bool true]) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply transferFromAfterSpend evm locals (immStore v) sender value hwv hhi hf hv hs
  apply ExecBlock.consNormal (transferCall
    (transferFromTransferArgs evm _ locals (immStore v) sender recipient value hf ht hv) hg)
  exact ExecBlock.consReturn (ExecStmt.return
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]))

theorem transferFromSpendReverts (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (sender : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hf : locals.get? "from" = some (.address sender))
    (hv : locals.get? "value" = some (uint256Value value))
    (hs : ¬ spendAllowanceAllowed evm sender evm.executionEnv.source value) :
    ExecTransitionBody config contract evm locals transferFromTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (transferFromPublicPrefix evm locals (immStore v) hwv hhi).run
  exact ExecBlock.consRevert (spendAllowanceCallReverts
    (transferFromSpendArgs evm locals (immStore v) sender value hf hv) hs)

theorem transferFromSpendStatic (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (sender : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hf : locals.get? "from" = some (.address sender))
    (hv : locals.get? "value" = some (uint256Value value))
    (hs : spendAllowanceAllowed evm sender evm.executionEnv.source value)
    (hfinite : allowanceWord evm sender evm.executionEnv.source ≠ unlimitedAllowance)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals transferFromTransition.body .staticViolation
      (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (transferFromPublicPrefix evm locals (immStore v) hwv hhi).run
  exact ExecBlock.consStatic (spendAllowanceCallStatic
    (transferFromSpendArgs evm locals (immStore v) sender value hf hv) hfinite hs hperm)

theorem transferFromTransferReverts (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (sender recipient : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hf : locals.get? "from" = some (.address sender))
    (ht : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value))
    (hs : spendAllowanceAllowed evm sender evm.executionEnv.source value)
    (hg : ¬ transferAllowed (spendAllowanceState evm sender evm.executionEnv.source value)
      sender recipient value) :
    ExecTransitionBody config contract evm locals transferFromTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply transferFromAfterSpend evm locals (immStore v) sender value hwv hhi hf hv hs
  exact ExecBlock.consRevert (transferCallReverts
    (transferFromTransferArgs evm _ locals (immStore v) sender recipient value hf ht hv) hg)

theorem transferFromTransferStatic (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (sender recipient : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hf : locals.get? "from" = some (.address sender))
    (ht : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value))
    (hs : spendAllowanceAllowed evm sender evm.executionEnv.source value)
    (hg : transferAllowed (spendAllowanceState evm sender evm.executionEnv.source value)
      sender recipient value) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals transferFromTransition.body .staticViolation
      (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply transferFromAfterSpend evm locals (immStore v) sender value hwv hhi hf hv hs
  exact ExecBlock.consStatic (transferCallStatic
    (transferFromTransferArgs evm _ locals (immStore v) sender recipient value hf ht hv) hg
    (by rw [spendAllowanceState_executionEnv]; exact hperm))

end Benchmarks.Morpho.MetaMorphoV1_1

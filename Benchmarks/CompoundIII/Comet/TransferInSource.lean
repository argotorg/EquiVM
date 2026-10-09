import Benchmarks.CompoundIII.Comet.TransferInModel
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem transferInReturn_eval (imms : Store) (asset sender : AccountAddress)
    (amount pre post : UInt256) (out : ByteArray) (evm : EVM.State) :
    evalExpr? config (transferInFinalFrame imms asset sender amount pre post out) evm
      transferInReturnExpr =
      if pre.toNat ≤ post.toNat then .ok (.int (Int.ofNat (UInt256.sub post pre).toNat))
      else .revert := by
  have hp : evalExpr? config (transferInFinalFrame imms asset sender amount pre post out)
      evm (.var "postTransferBalance") = .ok (.int (Int.ofNat post.toNat)) := by
    simp [evalExpr?, transferInFinalFrame, EvalResult.ofOption]
  have hb : evalExpr? config (transferInFinalFrame imms asset sender amount pre post out)
      evm (.var "preTransferBalance") = .ok (.int (Int.ofNat pre.toNat)) := by
    simp only [evalExpr?, transferInFinalFrame, transferCallFrame, transferInBeforeFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  by_cases hle : pre.toNat ≤ post.toNat
  · rw [if_pos hle]
    exact evalExpr_uint256_sub hp hb hle
  · rw [if_neg hle]
    exact checkedNarrowSubSourceUnderflow ⟨256, by decide⟩ hp hb (Nat.lt_of_not_ge hle)

theorem transferInAfter_source {asset sender : AccountAddress} {amount pre : UInt256}
    {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : TransferInAfter asset sender amount pre evm result) (imms : Store) :
    QuoteSourceResult (transferInBeforeFrame imms asset sender amount pre) evm
      transferInAfterBlock result := by
  have ha : evalExpr? config (transferInBeforeFrame imms asset sender amount pre) evm
      (.var "asset") = .ok (.address asset) := by
    simp only [evalExpr?, transferInBeforeFrame, transferInEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hd : evalExpr? config (transferInBeforeFrame imms asset sender amount pre) evm
      transferInPayloadExpr =
      .ok (.bytes (transferFromPayload sender evm.executionEnv.codeOwner amount)) := by
    simp only [transferInPayloadExpr, evalExpr?, evalExprList?, transferInBeforeFrame,
      transferInEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption, envValue, pure, bind, EvalResult.bind]
    change (EvalResult.ofOption .typeError (config.externalABI.encode? "transferFrom"
      [.address sender, .address evm.executionEnv.codeOwner,
        .int (Int.ofNat amount.toNat)])).bind
          (fun bytes ↦ EvalResult.ok (Value.bytes bytes)) = _
    rw [transferFromPayload_encode]
    rfl
  have hasset (evm' : EVM.State) (out : ByteArray) : evalExpr? config
      (transferCallFrame (transferInBeforeFrame imms asset sender amount pre) out)
      evm' (.var "asset") = .ok (.address asset) := by
    simp only [evalExpr?, transferCallFrame, transferInBeforeFrame, transferInEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  cases ht with
  | transferFailed ht =>
    exact execBlockAppendReverted (transferCall_source ht
      (transferInBeforeFrame imms asset sender amount pre) (.var "asset")
      transferInPayloadExpr rfl ha hd)
  | @balanceFailed evm' out ht hb =>
    have hc := transferCall_source ht (transferInBeforeFrame imms asset sender amount pre)
      (.var "asset") transferInPayloadExpr rfl ha hd
    have hbalance := tokenBalanceTrace_source hb _ (.var "asset") "postTransferBalance"
      (hasset evm' out)
    exact execBlockAppendOk hc (ExecBlock.consRevert hbalance)
  | @balanceResult evm' evm'' out post ht hb =>
    have hc := transferCall_source ht (transferInBeforeFrame imms asset sender amount pre)
      (.var "asset") transferInPayloadExpr rfl ha hd
    have hbalance := tokenBalanceTrace_source hb _ (.var "asset") "postTransferBalance"
      (hasset evm' out)
    have he := transferInReturn_eval imms asset sender amount pre post out evm''
    by_cases hle : pre.toNat ≤ post.toNat
    · rw [if_pos hle] at he ⊢
      exact ⟨_, execBlockAppendOk hc (ExecBlock.consNormal hbalance (ABlock.start.returns he))⟩
    · rw [if_neg hle] at he ⊢
      apply execBlockAppendOk hc
      apply ExecBlock.consNormal hbalance
      apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
      change evalExprs? config (transferInFinalFrame imms asset sender amount pre post out)
        evm'' [transferInReturnExpr] = .revert
      simp only [evalExprs?, he, bind, EvalResult.bind]

theorem transferIn_source {asset sender : AccountAddress} {amount : UInt256}
    {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : TransferInTrace asset sender amount evm result) (imms : Store) :
    QuoteSourceResult (transferInEntry imms asset sender amount) evm
      transferInCallable.body result := by
  have ha : evalExpr? config (transferInEntry imms asset sender amount) evm
      (.var "asset") = .ok (.address asset) := by
    simp [evalExpr?, transferInEntry, EvalResult.ofOption]
  cases ht with
  | balanceFailed hb =>
    exact ExecBlock.consRevert (tokenBalanceTrace_source hb _ _ "preTransferBalance" ha)
  | @balanceOk evm' pre result hb ht =>
    have hbalance := tokenBalanceTrace_source hb _ _ "preTransferBalance" ha
    have hafter := transferInAfter_source ht imms
    cases result with
    | none => exact ExecBlock.consNormal hbalance hafter
    | some r =>
      obtain ⟨evm'', value⟩ := r
      obtain ⟨final, hafter⟩ := hafter
      exact ⟨final, ExecBlock.consNormal hbalance hafter⟩

theorem transferIn_call {asset sender : AccountAddress} {amount : UInt256}
    {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : TransferInTrace asset sender amount evm result) (frame : Frame)
    (assetExpr fromExpr amountExpr : Expr) (ret : Ident) (hf : frame.contract = contract)
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (hs : evalExpr? config frame evm fromExpr = .ok (.address sender))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int (Int.ofNat amount.toNat))) :
    ExecStmt config frame evm (.internalCall "doTransferIn" [assetExpr, fromExpr, amountExpr] ret)
      (wordCallResult frame ret result) := by
  have he : evalExprs? config frame evm [assetExpr, fromExpr, amountExpr] =
      .ok [.address asset, .address sender, .int (Int.ofNat amount.toNat)] := by
    simp only [evalExprs?, ha, hs, ham, pure, bind, EvalResult.bind]
  have hb := transferIn_source ht frame.immutables
  cases result with
  | none =>
    exact ExecStmt.internalCallRevert (callee := transferInCallable)
      (locals := (transferInEntry frame.immutables asset sender amount).locals) he
      (by rw [hf]; exact transferInCallable_lookup) rfl
      (by simpa only [hf] using ExecFuncBody.execBlockRevert hb)
  | some r =>
    obtain ⟨evm', value⟩ := r
    obtain ⟨final, hb⟩ := hb
    exact ExecStmt.internalCallReturn (callee := transferInCallable)
      (locals := (transferInEntry frame.immutables asset sender amount).locals) he
      (by rw [hf]; exact transferInCallable_lookup) rfl
      (by simpa only [hf] using ExecFuncBody.execBlockRet hb)

end Benchmarks.CompoundIII.Comet

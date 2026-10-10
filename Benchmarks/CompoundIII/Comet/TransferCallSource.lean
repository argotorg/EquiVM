import Benchmarks.CompoundIII.Comet.TransferReturnSource
import Benchmarks.CompoundIII.Comet.TransferPayload

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferCallBlock (assetExpr payloadExpr : Expr) : List Stmt :=
  [.require (.binary .gt (.extCodeSize assetExpr) (.intLit 0)),
    .lowLevelCall assetExpr (.intLit 0) payloadExpr "ok" "data",
    .require (.var "ok"), .internalCall "checkTransferReturn" [.var "data"] "checked"]

def transferCallFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := ((frame.locals.insert "ok" (.bool true)).insert "data"
    (.bytes out)).insert "checked" .unit }

inductive TransferCallTrace (asset : AccountAddress) (payload : ByteArray) (evm : EVM.State) :
    Option (EVM.State × ByteArray) → Prop where
  | codeMissing (hc : extCodeSizeWord evm.accountMap (EVM.word asset.val) = ⟨0⟩) :
      TransferCallTrace asset payload evm none
  | callResult {evm' : EVM.State} {z : Bool} {out : ByteArray}
      (hne : extCodeSizeWord evm.accountMap (EVM.word asset.val) ≠ ⟨0⟩)
      (hc : callViaEVM evm asset 0 payload (z, evm', out)) (hh : out.size < 2^255) :
      TransferCallTrace asset payload evm
        (if z = true ∧ TransferReturnValid out then some (evm', out) else none)

def transferCallResult (frame : Frame) (result : Option (EVM.State × ByteArray)) : ExecResult :=
  match result with
  | none => .reverted
  | some (evm', out) => .ok (transferCallFrame frame out) evm'

theorem transferCall_source {asset : AccountAddress} {payload : ByteArray}
    {evm : EVM.State} {result : Option (EVM.State × ByteArray)}
    (ht : TransferCallTrace asset payload evm result) (frame : Frame)
    (assetExpr payloadExpr : Expr) (hf : frame.contract = contract)
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (hd : evalExpr? config frame evm payloadExpr = .ok (.bytes payload)) :
    ExecBlock config frame evm (transferCallBlock assetExpr payloadExpr)
      (transferCallResult frame result) := by
  have haddr : AccountAddress.ofUInt256 (EVM.word asset.val) = asset :=
    accountAddress_roundtrip asset
  have hx := extCodeSource (target := EVM.word asset.val) (σ := evm.accountMap) rfl
    (by rw [haddr]; exact ha)
  cases ht with
  | codeMissing hc =>
    apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    rw [evalExpr?, hx, hc] <;> try (intro h; cases h)
    simp [evalExpr?, evalBinaryOp?, bind, EvalResult.bind, pure]
  | @callResult evm' z out hne hc hh =>
    have hguard : evalExpr? config frame evm
        (.binary .gt (.extCodeSize assetExpr) (.intLit 0)) = .ok (.bool true) := by
      rw [evalExpr?, hx] <;> try (intro h; cases h)
      simp only [bind, EvalResult.bind, evalExpr?, evalBinaryOp?, pure, EvalResult.ok.injEq,
        Value.bool.injEq, decide_eq_true_eq]
      have hn := intOfNat_toNat_ne_zero_of_u256_ne_zero _ hne
      simp only [Int.ofNat_eq_natCast] at hn ⊢
      omega
    have hcall := lowLevelCallSource (eth := .intLit 0) (frame := frame) ha
      (by simp only [evalExpr?, pure]) (success := "ok") (data := "data") hd hc
    let callFrame : Frame := { frame with locals :=
      (frame.locals.insert "ok" (.bool true)).insert "data" (.bytes out) }
    have hcheck := transferReturn_call callFrame evm' (.var "data") "checked" out hf
      (by simp [evalExpr?, callFrame, EvalResult.ofOption]) hh
    cases z with
    | false =>
      simp only [Bool.false_eq_true, false_and, if_false, transferCallResult]
      apply ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      apply ExecBlock.consNormal hcall
      apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    | true =>
      by_cases hv : TransferReturnValid out
      · simp only [hv, and_self, if_true, transferCallResult]
        rw [if_pos hv] at hcheck
        apply ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        apply ExecBlock.consNormal hcall
        apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
        · exact ExecBlock.consNormal hcheck ExecBlock.nil
        · simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            EvalResult.ofOption]
          rfl
      · simp only [hv, and_false, if_false, transferCallResult]
        rw [if_neg hv] at hcheck
        apply ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        apply ExecBlock.consNormal hcall
        apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
        · exact ExecBlock.consRevert hcheck
        · simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            EvalResult.ofOption]
          rfl

end Benchmarks.CompoundIII.Comet

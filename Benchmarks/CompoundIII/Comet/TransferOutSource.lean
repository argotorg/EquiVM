import Benchmarks.CompoundIII.Comet.TransferPayload
import Benchmarks.CompoundIII.Comet.TransferCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferOutCallable : CallableDecl :=
  { params := [⟨"asset", abiAddress⟩, ⟨"to", abiAddress⟩, ⟨"amount", abiUInt256⟩],
    returnType := [], body :=
    [.require (.binary .gt (.extCodeSize (.var "asset")) (.intLit 0)),
      .lowLevelCall (.var "asset") (.intLit 0)
        (.abiEncodeCall "transfer" [.var "to", .var "amount"]) "ok" "data",
      .require (.var "ok"), .internalCall "checkTransferReturn" [.var "data"] "checked"] }

theorem transferOutCallable_lookup :
    lookupCallable? contract "doTransferOut" = some transferOutCallable := rfl

def transferOutEntry (imms : Store) (asset recipient : AccountAddress) (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms, locals :=
    ((((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert "to"
      (.address recipient)).insert "asset" (.address asset)) }

def transferOutCallFrame (imms : Store) (asset recipient : AccountAddress) (amount : UInt256)
    (z : Bool) (out : ByteArray) : Frame :=
  let f := transferOutEntry imms asset recipient amount
  { f with locals := (f.locals.insert "ok" (.bool z)).insert "data" (.bytes out) }

inductive TransferOutTrace (asset recipient : AccountAddress) (amount : UInt256)
    (evm : EVM.State) : Option EVM.State → Prop where
  | codeMissing (hc : extCodeSizeWord evm.accountMap (EVM.word asset.val) = ⟨0⟩) :
      TransferOutTrace asset recipient amount evm none
  | callResult {evm' : EVM.State} {z : Bool} {out : ByteArray}
      (hne : extCodeSizeWord evm.accountMap (EVM.word asset.val) ≠ ⟨0⟩)
      (hc : callViaEVM evm asset 0 (transferPayload recipient amount) (z, evm', out))
      (hh : out.size < 2^255) : TransferOutTrace asset recipient amount evm
        (if z = true ∧ TransferReturnValid out then some evm' else none)

def TransferOutSourceResult (frame : Frame) (evm : EVM.State) (result : Option EVM.State) : Prop :=
  match result with
  | none => ExecFuncBody config frame evm transferOutCallable.body .reverted
  | some evm' => ∃ final, ExecFuncBody config frame evm transferOutCallable.body
      (.returned final evm' none)

theorem transferOut_source {asset recipient : AccountAddress} {amount : UInt256}
    {evm : EVM.State} {result : Option EVM.State}
    (ht : TransferOutTrace asset recipient amount evm result) (imms : Store) :
    TransferOutSourceResult (transferOutEntry imms asset recipient amount) evm result := by
  have he : evalExpr? config (transferOutEntry imms asset recipient amount) evm
      (.var "asset") = .ok (.address asset) := by
    simp only [evalExpr?, transferOutEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hd : evalExpr? config (transferOutEntry imms asset recipient amount) evm
      (.abiEncodeCall "transfer" [.var "to", .var "amount"]) =
      .ok (.bytes (transferPayload recipient amount)) := by
    simp only [evalExpr?, evalExprList?, transferOutEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, pure, bind, EvalResult.bind]
    change (EvalResult.ofOption .typeError (config.externalABI.encode? "transfer"
      [.address recipient, .int (Int.ofNat amount.toNat)])).bind
        (fun bytes ↦ EvalResult.ok (Value.bytes bytes)) = _
    rw [transferPayload_encode]
    rfl
  cases ht with
  | codeMissing hc =>
    exact ExecFuncBody.execBlockRevert (transferCall_source (.codeMissing hc)
      (transferOutEntry imms asset recipient amount) (.var "asset")
      (.abiEncodeCall "transfer" [.var "to", .var "amount"]) rfl he hd)
  | @callResult evm' z out hne hc hh =>
    have hb := transferCall_source (.callResult hne hc hh)
      (transferOutEntry imms asset recipient amount) (.var "asset")
      (.abiEncodeCall "transfer" [.var "to", .var "amount"]) rfl he hd
    by_cases hv : z = true ∧ TransferReturnValid out
    · rw [if_pos hv] at hb ⊢
      exact ⟨_, ExecFuncBody.execBlockOK hb⟩
    · rw [if_neg hv] at hb ⊢
      exact ExecFuncBody.execBlockRevert hb

theorem transferOut_call {asset recipient : AccountAddress} {amount : UInt256}
    {evm : EVM.State} {result : Option EVM.State}
    (ht : TransferOutTrace asset recipient amount evm result) (frame : Frame)
    (assetExpr toExpr amountExpr : Expr) (ret : Ident) (hf : frame.contract = contract)
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (ht' : evalExpr? config frame evm toExpr = .ok (.address recipient))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int (Int.ofNat amount.toNat))) :
    ExecStmt config frame evm (.internalCall "doTransferOut" [assetExpr, toExpr, amountExpr] ret)
      (match result with
        | none => .reverted
        | some evm' => .ok { frame with locals := frame.locals.insert ret .unit } evm') := by
  have hb := transferOut_source ht frame.immutables
  cases result with
  | none =>
    exact ExecStmt.internalCallRevert (callee := transferOutCallable)
      (locals := (transferOutEntry frame.immutables asset recipient amount).locals)
      (argVals := [.address asset, .address recipient, .int (Int.ofNat amount.toNat)])
      (by simp only [evalExprs?, ha, ht', ham, pure, bind, EvalResult.bind])
      (by rw [hf]; exact transferOutCallable_lookup) rfl (by simpa only [hf] using hb)
  | some evm' =>
    obtain ⟨final, hb⟩ := hb
    exact ExecStmt.internalCallReturn (callee := transferOutCallable) (value := none)
      (locals := (transferOutEntry frame.immutables asset recipient amount).locals)
      (argVals := [.address asset, .address recipient, .int (Int.ofNat amount.toNat)])
      (by simp only [evalExprs?, ha, ht', ham, pure, bind, EvalResult.bind])
      (by rw [hf]; exact transferOutCallable_lookup) rfl (by simpa only [hf] using hb)

end Benchmarks.CompoundIII.Comet

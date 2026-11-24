import Benchmarks.CompoundIII.Comet.TokenBalanceTrace
import Benchmarks.CompoundIII.Comet.TransferCallSource
import Benchmarks.CompoundIII.Comet.TransferFromPayload
import Benchmarks.CompoundIII.Comet.QuoteTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

inductive TransferInAfter (fork : Ethereum.Fork) (asset sender : AccountAddress) (amount pre : UInt256)
    (evm : EVM.State) : Option (EVM.State × UInt256) → Prop where
  | transferFailed (ht : TransferCallTrace fork asset
      (transferFromPayload sender evm.executionEnv.codeOwner amount) evm none) :
      TransferInAfter fork asset sender amount pre evm none
  | balanceFailed {evm' : EVM.State} {out : ByteArray}
      (ht : TransferCallTrace fork asset (transferFromPayload sender evm.executionEnv.codeOwner amount)
        evm (some (evm', out))) (hb : TokenBalanceTrace fork asset evm' none) :
      TransferInAfter fork asset sender amount pre evm none
  | balanceResult {evm' evm'' : EVM.State} {out : ByteArray} {post : UInt256}
      (ht : TransferCallTrace fork asset (transferFromPayload sender evm.executionEnv.codeOwner amount)
        evm (some (evm', out))) (hb : TokenBalanceTrace fork asset evm' (some (evm'', post))) :
      TransferInAfter fork asset sender amount pre evm
        (if pre.toNat ≤ post.toNat then some (evm'', UInt256.sub post pre) else none)

inductive TransferInTrace (fork : Ethereum.Fork) (asset sender : AccountAddress) (amount : UInt256)
    (evm : EVM.State) : Option (EVM.State × UInt256) → Prop where
  | balanceFailed (hb : TokenBalanceTrace fork asset evm none) :
      TransferInTrace fork asset sender amount evm none
  | balanceOk {evm' : EVM.State} {pre : UInt256} {result}
      (hb : TokenBalanceTrace fork asset evm (some (evm', pre)))
      (ht : TransferInAfter fork asset sender amount pre evm' result) :
      TransferInTrace fork asset sender amount evm result

def transferInPayloadExpr : Expr :=
  .abiEncodeCall "transferFrom" [.var "from", .env .this, .var "amount"]

def transferInReturnExpr : Expr := .inRange (.uint ⟨256, by decide⟩)
  (.binary .sub (.var "postTransferBalance") (.var "preTransferBalance"))

def transferInFinishBlock : List Stmt :=
  [.externalCall (.var "asset") "balanceOf" (.intLit 0) [.env .this]
    "postTransferBalance" (perm := false), .return [transferInReturnExpr]]

def transferInAfterBlock : List Stmt :=
  transferCallBlock (.var "asset") transferInPayloadExpr ++ transferInFinishBlock

def transferInCallable : CallableDecl :=
  { params := [⟨"asset", abiAddress⟩, ⟨"from", abiAddress⟩, ⟨"amount", abiUInt256⟩],
    returnType := [abiUInt256], body :=
    .externalCall (.var "asset") "balanceOf" (.intLit 0) [.env .this]
      "preTransferBalance" (perm := false) :: transferInAfterBlock }

theorem transferInCallable_lookup :
    lookupCallable? contract "doTransferIn" = some transferInCallable := rfl

def transferInEntry (imms : Store) (asset sender : AccountAddress) (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms, locals :=
    ((((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert "from"
      (.address sender)).insert "asset" (.address asset)) }

def transferInBeforeFrame (imms : Store) (asset sender : AccountAddress)
    (amount pre : UInt256) : Frame :=
  let f := transferInEntry imms asset sender amount
  { f with locals := f.locals.insert "preTransferBalance" (.int (Int.ofNat pre.toNat)) }

def transferInFinalFrame (imms : Store) (asset sender : AccountAddress)
    (amount pre post : UInt256) (out : ByteArray) : Frame :=
  let f := transferCallFrame (transferInBeforeFrame imms asset sender amount pre) out
  { f with locals := f.locals.insert "postTransferBalance" (.int (Int.ofNat post.toNat)) }

end Benchmarks.CompoundIII.Comet

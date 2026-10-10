import Benchmarks.CompoundIII.Comet.TransferBaseRead
import Benchmarks.CompoundIII.Comet.TransferBaseMathFrames
import Benchmarks.CompoundIII.Comet.TransferBaseTotalsModel
import Benchmarks.CompoundIII.Comet.TransferBaseUpdateModel
import Benchmarks.CompoundIII.Comet.TransferBaseTailModel
import Benchmarks.CompoundIII.Comet.WithdrawBaseModel
import Benchmarks.CompoundIII.Comet.SupplyBaseModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def transferBaseTotals (evm : EVM.State) (src dst : AccountAddress) (amount : UInt256) :
    InternalOutcome :=
  transferBaseTotalsOutcome evm (supplyBaseSupplied evm dst amount)
    (withdrawBaseSupplied evm src amount) (withdrawBaseBorrowed evm src amount)
    (supplyBaseRepaid evm dst amount)

def transferBaseUpdates (v : CometWithExtendedAssetListImmutables) (original evm : EVM.State)
    (src dst : AccountAddress) (amount : UInt256) : InternalOutcome :=
  transferBaseUpdateOutcome v evm src dst (withdrawBaseBasic original src)
    (withdrawBaseBasic original dst) (withdrawBaseNext original src amount)
    (supplyBaseNext original dst amount)

inductive TransferBaseAfterAccrue (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (amount : UInt256) (evm : EVM.State) : InternalOutcome → Prop where
  | mathFailed (hf : ¬ TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount) :
      TransferBaseAfterAccrue v src dst amount evm .reverted
  | totalsReverted (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount)
      (ht : transferBaseTotals evm src dst amount = .reverted) :
      TransferBaseAfterAccrue v src dst amount evm .reverted
  | totalsStatic (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount)
      (ht : transferBaseTotals evm src dst amount = .staticViolation) :
      TransferBaseAfterAccrue v src dst amount evm .staticViolation
  | updateReverted {evm'} (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount)
      (ht : transferBaseTotals evm src dst amount = .ok evm')
      (hu : transferBaseUpdates v evm evm' src dst amount = .reverted) :
      TransferBaseAfterAccrue v src dst amount evm .reverted
  | updateStatic {evm'} (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount)
      (ht : transferBaseTotals evm src dst amount = .ok evm')
      (hu : transferBaseUpdates v evm evm' src dst amount = .staticViolation) :
      TransferBaseAfterAccrue v src dst amount evm .staticViolation
  | done {evm' evm'' result} (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount)
      (ht : transferBaseTotals evm src dst amount = .ok evm')
      (hu : transferBaseUpdates v evm evm' src dst amount = .ok evm'')
      (tail : TransferBaseTailTrace v src
        (withdrawBaseBalance evm (withdrawBaseBasic evm src).principal amount) evm'' result) :
      TransferBaseAfterAccrue v src dst amount evm result

inductive TransferBaseTrace (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (amount : UInt256) (evm : EVM.State) : InternalOutcome → Prop where
  | reverted (ha : accrueOutcome v evm = .reverted) : TransferBaseTrace v src dst amount evm .reverted
  | staticViolation (ha : accrueOutcome v evm = .staticViolation) :
      TransferBaseTrace v src dst amount evm .staticViolation
  | done {evm' result} (ha : accrueOutcome v evm = .ok evm')
      (tail : TransferBaseAfterAccrue v src dst amount evm' result) :
      TransferBaseTrace v src dst amount evm result

def transferBaseReadBlock : List Stmt :=
  [.letDecl "srcUser" (some (.tuple
      [.elem (.int (.sint ⟨104, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨16, by decide⟩)),
        .elem (.int (.uint ⟨8, by decide⟩))]))
      (.storage ⟨"userBasic", [.mindex (.var "src")]⟩),
    .letDecl "dstUser" (some (.tuple
      [.elem (.int (.sint ⟨104, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨16, by decide⟩)),
        .elem (.int (.uint ⟨8, by decide⟩))]))
      (.storage ⟨"userBasic", [.mindex (.var "dst")]⟩),
    .letDecl "srcPrincipal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
      (.field (.var "srcUser") "principal"),
    .letDecl "dstPrincipal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
      (.field (.var "dstUser") "principal")]

def transferBaseAfterAccrueBlock : List Stmt :=
  transferBaseReadBlock ++ transferBaseMathBlock ++ transferBaseTotalsBlock ++
    transferBaseUpdateBlock ++ transferBaseTail

def transferBaseCallable : CallableDecl :=
  { params := [⟨"src", .elem .address⟩, ⟨"dst", .elem .address⟩,
      ⟨"amount", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := []
    body := .internalCall "accrueInternal" [] "__c0" :: transferBaseAfterAccrueBlock }

theorem transferBaseCallable_lookup :
    lookupCallable? contract "transferBase" = some transferBaseCallable := rfl

def transferBaseEntry (imms : Store) (src dst : AccountAddress) (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (((∅ : Store).insert "amount" (.int amount.toNat)).insert "dst"
      (.address dst)).insert "src" (.address src) }

def transferBaseAccruedFrame (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (amount : UInt256) : Frame :=
  let frame := transferBaseEntry (immStore v) src dst amount
  { frame with locals := frame.locals.insert "__c0" .unit }

def transferBaseReadFrame (frame : Frame) (evm : EVM.State) (src dst : AccountAddress) : Frame :=
  { frame with
    locals := (((frame.locals.insert "srcUser" (userBasicValue (withdrawBaseBasic evm src))).insert
      "dstUser" (userBasicValue (withdrawBaseBasic evm dst))).insert "srcPrincipal"
      (.int (signed104 (withdrawBaseBasic evm src).principal))).insert "dstPrincipal"
      (.int (signed104 (withdrawBaseBasic evm dst).principal)) }

def transferBaseReadyFrame (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (amount : UInt256) (evm : EVM.State) : Frame :=
  transferBaseMathFrame
    (transferBaseReadFrame (transferBaseAccruedFrame v src dst amount) evm src dst) evm
    (withdrawBaseBasic evm src).principal (withdrawBaseBasic evm dst).principal amount

end Benchmarks.CompoundIII.Comet

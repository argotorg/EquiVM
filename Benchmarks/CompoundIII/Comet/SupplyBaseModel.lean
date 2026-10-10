import Benchmarks.CompoundIII.Comet.SupplyBaseRead
import Benchmarks.CompoundIII.Comet.SupplyBaseMathModel
import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsModel
import Benchmarks.CompoundIII.Comet.SupplyBaseEventsSource
import Benchmarks.CompoundIII.Comet.TransferInModel
import Benchmarks.CompoundIII.Comet.UpdateBaseModel
import Benchmarks.CompoundIII.Comet.AccrueInternalModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def supplyBaseNext (evm : EVM.State) (dst : AccountAddress) (amount : UInt256) : UInt256 :=
  supplyBasePrincipal evm (withdrawBaseBasic evm dst).principal amount

def supplyBaseSupplied (evm : EVM.State) (dst : AccountAddress) (amount : UInt256) : UInt256 :=
  supplyAmount (withdrawBaseBasic evm dst).principal (supplyBaseNext evm dst amount)

def supplyBaseRepaid (evm : EVM.State) (dst : AccountAddress) (amount : UInt256) : UInt256 :=
  repayAmount (withdrawBaseBasic evm dst).principal (supplyBaseNext evm dst amount)

inductive SupplyBaseAfterAccrue (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | mathFailed (hf : ¬ SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount) :
      SupplyBaseAfterAccrue v sender dst amount evm .reverted
  | totalsReverted (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount)
      (ht : supplyBaseTotalsOutcome evm (supplyBaseSupplied evm dst amount)
        (supplyBaseRepaid evm dst amount) = .reverted) :
      SupplyBaseAfterAccrue v sender dst amount evm .reverted
  | totalsStatic (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount)
      (ht : supplyBaseTotalsOutcome evm (supplyBaseSupplied evm dst amount)
        (supplyBaseRepaid evm dst amount) = .staticViolation) :
      SupplyBaseAfterAccrue v sender dst amount evm .staticViolation
  | updateReverted {evm'}
      (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount)
      (ht : supplyBaseTotalsOutcome evm (supplyBaseSupplied evm dst amount)
        (supplyBaseRepaid evm dst amount) = .ok evm')
      (hu : updateBaseOutcome v evm' dst (withdrawBaseBasic evm dst)
        (supplyBaseNext evm dst amount) = .reverted) :
      SupplyBaseAfterAccrue v sender dst amount evm .reverted
  | updateStatic {evm'}
      (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount)
      (ht : supplyBaseTotalsOutcome evm (supplyBaseSupplied evm dst amount)
        (supplyBaseRepaid evm dst amount) = .ok evm')
      (hu : updateBaseOutcome v evm' dst (withdrawBaseBasic evm dst)
        (supplyBaseNext evm dst amount) = .staticViolation) :
      SupplyBaseAfterAccrue v sender dst amount evm .staticViolation
  | done {evm' evm''}
      (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount)
      (ht : supplyBaseTotalsOutcome evm (supplyBaseSupplied evm dst amount)
        (supplyBaseRepaid evm dst amount) = .ok evm')
      (hu : updateBaseOutcome v evm' dst (withdrawBaseBasic evm dst)
        (supplyBaseNext evm dst amount) = .ok evm'') :
      SupplyBaseAfterAccrue v sender dst amount evm (.ok evm'')

inductive SupplyBaseAfterTransfer (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (ha : accrueOutcome v evm = .reverted) :
      SupplyBaseAfterTransfer v sender dst amount evm .reverted
  | staticViolation (ha : accrueOutcome v evm = .staticViolation) :
      SupplyBaseAfterTransfer v sender dst amount evm .staticViolation
  | done {evm' result} (ha : accrueOutcome v evm = .ok evm')
      (tail : SupplyBaseAfterAccrue v sender dst amount evm' result) :
      SupplyBaseAfterTransfer v sender dst amount evm result

inductive SupplyBaseTrace (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | transferFailed (ht : TransferInTrace v.baseToken sender amount evm none) :
      SupplyBaseTrace v sender dst amount evm .reverted
  | transferOk {evm' received result}
      (ht : TransferInTrace v.baseToken sender amount evm (some (evm', received)))
      (tail : SupplyBaseAfterTransfer v sender dst received evm' result) :
      SupplyBaseTrace v sender dst amount evm result

def supplyBaseReadBlock : List Stmt :=
  [.letDecl "dstUser" (some (.tuple
      [.elem (.int (.sint ⟨104, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨16, by decide⟩)),
        .elem (.int (.uint ⟨8, by decide⟩))]))
      (.storage ⟨"userBasic", [.mindex (.var "dst")]⟩),
    .letDecl "dstPrincipal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
      (.field (.var "dstUser") "principal")]

def supplyBaseUpdateStmt : Stmt :=
  .internalCall "updateBasePrincipal" [.var "dst", .var "dstUser", .var "dstPrincipalNew"] "__c6"

def supplyBaseCallable : CallableDecl :=
  { params := [⟨"from", .elem .address⟩, ⟨"dst", .elem .address⟩,
      ⟨"amount", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := []
    body := [.internalCall "doTransferIn" [.immutable "baseToken", .var "from", .var "amount"]
      "__c0", .assign .localVar ⟨"amount", []⟩ (.var "__c0"),
      .internalCall "accrueInternal" [] "__c1"] ++ supplyBaseReadBlock ++
      supplyBaseMathBlock ++ supplyBaseTotalsBlock ++ [supplyBaseUpdateStmt] ++ supplyBaseEvents }

theorem supplyBaseCallable_lookup :
    lookupCallable? contract "supplyBase" = some supplyBaseCallable := rfl

def supplyBaseEntry (imms : Store) (sender dst : AccountAddress) (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (((∅ : Store).insert "amount" (.int amount.toNat)).insert "dst"
      (.address dst)).insert "from" (.address sender) }

def supplyBaseReadFrame (frame : Frame) (evm : EVM.State) (dst : AccountAddress) : Frame :=
  { frame with
    locals := (frame.locals.insert "dstUser" (userBasicValue (withdrawBaseBasic evm dst))).insert
      "dstPrincipal" (.int (signed104 (withdrawBaseBasic evm dst).principal)) }

def supplyBaseReceivedFrame (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (requested amount : UInt256) : Frame :=
  let frame := supplyBaseEntry (immStore v) sender dst requested
  { frame with
    locals := (frame.locals.insert "__c0" (.int amount.toNat)).insert "amount" (.int amount.toNat) }

def supplyBaseAccruedFrame (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (requested amount : UInt256) : Frame :=
  let frame := supplyBaseReceivedFrame v sender dst requested amount
  { frame with locals := frame.locals.insert "__c1" .unit }

def supplyBaseReadyFrame (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (requested amount : UInt256) (evm : EVM.State) : Frame :=
  supplyBaseMathFrame
    (supplyBaseReadFrame (supplyBaseAccruedFrame v sender dst requested amount) evm dst)
    evm (withdrawBaseBasic evm dst).principal amount

def supplyBaseAfterAccrueBlock : List Stmt :=
  supplyBaseReadBlock ++ supplyBaseMathBlock ++ supplyBaseTotalsBlock ++
    [supplyBaseUpdateStmt] ++ supplyBaseEvents

end Benchmarks.CompoundIII.Comet

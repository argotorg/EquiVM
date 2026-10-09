import Benchmarks.CompoundIII.Comet.WithdrawBaseRead
import Benchmarks.CompoundIII.Comet.WithdrawBaseMathModel
import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsModel
import Benchmarks.CompoundIII.Comet.WithdrawBaseTailModel
import Benchmarks.CompoundIII.Comet.UpdateBaseModel
import Benchmarks.CompoundIII.Comet.AccrueInternalModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def withdrawBaseNext (evm : EVM.State) (src : AccountAddress) (amount : UInt256) : UInt256 :=
  withdrawBasePrincipal evm (withdrawBaseBasic evm src).principal amount

def withdrawBaseSupplied (evm : EVM.State) (src : AccountAddress) (amount : UInt256) : UInt256 :=
  withdrawSupplyAmount (withdrawBaseBasic evm src).principal (withdrawBaseNext evm src amount)

def withdrawBaseBorrowed (evm : EVM.State) (src : AccountAddress) (amount : UInt256) : UInt256 :=
  withdrawBorrowAmount (withdrawBaseBasic evm src).principal (withdrawBaseNext evm src amount)

inductive WithdrawBaseAfterAccrue (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | mathFailed (hf : ¬ WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount) :
      WithdrawBaseAfterAccrue v src recipient amount evm .reverted
  | totalsReverted (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount)
      (ht : withdrawBaseTotalsOutcome evm (withdrawBaseSupplied evm src amount)
        (withdrawBaseBorrowed evm src amount) = .reverted) :
      WithdrawBaseAfterAccrue v src recipient amount evm .reverted
  | totalsStatic (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount)
      (ht : withdrawBaseTotalsOutcome evm (withdrawBaseSupplied evm src amount)
        (withdrawBaseBorrowed evm src amount) = .staticViolation) :
      WithdrawBaseAfterAccrue v src recipient amount evm .staticViolation
  | updateReverted {evm'}
      (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount)
      (ht : withdrawBaseTotalsOutcome evm (withdrawBaseSupplied evm src amount)
        (withdrawBaseBorrowed evm src amount) = .ok evm')
      (hu : updateBaseOutcome v evm' src (withdrawBaseBasic evm src)
        (withdrawBaseNext evm src amount) = .reverted) :
      WithdrawBaseAfterAccrue v src recipient amount evm .reverted
  | updateStatic {evm'}
      (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount)
      (ht : withdrawBaseTotalsOutcome evm (withdrawBaseSupplied evm src amount)
        (withdrawBaseBorrowed evm src amount) = .ok evm')
      (hu : updateBaseOutcome v evm' src (withdrawBaseBasic evm src)
        (withdrawBaseNext evm src amount) = .staticViolation) :
      WithdrawBaseAfterAccrue v src recipient amount evm .staticViolation
  | done {evm' evm'' result}
      (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount)
      (ht : withdrawBaseTotalsOutcome evm (withdrawBaseSupplied evm src amount)
        (withdrawBaseBorrowed evm src amount) = .ok evm')
      (hu : updateBaseOutcome v evm' src (withdrawBaseBasic evm src)
        (withdrawBaseNext evm src amount) = .ok evm'')
      (tail : WithdrawBaseTailTrace v src recipient amount
        (withdrawBaseBalance evm (withdrawBaseBasic evm src).principal amount) evm'' result) :
      WithdrawBaseAfterAccrue v src recipient amount evm result

inductive WithdrawBaseTrace (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (ha : accrueOutcome v evm = .reverted) :
      WithdrawBaseTrace v src recipient amount evm .reverted
  | staticViolation (ha : accrueOutcome v evm = .staticViolation) :
      WithdrawBaseTrace v src recipient amount evm .staticViolation
  | done {evm' result} (ha : accrueOutcome v evm = .ok evm')
      (tail : WithdrawBaseAfterAccrue v src recipient amount evm' result) :
      WithdrawBaseTrace v src recipient amount evm result

def withdrawBaseReadBlock : List Stmt :=
  [.letDecl "srcUser" (some (.tuple
      [.elem (.int (.sint ⟨104, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨16, by decide⟩)),
        .elem (.int (.uint ⟨8, by decide⟩))]))
      (.storage ⟨"userBasic", [.mindex (.var "src")]⟩),
    .letDecl "srcPrincipal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
      (.field (.var "srcUser") "principal")]

def withdrawBaseUpdateStmt : Stmt :=
  .internalCall "updateBasePrincipal" [.var "src", .var "srcUser", .var "srcPrincipalNew"] "__c5"

def withdrawBaseCallable : CallableDecl :=
  { params := [⟨"src", .elem .address⟩, ⟨"to", .elem .address⟩,
      ⟨"amount", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := []
    body := [.internalCall "accrueInternal" [] "__c0"] ++ withdrawBaseReadBlock ++
      withdrawBaseMathBlock ++ withdrawBaseTotalsBlock ++ [withdrawBaseUpdateStmt] ++
      withdrawBaseTail }

theorem withdrawBaseCallable_lookup :
    lookupCallable? contract "withdrawBase" = some withdrawBaseCallable := rfl

def withdrawBaseEntry (imms : Store) (src recipient : AccountAddress) (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (((∅ : Store).insert "amount" (.int amount.toNat)).insert "to"
      (.address recipient)).insert "src" (.address src) }

def withdrawBaseReadFrame (frame : Frame) (evm : EVM.State) (src : AccountAddress) : Frame :=
  { frame with
    locals := (frame.locals.insert "srcUser" (userBasicValue (withdrawBaseBasic evm src))).insert
      "srcPrincipal" (.int (signed104 (withdrawBaseBasic evm src).principal)) }

def withdrawBaseAccruedFrame (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) : Frame :=
  let frame := withdrawBaseEntry (immStore v) src recipient amount
  { frame with locals := frame.locals.insert "__c0" .unit }

def withdrawBaseReadyFrame (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) : Frame :=
  withdrawBaseMathFrame
    (withdrawBaseReadFrame (withdrawBaseAccruedFrame v src recipient amount) evm src)
    evm (withdrawBaseBasic evm src).principal amount

def withdrawBaseAfterAccrueBlock : List Stmt :=
  withdrawBaseReadBlock ++ withdrawBaseMathBlock ++ withdrawBaseTotalsBlock ++
    [withdrawBaseUpdateStmt] ++ withdrawBaseTail

end Benchmarks.CompoundIII.Comet

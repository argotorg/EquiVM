import Benchmarks.Morpho.MetaMorphoV1_1.SetTimelockSource
import Benchmarks.Morpho.MetaMorphoV1_1.SetGuardianSource
import Benchmarks.Morpho.MetaMorphoV1_1.RevocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.PackedStorage
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Pending record reads and time guards shared by timelock and guardian acceptance. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def pendingUpdateWord (guardian : Bool) (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revocationSlot guardian)

def pendingUpdateTime (guardian : Bool) (word : UInt256) : UInt256 :=
  if guardian then UInt256.land (UInt256.shiftRight word ⟨160⟩) (UInt256.ofNat (2 ^ 64 - 1))
  else UInt256.shiftRight word ⟨192⟩

def pendingUpdateValue (guardian : Bool) (word : UInt256) : UInt256 :=
  UInt256.land word (if guardian then solcAddrMask else UInt256.ofNat (2 ^ 192 - 1))

abbrev acceptPendingAllowed (guardian : Bool) (evm : EVM.State) : Prop :=
  pendingUpdateTime guardian (pendingUpdateWord guardian evm) ≠ ⟨0⟩ ∧
    (pendingUpdateTime guardian (pendingUpdateWord guardian evm)).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat

def acceptPendingState (guardian : Bool) (evm : EVM.State) : EVM.State :=
  if guardian then setGuardianState evm
    (AccountAddress.ofNat (pendingUpdateValue true (pendingUpdateWord true evm)).toNat)
  else setTimelockState evm (pendingUpdateValue false (pendingUpdateWord false evm))

def acceptPendingFrame (guardian : Bool) (evm : EVM.State) (locals imms : Store) : Frame :=
  { contract := contract
    locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
      "afterTimelock_validAt"
      (uint256Value (pendingUpdateTime guardian (pendingUpdateWord guardian evm)))
    immutables := imms }

def acceptPendingCall (guardian : Bool) : Stmt :=
  .internalCall (if guardian then "_setGuardian" else "_setTimelock")
    [.storage ⟨revocationName guardian, [.field "value"]⟩] "__c0"

def acceptPendingNonzero : Expr :=
  .binary .ne (.var "afterTimelock_validAt") (.intLit 0)
def acceptPendingTime : Expr :=
  .binary .ge (.env .timestamp) (.var "afterTimelock_validAt")

def acceptPendingBody (guardian : Bool) : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "__calldata" (some .bytes) (.env .msgData),
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))),
    .letDecl "afterTimelock_validAt" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.storage ⟨revocationName guardian, [.field "validAt"]⟩),
    .require acceptPendingNonzero, .require acceptPendingTime, acceptPendingCall guardian]

theorem pendingUpdateTimeSource (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? (revocationName guardian) = none) :
    evalExpr? config ⟨contract, locals, imms⟩ evm
      (.storage ⟨revocationName guardian, [.field "validAt"]⟩) =
      .ok (uint256Value (pendingUpdateTime guardian (pendingUpdateWord guardian evm))) := by
  cases guardian
  · exact evalStorage_pendingTimelockValidAt evm locals imms hbase
  · exact evalStorage_pendingGuardianValidAt evm locals imms hbase

theorem acceptPendingRead (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? (revocationName guardian) = none) :
    ABlock config evm ⟨contract, locals, imms⟩ (acceptPendingBody guardian)
      (acceptPendingFrame guardian evm locals imms)
      [.require acceptPendingNonzero, .require acceptPendingTime, acceptPendingCall guardian] := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (pendingUpdateTimeSource guardian evm _ imms ?_)) htail
  cases guardian <;> simpa [revocationName] using hbase

theorem acceptPendingNonzeroSource (guardian : Bool) (evm : EVM.State) (locals imms : Store) :
    evalExpr? config (acceptPendingFrame guardian evm locals imms) evm acceptPendingNonzero =
      .ok (.bool (decide (pendingUpdateTime guardian (pendingUpdateWord guardian evm) ≠ ⟨0⟩))) := by
  apply SourceMemory.wordNeSource
  · simp only [evalExpr?, acceptPendingFrame, store_get_self, EvalResult.ofOption]
  · simp [evalExpr?, uint256Value, pure, UInt256.toNat]

theorem acceptPendingTimeSource (guardian : Bool) (evm : EVM.State) (locals imms : Store) :
    evalExpr? config (acceptPendingFrame guardian evm locals imms) evm acceptPendingTime =
      .ok (.bool (decide ((pendingUpdateTime guardian (pendingUpdateWord guardian evm)).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat))) := by
  apply naturalGeSource
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, acceptPendingFrame, store_get_self, EvalResult.ofOption]

theorem acceptPendingPrefix (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? (revocationName guardian) = none)
    (hgood : acceptPendingAllowed guardian evm) :
    ABlock config evm ⟨contract, locals, imms⟩ (acceptPendingBody guardian)
      (acceptPendingFrame guardian evm locals imms) [acceptPendingCall guardian] := by
  apply ((acceptPendingRead guardian evm locals imms hwv hhi hbase).requireStep (by
    simp [acceptPendingNonzeroSource, hgood.1])).requireStep
  simp only [acceptPendingTimeSource, hgood.2, decide_true]

end Benchmarks.Morpho.MetaMorphoV1_1

import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def TotalsChangeFits (evm : EVM.State) (borrow : Bool) (increase decrease : UInt256) : Prop :=
  (withdrawBaseTotal evm borrow).toNat + increase.toNat < 2^104 ∧
    decrease.toNat ≤ (withdrawBaseTotal evm borrow + increase).toNat

instance (evm : EVM.State) (borrow : Bool) (increase decrease : UInt256) :
    Decidable (TotalsChangeFits evm borrow increase decrease) := by
  unfold TotalsChangeFits; infer_instance

def totalsChangeState (evm : EVM.State) (borrow : Bool) (increase decrease : UInt256) : EVM.State :=
  storeTotalsPrincipal evm borrow (UInt256.sub (withdrawBaseTotal evm borrow + increase) decrease)

def totalsChangeOutcome (evm : EVM.State) (borrow : Bool) (increase decrease : UInt256) :
    InternalOutcome :=
  if TotalsChangeFits evm borrow increase decrease then
    if evm.executionEnv.perm then .ok (totalsChangeState evm borrow increase decrease)
    else .staticViolation
  else .reverted

theorem totalsChangeOutcome_perm {evm evm' borrow increase decrease}
    (h : totalsChangeOutcome evm borrow increase decrease = .ok evm') :
    evm'.executionEnv.perm = true := by
  unfold totalsChangeOutcome at h
  split at h
  next hf =>
    split at h
    next hp =>
      cases h
      simpa only [totalsChangeState, storeTotalsPrincipal, storageStore_executionEnv] using hp
    next hp => cases h
  next hf => cases h

def totalsChangeStmt (borrow : Bool) (increaseName decreaseName : Ident) : Stmt :=
  .assign .storage ⟨totalsPrincipalName borrow, []⟩ (.inRange (.uint ⟨104, by decide⟩)
    (.binary .sub (.inRange (.uint ⟨104, by decide⟩) (.binary .add
      (.storage ⟨totalsPrincipalName borrow, []⟩) (.var increaseName))) (.var decreaseName)))

def totalsChangeResult (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (increase decrease : UInt256) : ExecResult :=
  match totalsChangeOutcome evm borrow increase decrease with
  | .ok evm' => .ok frame evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

def transferBaseTotalsState (evm : EVM.State) (supplied withdrawn borrowed repaid : UInt256) :
    EVM.State :=
  totalsChangeState (totalsChangeState evm false supplied withdrawn) true borrowed repaid

def transferBaseTotalsOutcome (evm : EVM.State) (supplied withdrawn borrowed repaid : UInt256) :
    InternalOutcome :=
  match totalsChangeOutcome evm false supplied withdrawn with
  | .ok evm' => totalsChangeOutcome evm' true borrowed repaid
  | .reverted => .reverted
  | .staticViolation => .staticViolation

theorem transferBaseTotalsOutcome_perm {evm evm' supplied withdrawn borrowed repaid}
    (h : transferBaseTotalsOutcome evm supplied withdrawn borrowed repaid = .ok evm') :
    evm'.executionEnv.perm = true := by
  unfold transferBaseTotalsOutcome at h
  split at h
  next evm'' hfirst => exact totalsChangeOutcome_perm h
  next hfirst => cases h
  next hfirst => cases h

def transferBaseTotalsBlock : List Stmt :=
  [totalsChangeStmt false "supplyAmount" "withdrawAmount",
    totalsChangeStmt true "borrowAmount" "repayAmount"]

def transferBaseTotalsResult (frame : Frame) (evm : EVM.State)
    (supplied withdrawn borrowed repaid : UInt256) : ExecResult :=
  match transferBaseTotalsOutcome evm supplied withdrawn borrowed repaid with
  | .ok evm' => .ok frame evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

end Benchmarks.CompoundIII.Comet

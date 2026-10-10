import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def supplyBaseSupplyState (evm : EVM.State) (supplied : UInt256) : EVM.State :=
  storeTotalsPrincipal evm false (withdrawBaseTotal evm false + supplied)

def supplyBaseTotalsState (evm : EVM.State) (supplied repaid : UInt256) : EVM.State :=
  let evm' := supplyBaseSupplyState evm supplied
  storeTotalsPrincipal evm' true (UInt256.sub (withdrawBaseTotal evm' true) repaid)

def supplyBaseTotalsOutcome (evm : EVM.State) (supplied repaid : UInt256) : InternalOutcome :=
  if (withdrawBaseTotal evm false).toNat + supplied.toNat < 2^104 then
    if evm.executionEnv.perm then
      if repaid.toNat ≤ (withdrawBaseTotal (supplyBaseSupplyState evm supplied) true).toNat then
        .ok (supplyBaseTotalsState evm supplied repaid) else .reverted
    else .staticViolation
  else .reverted

def supplyBaseTotalsBlock : List Stmt :=
  [.assign .storage ⟨"totalSupplyBase", []⟩ (.inRange (.uint ⟨104, by decide⟩)
      (.binary .add (.storage ⟨"totalSupplyBase", []⟩) (.var "supplyAmount"))),
    .assign .storage ⟨"totalBorrowBase", []⟩ (.inRange (.uint ⟨104, by decide⟩)
      (.binary .sub (.storage ⟨"totalBorrowBase", []⟩) (.var "repayAmount")))]

def supplyBaseTotalsResult (frame : Frame) (evm : EVM.State) (supplied repaid : UInt256) :
    ExecResult :=
  match supplyBaseTotalsOutcome evm supplied repaid with
  | .ok evm' => .ok frame evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

end Benchmarks.CompoundIII.Comet

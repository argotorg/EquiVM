import Benchmarks.CompoundIII.Comet.TotalsPrincipalWrite
import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def withdrawBaseTotal (evm : EVM.State) (borrow : Bool) : UInt256 :=
  totalsPrincipalWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) borrow

def withdrawBaseSupplyState (evm : EVM.State) (supplied : UInt256) : EVM.State :=
  storeTotalsPrincipal evm false (UInt256.sub (withdrawBaseTotal evm false) supplied)

def withdrawBaseTotalsState (evm : EVM.State) (supplied borrowed : UInt256) : EVM.State :=
  let evm' := withdrawBaseSupplyState evm supplied
  storeTotalsPrincipal evm' true (withdrawBaseTotal evm' true + borrowed)

def withdrawBaseTotalsOutcome (evm : EVM.State) (supplied borrowed : UInt256) : InternalOutcome :=
  if supplied.toNat ≤ (withdrawBaseTotal evm false).toNat then
    if evm.executionEnv.perm then
      if (withdrawBaseTotal (withdrawBaseSupplyState evm supplied) true).toNat + borrowed.toNat <
          2^104 then .ok (withdrawBaseTotalsState evm supplied borrowed) else .reverted
    else .staticViolation
  else .reverted

def withdrawBaseTotalsBlock : List Stmt :=
  [.assign .storage ⟨"totalSupplyBase", []⟩ (.inRange (.uint ⟨104, by decide⟩)
      (.binary .sub (.storage ⟨"totalSupplyBase", []⟩) (.var "withdrawAmount"))),
    .assign .storage ⟨"totalBorrowBase", []⟩ (.inRange (.uint ⟨104, by decide⟩)
      (.binary .add (.storage ⟨"totalBorrowBase", []⟩) (.var "borrowAmount")))]

def withdrawBaseTotalsResult (frame : Frame) (evm : EVM.State) (supplied borrowed : UInt256) :
    ExecResult :=
  match withdrawBaseTotalsOutcome evm supplied borrowed with
  | .ok evm' => .ok frame evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

end Benchmarks.CompoundIII.Comet

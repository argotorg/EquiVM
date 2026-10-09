import Benchmarks.CompoundIII.Comet.PrincipalTransferEventSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferBaseEvents : List Stmt :=
  [principalTransferEvent false "src" "withdrawAmount" "__c12",
    principalTransferEvent true "dst" "supplyAmount" "__c13"]

theorem transferBaseEvents_source (frame : Frame) (evm : EVM.State) (src dst : AccountAddress)
    (withdrawn supplied : UInt256) (hc : frame.contract = contract)
    (hsrc : frame.locals.get? "src" = some (.address src))
    (hdst : frame.locals.get? "dst" = some (.address dst))
    (hw : frame.locals.get? "withdrawAmount" = some (.int withdrawn.toNat))
    (hs : frame.locals.get? "supplyAmount" = some (.int supplied.toNat))
    (hi : frame.locals.get? "baseSupplyIndex" = none)
    (hW : withdrawn.toNat < 2^104) (hS : supplied.toNat < 2^104) :
    ∃ final, ExecBlock config frame evm transferBaseEvents (.ok final evm) := by
  have hburn := principalTransferEvent_source frame evm false src withdrawn
    "src" "withdrawAmount" "__c12" (by decide) hc hsrc hw hi hW
  let f := principalTransferEventFrame frame evm withdrawn "__c12"
  have hfc : f.contract = contract := (principalTransferEventFrame_contract _ _ _ _).trans hc
  have hfd : f.locals.get? "dst" = some (.address dst) := by
    rw [principalTransferEventFrame_get _ _ _ _ _ (by decide)]
    exact hdst
  have hfs : f.locals.get? "supplyAmount" = some (.int supplied.toNat) := by
    rw [principalTransferEventFrame_get _ _ _ _ _ (by decide)]
    exact hs
  have hfi : f.locals.get? "baseSupplyIndex" = none := by
    rw [principalTransferEventFrame_get _ _ _ _ _ (by decide)]
    exact hi
  have hmint := principalTransferEvent_source f evm true dst supplied
    "dst" "supplyAmount" "__c13" (by decide) hfc hfd hfs hfi hS
  exact ⟨_, ExecBlock.consNormal hburn (ExecBlock.consNormal hmint .nil)⟩

end Benchmarks.CompoundIII.Comet

import Reasoning.SolmBody
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace UniswapV2Pair

abbrev optionalSafeTransferFrame (caller : Frame) (retVar : Ident) (value : UInt256) : Frame :=
  if value = ⟨0⟩ then caller else resumeAfterInternalCall caller retVar none

theorem optionalSafeTransferSkip {cfg : Config} {caller : Frame} {evm : EVM.State}
    {condition : Expr} {body : List Stmt} {retVar : Ident} {value : UInt256}
    (hz : value = ⟨0⟩) (hcond : evalExpr? cfg caller evm condition = .ok (.bool false)) :
    ExecStmt cfg caller evm (.ite condition body [])
      (.ok (optionalSafeTransferFrame caller retVar value) evm) := by
  rw [optionalSafeTransferFrame, if_pos hz]
  exact ExecStmt.iteFalse hcond ExecBlock.nil

end UniswapV2Pair

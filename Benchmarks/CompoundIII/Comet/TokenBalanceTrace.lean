import Benchmarks.CompoundIII.Comet.TokenBalanceCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

inductive TokenBalanceTrace (asset : AccountAddress) (evm : EVM.State) :
    Option (EVM.State × UInt256) → Prop where
  | response {evm' : EVM.State} {z : Bool} {out : ByteArray}
      (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
        (z, evm', out) false) (hh : out.size < 2^255) :
      TokenBalanceTrace asset evm
        (if z = true ∧ 32 ≤ out.size then some (evm', calldataWord out 0) else none)

def wordCallResult (frame : Frame) (ret : Ident) (result : Option (EVM.State × UInt256)) :
    ExecResult :=
  match result with
  | none => .reverted
  | some (evm', value) =>
      .ok { frame with locals := frame.locals.insert ret (.int (Int.ofNat value.toNat)) } evm'

theorem tokenBalanceTrace_source {asset : AccountAddress} {evm : EVM.State}
    {result : Option (EVM.State × UInt256)} (ht : TokenBalanceTrace asset evm result)
    (frame : Frame) (expr : Expr) (ret : Ident)
    (he : evalExpr? config frame evm expr = .ok (.address asset)) :
    ExecStmt config frame evm
      (.externalCall expr "balanceOf" (.intLit 0) [.env .this] ret (perm := false))
      (wordCallResult frame ret result) := by
  cases ht with
  | @response evm' z out hc hh =>
    by_cases hv : z = true ∧ 32 ≤ out.size
    · rw [if_pos hv]
      rcases hv with ⟨rfl, hlo⟩
      exact tokenBalance_source_ok he hc hlo hh
    · rw [if_neg hv]
      exact tokenBalance_source_revert he hc hv

end Benchmarks.CompoundIII.Comet

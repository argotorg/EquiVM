import Reasoning.ExternalCall
import Solm.Equiv

/-!
# Clipper-local external-call transport helpers

The generic call transport is sufficient for Clipper: related call states have equal account
maps, original account maps, and execution environments.  Keep this local name for downstream
proofs while the call sites migrate to the generic theorem.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Clipper

theorem typedCallViaEVM_accountMapEquiv_noSubstate {cfg : Config}
    {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value} {z : Bool}
    {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out) callPerm)
    (hAccounts : evm_evm.accountMap = evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hEnv : evm_evm.executionEnv = evm_solm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z, { evm_solm with accountMap := σ'_solm, substate := A'_solm }, out)
        callPerm ∧
      evm'_evm.accountMap = σ'_solm := by
  exact Reasoning.Theory.typedCallViaEVM_accountMapEquiv
    hcall hAccounts hOriginalAccounts hEnv

end Benchmarks.Dss.Clipper

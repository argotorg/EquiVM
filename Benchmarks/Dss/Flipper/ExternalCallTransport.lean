import Benchmarks.Dss.Flipper.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-- Replay a typed call when the caller states have the same call inputs. -/
theorem flipper_typedCallViaEVM_sameInputs
    {cfg : Config} {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out) callPerm)
    (hAccounts : evm_evm.accountMap = evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hEnv : evm_evm.executionEnv = evm_solm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z, { evm_solm with accountMap := σ'_solm, substate := A'_solm }, out)
        callPerm ∧
      EVMStateEquiv evm'_evm
        { evm_solm with accountMap := σ'_solm, substate := A'_solm } := by
  obtain ⟨σ', A', hcall', hσ'⟩ :=
    typedCallViaEVM_accountMapEquiv hcall hAccounts hOriginalAccounts hEnv
  refine ⟨σ', A', hcall', ?_⟩
  exact ⟨(typedCallViaEVM_executionEnv_eq hcall).trans hEnv, hσ'⟩

end Benchmarks.Dss.Flipper

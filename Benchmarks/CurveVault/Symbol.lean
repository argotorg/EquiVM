import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.StringRoutine

variable {fork : Ethereum.Fork}

/-!
# Vault `symbol()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body (its own `calldatasize`/`callvalue` guard first), the Stele body evaluation, and the
`…Body` theorem `Correct.lean` consumes.
Dispatcher: bucket 0, arm entry pc 73; reach lemma `vaultReachSymbolBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultSymbolBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 29)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 29) rfl hsel
  have hd : dispatchMsg contract I.calldata = some symbolTransition := by
    apply vaultDispatch_symbol
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := symbolTransition) (pc := UInt256.ofNat 6544)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachSymbolBody hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (symbolTransition.params.map Param.name)
      (transitionSignature symbolTransition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  rcases vaultStringRoutine false SourceState.init (initState_memoryPaidByGas σ σ₀ g A I)
    hvalue hsize (by native_decide) (by simp) rdBody with hsuccess | ⟨hsource, hrev⟩
  · rcases hsuccess with ⟨bytes, out, locals', hsource, hencode, hret⟩
    exact hret.reEquivExecution hcode hd hdec hsource (returnEquiv_of_encode hencode)
  · exact hrev.reEquivExecutionRevert hcode hd hdec hsource

/-- `symbol()`: the theorem `Correct.lean` routes selector 29 to. -/
theorem vaultSymbolBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 29)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultSymbolBodyCore hcode hsize hsel

end Benchmarks.CurveVault

import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.StringRoutine

variable {fork : Ethereum.Fork}

/-!
# Vault `name()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body (its own `calldatasize`/`callvalue` guard first), the Stele body evaluation, and the
`…Body` theorem `Correct.lean` consumes.
Dispatcher: bucket 4, arm entry pc 73; reach lemma `vaultReachNameBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultNameBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 4)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 4) rfl hsel
  have hd : dispatchMsg contract I.calldata = some nameTransition := by
    apply vaultDispatch_name
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := nameTransition) (pc := UInt256.ofNat 6437)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachNameBody hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (nameTransition.params.map Param.name)
      (transitionSignature nameTransition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  rcases vaultStringRoutine true SourceState.init (initState_memoryPaidByGas σ σ₀ g A I)
    hvalue hsize (by native_decide) (by simp) rdBody with hsuccess | ⟨hsource, hrev⟩
  · rcases hsuccess with ⟨bytes, out, locals', hsource, hencode, hret⟩
    exact hret.reEquivExecution hcode hd hdec hsource (returnEquiv_of_encode hencode)
  · exact hrev.reEquivExecutionRevert hcode hd hdec hsource

/-- `name()`: the theorem `Correct.lean` routes selector 4 to. -/
theorem vaultNameBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 4)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultNameBodyCore hcode hsize hsel

end Benchmarks.CurveVault

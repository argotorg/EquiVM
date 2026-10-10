import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.RevocationEntry

/-!
# MetaMorphoV1_1 `revokePendingGuardian()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 10526; reach lemma `metaMorphoV1_1ReachRevokePendingGuardianBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- `revokePendingGuardian()`: the theorem `Correct.lean` routes selector 7 to. -/
theorem metaMorphoV1_1RevokePendingGuardianBody {σ σ₀ A I} {g : UInt256}
    (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 7)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 7) rfl hsel
  have hd : dispatchMsg contract I.calldata = some revokePendingGuardianTransition := by
    apply metaMorphoV1_1Dispatch_revokePendingGuardian <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (revokePendingGuardianTransition.params.map Param.name)
      (transitionSignature revokePendingGuardianTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachRevokePendingGuardianBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨_, _, r1⟩ := revocationReachRole v true (by simp) hwv hsz hhi hsize rd
      by_cases hrole : guardianRoleAllowed evm
      · obtain ⟨_, _, r2⟩ := revocationReachStore (evm := evm) v true (by simp) hrole r1
        by_cases hperm : I.perm = true
        · obtain ⟨final, hbody⟩ := revocationBodyReturns true evm ∅ (immStore v)
            hwv hhi hrole (by simp)
          exact (revocationStoreReturn v true (by simp) hperm r2).reEquivExecutionGen
            hcode hd hdec hbody (storageStore_accountMap evm _ _ _).symm voidReturnEquiv
        · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
          exact (revocationStoreStatic v true (by simp) hp r2).reEquivStaticHalt
            hcode hd hdec (revocationBodyStatic true evm ∅ (immStore v)
              hwv hhi hrole (by simp) hp)
      · have hrev := revocationRevertRole (evm := evm) v true (by simp) hrole r1
        exact hrev.reEquivExecutionRevert hcode hd hdec
            (revocationBodyRevertsRole true evm ∅ (immStore v) hwv hhi hrole)
    · have hrev := revocationRevertHuge v true (by simp) hwv (by omega) hsize rd
      exact hrev.reEquivExecutionRevert hcode hd hdec
          (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (revocationRevertNonPayable v true (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1

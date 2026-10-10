import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingSource
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingRoutines

/-!
# MetaMorphoV1_1 `acceptGuardian()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4172; reach lemma `metaMorphoV1_1ReachAcceptGuardianBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- `acceptGuardian()`: the theorem `Correct.lean` routes selector 48 to. -/
theorem metaMorphoV1_1AcceptGuardianBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 48)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 48) rfl hsel
  have hd : dispatchMsg contract I.calldata = some acceptGuardianTransition := by
    apply metaMorphoV1_1Dispatch_acceptGuardian <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (acceptGuardianTransition.params.map Param.name)
      (transitionSignature acceptGuardianTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachAcceptGuardianBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨_, _, r1⟩ := acceptPendingReachRead v true (by simp) hwv hsz hhi hsize rd
      by_cases hgood : acceptPendingAllowed true evm
      · obtain ⟨_, _, r2⟩ := acceptPendingReachValue (evm := evm) v true (by simp) hgood r1
        by_cases hperm : I.perm = true
        · obtain ⟨final, hbody⟩ := acceptPendingBodyReturns true evm ∅ (immStore v)
            hwv hhi (by simp) hgood
          have hret := acceptPendingStoreReturn (evm := evm) v true (by simp) hperm r2
          exact hret.reEquivExecutionGen hcode hd hdec hbody rfl voidReturnEquiv
        · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
          have hstatic := acceptPendingStoreStatic (evm := evm) v true (by simp) hp r2
          exact hstatic.reEquivStaticHalt hcode hd hdec
            (acceptPendingBodyStatic true evm ∅ (immStore v)
              hwv hhi (by simp) hgood hp)
      · have hrev := acceptPendingRevertTime (evm := evm) v true (by simp) hgood r1
        exact hrev.reEquivExecutionRevert hcode hd hdec
            (acceptPendingBodyReverts true evm ∅ (immStore v) hwv hhi (by simp) hgood)
    · have hrev := acceptPendingRevertHuge v true (by simp) hwv (by omega) hsize rd
      exact hrev.reEquivExecutionRevert hcode hd hdec
          (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (acceptPendingRevertNonPayable v true (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1

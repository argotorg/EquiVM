import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitTimelockRoutines

/-!
# MetaMorphoV1_1 `submitTimelock(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 6869; reach lemma `metaMorphoV1_1ReachSubmitTimelockBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- `submitTimelock(uint256)`: the theorem `Correct.lean` routes selector 33 to. -/
theorem metaMorphoV1_1SubmitTimelockBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 33)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 33) rfl hsel
  have hd : dispatchMsg contract I.calldata = some submitTimelockTransition := by
    apply metaMorphoV1_1Dispatch_submitTimelock <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSubmitTimelockBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let value := calldataWord I.calldata 4
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec := decodeCalldata_uint256_ok (x := "newTimelock") hlen hhi
        obtain ⟨_, _, rd12917⟩ := submitTimelockReachOwner v (by simp) hwv hlen hhi hsize rd
        by_cases howner : ownerAddress evm = I.source
        · obtain ⟨_, _, rd6897⟩ := checkOwnerReturn v (by simp) howner
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
          by_cases hgood : submitTimelockAllowed evm value
          · obtain ⟨_, _, rd6938⟩ := submitTimelockReachBranch (evm := evm) v (by simp)
              hgood rd6897
            by_cases hperm : I.perm = true
            · by_cases hfit : submitTimelockFits evm value
              · obtain ⟨final, hbody⟩ := submitTimelockBodyReturns evm (immStore v) value
                  hwv hhi howner hgood hfit
                have hret := submitTimelockStoreReturn (evm := evm) v (by simp)
                  hperm hgood.2.2 hfit rd6938
                exact hret.reEquivExecutionGen hcode hd hdec hbody rfl voidReturnEquiv
              · have hrev := submitTimelockRevertOverflow (evm := evm) v (by simp)
                  hperm hgood.2.2 hfit rd6938
                exact hrev.reEquivExecutionRevert hcode hd hdec
                  (submitTimelockBodyRevertsOverflow evm (immStore v) value
                    hwv hhi howner hgood hfit)
            · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
              have hstatic := submitTimelockStoreStatic (evm := evm) v (by simp) hp rd6938
              exact hstatic.reEquivStaticHalt hcode hd hdec
                (submitTimelockBodyStatic evm (immStore v) value hwv hhi howner hgood hp)
          · have hrev := submitTimelockRevertGuard (evm := evm) v (by simp) hgood rd6897
            exact hrev.reEquivExecutionRevert hcode hd hdec
              (submitTimelockBodyRevertsGuard evm (immStore v) value hwv hhi howner hgood)
        · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
            hcode hd hdec (adminBodyRevertsOwner evm _ (immStore v) submitTimelockTail
              hwv hhi howner)
      · have hrev := submitTimelockRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := submitTimelockRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_uint256_none_short (by omega))
  · exact dispatchedRevert hcode hd (submitTimelockRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1

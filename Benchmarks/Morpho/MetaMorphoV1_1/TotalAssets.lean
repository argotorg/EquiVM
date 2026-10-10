import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.TotalAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.TotalAssetsRoutines

/-!
# MetaMorphoV1_1 `totalAssets()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 11049; reach lemma `metaMorphoV1_1ReachTotalAssetsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `totalAssets()`: the theorem `Correct.lean` routes selector 0 to. -/
theorem metaMorphoV1_1TotalAssetsBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 0) rfl hsel
  have hd : dispatchMsg contract I.calldata = some totalAssetsTransition := by
    apply metaMorphoV1_1Dispatch_totalAssets <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (totalAssetsTransition.params.map Param.name)
      (transitionSignature totalAssetsTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachTotalAssetsBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨aw1, k1, C1, h1⟩ := totalAssetsReachAccrual v (by simp) hwv hsz hhi hsize rd
      rcases accruedAssetsSimulation v (by simp) hsize solcFreePtrMem_mload64
          (by decide) (by rw [solcFreePtrMem_size]) SourceState.init
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
        ⟨hbad, hrev⟩ | ⟨evm', frame', lost, total, shares, ptr, mem', out, hs', hstore,
          hfree, hlo, hmem, hbody, aw2, k2, C2, h2⟩
      · exact hrev.reEquivExecutionRevert hcode hd hdec
          (totalAssetsBodyReverts v ∅ hwv hhi hbad)
      · exact (totalAssetsEncodeReturn v (by simp) h2).reEquivExecutionGen hcode hd hdec
          (totalAssetsBodyReturns v ∅ hwv hhi hbody) rfl
          (returnEquiv_of_encode (uint256ReturnEncoding _))
    · exact (totalAssetsRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (totalAssetsRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1

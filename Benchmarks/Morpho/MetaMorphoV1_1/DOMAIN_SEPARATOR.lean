import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.DomainCacheRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.DomainEntry
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositEntry

/-!
# MetaMorphoV1_1 `DOMAIN_SEPARATOR()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9689; reach lemma `metaMorphoV1_1ReachDOMAIN_SEPARATORBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `DOMAIN_SEPARATOR()`: the theorem `Correct.lean` routes selector 14 to. -/
theorem metaMorphoV1_1DOMAIN_SEPARATORBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 14)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 14) rfl hsel
  have hd : dispatchMsg contract I.calldata = some dOMAIN_SEPARATORTransition := by
    apply metaMorphoV1_1Dispatch_dOMAIN_SEPARATOR <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (dOMAIN_SEPARATORTransition.params.map Param.name)
      (transitionSignature dOMAIN_SEPARATORTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachDOMAIN_SEPARATORBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨aw1, k1, C1, h1⟩ := domainReachCache v (by simp) hwv hsz hhi hsize rd
      obtain ⟨aw2, k2, C2, h2⟩ := domainSeparatorRoutine v 128 (by simp) (by decide)
        (by decide) solcFreePtrMem_mload64
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
      exact (maxDepositEncodeReturn v (by simp) h2).reEquivExecutionGen hcode hd hdec
        (domainSeparatorViewBody evm v hwv hhi) rfl
        (returnEquiv.returned rfl (bytes32ReturnEncoding _))
    · exact (domainRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (domainRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1

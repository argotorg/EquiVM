import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation
import Benchmarks.Morpho.MetaMorphoV1_1.StringSetSimulation

/-!
# MetaMorphoV1_1 `setName(string)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2240; reach lemma `metaMorphoV1_1ReachSetNameBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `setName(string)`: the theorem `Correct.lean` routes selector 58 to. -/
theorem metaMorphoV1_1SetNameBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 58)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 58) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setNameTransition := by
    apply metaMorphoV1_1Dispatch_setName <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSetNameBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (stringSetNonpayable v false (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  obtain ⟨aw1, k1, C1, h1⟩ := stringSetDecodeEntry v false (by simp) hwv rd
  rcases stringDecoder v "newName" (by simp) hsz hsize (by decide) (by decide)
    solcFreePtrMem_mload64 (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
    ⟨hdec, hrev⟩ | ⟨hdec, hsmall, hdecode⟩
  · exact hrev.reEquivDecodingFailed hcode hd hdec
  · have hhi : I.calldata.size < 2 ^ 255 + 4 := by
      by_contra hh
      have hnone := decodeCalldata_string_none_huge (x := "newName") (Nat.le_of_not_gt hh)
      rw [hdec] at hnone
      cases hnone
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    rcases hdecode with ⟨hbad, hrev⟩ | ⟨hfit, mem, aw2, k2, C2, hb, _hf, h2⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec
        (stringSetRevertsAllocation false evm (immStore v) _ hwv hhi hsmall hbad)
    · rcases stringSetSimulation v false (immStore v) (by simp) SourceState.init hwv hhi
        hsmall hfit hb h2 with ⟨hsource, hrev⟩ | ⟨hsource, hret⟩ | ⟨hsource, hstatic⟩
      · exact hrev.reEquivExecutionRevert hcode hd hdec hsource
      · exact hret.reEquivExecutionGen hcode hd hdec hsource rfl voidReturnEquiv
      · exact hstatic.reEquivStaticHalt hcode hd hdec hsource

end Benchmarks.Morpho.MetaMorphoV1_1

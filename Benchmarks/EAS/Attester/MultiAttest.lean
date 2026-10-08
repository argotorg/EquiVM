import Benchmarks.EAS.Attester.MultiAttestExternal

/-!
# Attester multiAttest proof scaffold

Reach arm 102, decoder 2482, body 935. Relate the schemas and nested inputs, including
noncanonical aliases and wrapped nested offsets. Establish the outer/inner loop invariants,
nonempty/equal lengths, and the request array in memory. Before CALL 1786 the free pointer
is 160 + 192*n + 480*sum(inner lengths). Match the raw zero-value call, return-copy rounding,
the bytes32[] decoder at 3547, and its allocation guard at 3681–3693 before canonical return
encoding. Neither the number nor the content of returned UIDs is checked against the input.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterMultiAttestBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hc := hcode.trans (deployedRuntime_eq_layout hfit)
  have hdispatch := attesterMultiAttestDispatch hselector
  have hfour := calldata_size_ge_of_selIs I attesterMultiAttestSelBytes rfl hselector
  have hsel : I.calldata.extract 0 4 = attesterMultiAttestSelBytes :=
    (byteArray_eq_of_beq hselector).symm
  obtain ⟨k, C, rd⟩ := attesterMultiAttestReachDecode (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hc hvalue hsize hselector
  rcases multiAttestBodyView rd (by simp) with ⟨hbad, hrev⟩ | ⟨hchecks, k, C, rd⟩
  · exact hrev.reEquivDecodingFailed hc hdispatch
      (decodeCalldata_arrays_none_of_bad_heads uint256 "schemas" "schemaInputs" I.calldata hbad)
  by_cases hshape : BatchShape I.calldata
  · obtain ⟨eas, heas⟩ := eas_of_fit hfit
    have heas' : (restrictImmutables contract imms).get? "_eas" = some (.address eas) := by
      rw [restrictImmutables_get? (by decide), heas]
    rcases multiAttestBuildRequests rd (by simp) hchecks hshape hsize with
      ⟨hbad, hrev⟩ | ⟨hrows, aw, k, C, rd⟩
    · cases hdecode : decodeArrays? uint256 I.calldata with
      | none => exact hrev.reEquivDecodingFailed hc hdispatch (multiAttestDecode_none hdecode)
      | some values =>
          obtain ⟨schemas, rows, _, rfl, _, _, _⟩ := decodeArrays_first_facts hdecode
          rcases multiAttestSourceBuild
            (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hvalue heas' hdecode hshape hsel with
            ⟨_, hsource⟩ | ⟨hvalid, _⟩
          · exact hrev.reEquivExecutionRevert hc hdispatch (multiAttestDecode_some hdecode) hsource
          · exact False.elim (hbad hvalid)
    · obtain ⟨values, hdecode⟩ := hrows.decode_exists (.inr rfl) hchecks hsize hfour hsel
        (by decide +kernel)
      obtain ⟨schemas, rows, _, rfl, _, _, _⟩ := decodeArrays_first_facts hdecode
      rcases multiAttestSourceBuild
        (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hvalue heas' hdecode hshape hsel with
        ⟨hbad, _⟩ | ⟨_, locals, hprefix, hlocalEas, hrequest, halloc⟩
      · exact False.elim (hbad hrows)
      · obtain ⟨aw, k, C, rd⟩ := multiAttestPrepare rd (by simp) hchecks hshape hrows
        exact multiAttestExternalCorrect imms hfit hc hselector hdecode hshape hrows heas
          hprefix hlocalEas hrequest halloc rd
  · have hrev := multiAttestBadShape rd (by simp) hshape
    cases hdecode : decodeArrays? uint256 I.calldata with
    | none => exact hrev.reEquivDecodingFailed hc hdispatch (multiAttestDecode_none hdecode)
    | some values =>
        obtain ⟨schemas, rows, _, rfl, hslen, hrlen, _⟩ := decodeArrays_first_facts hdecode
        have hsource := multiAttestSourceBadShape
          (schemas := schemas) (rows := rows)
          (imms := restrictImmutables contract imms)
          (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hvalue
          (by simpa only [hslen, hrlen, BatchShape] using hshape)
        exact hrev.reEquivExecutionRevert hc hdispatch (multiAttestDecode_some hdecode) hsource


end Benchmarks.EAS.Attester

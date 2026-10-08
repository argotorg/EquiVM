import Benchmarks.EAS.Attester.MultiRevokeExternal

/-!
# Attester multiRevoke proof scaffold

Reach arm 81, decoder 2482, body 195. Relate schemas and nested UIDs, including aliased,
unaligned, and wrapped offsets. Establish both loop invariants, nonempty/equal lengths,
and the ordered request array. EXTCODESIZE at 891 must be nonzero before CALL 906. Match
failed calls and successful calls with arbitrary ignored return bytes. Every request value
and the CALL value is zero; no storage slot belongs to this wrapper.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterMultiRevokeBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hc := hcode.trans (deployedRuntime_eq_layout hfit)
  have hdispatch := attesterMultiRevokeDispatch hselector
  have hfour := calldata_size_ge_of_selIs I attesterMultiRevokeSelBytes rfl hselector
  have hsel : I.calldata.extract 0 4 = attesterMultiRevokeSelBytes :=
    (byteArray_eq_of_beq hselector).symm
  obtain ⟨k, C, rd⟩ := attesterMultiRevokeReachDecode (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hc hvalue hsize hselector
  rcases multiRevokeBodyView rd (by simp) with ⟨hbad, hrev⟩ | ⟨hchecks, k, C, rd⟩
  · exact hrev.reEquivDecodingFailed hc hdispatch
      (decodeCalldata_arrays_none_of_bad_heads bytes32 "schemas" "schemaUids" I.calldata hbad)
  by_cases hshape : BatchShape I.calldata
  · obtain ⟨eas, heas⟩ := eas_of_fit hfit
    have heas' : (restrictImmutables contract imms).get? "_eas" = some (.address eas) := by
      rw [restrictImmutables_get? (by decide), heas]
    rcases multiRevokeBuildRequests rd (by simp) hchecks hshape hsize with
      ⟨hbad, hrev⟩ | ⟨hrows, aw, k, C, rd⟩
    · cases hdecode : decodeArrays? bytes32 I.calldata with
      | none => exact hrev.reEquivDecodingFailed hc hdispatch (multiRevokeDecode_none hdecode)
      | some values =>
          obtain ⟨schemas, rows, _, rfl, _, _, _⟩ := decodeArrays_first_facts hdecode
          rcases multiRevokeSourceBuild
            (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hvalue heas' hdecode hshape hsel with
            ⟨_, hsource⟩ | ⟨hvalid, _⟩
          · exact hrev.reEquivExecutionRevert hc hdispatch (multiRevokeDecode_some hdecode) hsource
          · exact False.elim (hbad hvalid)
    · obtain ⟨values, hdecode⟩ := hrows.decode_exists (.inl rfl) hchecks hsize hfour hsel
        (by decide +kernel)
      obtain ⟨schemas, rows, _, rfl, _, _, _⟩ := decodeArrays_first_facts hdecode
      rcases multiRevokeSourceBuild
        (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hvalue heas' hdecode hshape hsel with
        ⟨hbad, _⟩ | ⟨_, locals, hprefix, hlocalEas, hrequest⟩
      · exact False.elim (hbad hrows)
      · obtain ⟨aw, k, C, rd⟩ := multiRevokePrepare rd (by simp) hchecks hshape hrows
        exact multiRevokeExternalCorrect imms hfit hc hselector hdecode hshape hrows heas
          hprefix hlocalEas hrequest rd
  · have hrev := multiRevokeBadShape rd (by simp) hshape
    cases hdecode : decodeArrays? bytes32 I.calldata with
    | none => exact hrev.reEquivDecodingFailed hc hdispatch (multiRevokeDecode_none hdecode)
    | some values =>
        obtain ⟨schemas, rows, _, rfl, hslen, hrlen, _⟩ := decodeArrays_first_facts hdecode
        have hsource := multiRevokeSourceBadShape
          (schemas := schemas) (rows := rows)
          (imms := restrictImmutables contract imms)
          (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hvalue
          (by simpa only [hslen, hrlen, BatchShape] using hshape)
        exact hrev.reEquivExecutionRevert hc hdispatch (multiRevokeDecode_some hdecode) hsource

end Benchmarks.EAS.Attester

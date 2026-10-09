import Benchmarks.EAS.Attester.AttestReturnTrace
import Benchmarks.EAS.Attester.AttestSource

/-!
# Attester attest proof scaffold

Decode the two words at calldata offsets 4 and 36 (minimum size 68, signed-size guard).
Reach arm 143, decoder 2662, body 1884. Encode the request, its dynamic tuple offsets, and
the one-word input bytes; CALL at 2127 has zero value and a 32-byte output area. There is no
EXTCODESIZE guard. Match failed calls, returns shorter than 32 bytes, and successful UID
returns, including trailing return data. The callee may modify arbitrary accounts.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables
open attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attesterAttestBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterAttestSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hc := hcode.trans (deployedRuntime_eq_layout hfit)
  have hd := attesterAttestDispatch hselector
  have hsz := calldata_size_ge_of_selIs I attesterAttestSelBytes rfl hselector
  obtain ⟨k, C, rd⟩ := attesterAttestReachDecode (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hc hvalue hsize hselector
  by_cases hshort : I.calldata.size < 68
  · exact (attesterDecodeTwoWordsRevert rd (by simp) hsz hsize (.inl hshort))
      |>.reEquivDecodingFailed hc hd (attesterAttestDecodeShort hshort)
  by_cases hhi : 2 ^ 255 + 4 ≤ I.calldata.size
  · exact (attesterDecodeTwoWordsRevert rd (by simp) hsz hsize (.inr hhi))
      |>.reEquivDecodingFailed hc hd (attesterAttestDecodeHuge hhi)
  have hdec := attesterAttestDecode (by omega : 68 ≤ I.calldata.size)
    (by omega : I.calldata.size < 2 ^ 255 + 4)
  obtain ⟨k, C, rd⟩ := attesterAttestReachBody rd (by omega) (by omega) hsize
  obtain ⟨gasArg, aw, k, C, rd⟩ := attestReachCall rd
  obtain ⟨eas, heas⟩ := eas_of_fit hfit
  have heas' : (restrictImmutables contract imms).get? "_eas" = some (.address eas) := by
    rw [restrictImmutables_get? (by decide), heas]
  have hw : wordsOf imms "_eas" = UInt256.ofNat eas.val := wordsOf_of_get heas rfl
  have ht : eas = AccountAddress.ofUInt256 (UInt256.land solcAddrMask (wordsOf imms "_eas")) := by
    rw [hw, easWord_mask, accountAddress_roundtrip]
  have hcallDec : decode (immutableLayout.runtime attesterBytecode (wordsOf imms)) ⟨2127⟩ =
      some (.CALL, none) := by
    immutable_decode(immutableLayout, attesterBytecode, wordsOf imms, (⟨2127⟩ : UInt256),
      UInt8.ofNat 241, .CALL, none, immutableLayout_inBounds, immutableTemplate_size64)
  have hencode := attestRequest_encoding (calldataWord I.calldata 4) (calldataWord I.calldata 36)
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', rd'⟩ := RD.callDepthLimit rd hcallDec hdepth (by simp)
    have hbody := attestSourceFailure hvalue heas'
      (callNotMade_depthLimit (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hencode hdepth)
    exact (attestAfterCallFailure rd' (by simp)).reEquivExecutionRevert hc hd hdec hbody
  have hdepthlt : I.depth.val < 1024 := by
    have hbound := I.depth.isLt
    have hne : I.depth.val ≠ 1024 := fun h ↦ hdepth (Fin.ext h)
    omega
  obtain ⟨σ', z, out, Ain, callGas, k', C', ⟨g'', A', hθ⟩, rd', hout⟩ :=
    RD.call rd hcallDec hdepthlt (by simp)
  have hcall := callCoincides (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (callPerm := true) hdepth ht hencode (by simpa only [Bool.true_and] using hθ)
  cases z with
  | false =>
      have hbody := attestSourceFailure hvalue heas' hcall
      exact (attestAfterCallFailure rd' (by simp)).reEquivExecutionRevert hc hd hdec hbody
  | true =>
      simp only [callOutputLen32 hout] at rd'
      obtain ⟨aw', k'', C'', rd''⟩ := attestReachDecodeReturn rd'
      by_cases hshortout : out.size < 32
      · have hbody := attestSourceDecodeFailure hvalue heas' hcall (attestDecodeReturn_short
          hshortout)
        exact (attestDecodeReturnShort rd'' (by simp) hshortout).reEquivExecutionRevert hc hd hdec
            hbody
      have hsmall : ((attestMemory (calldataWord I.calldata 4) (calldataWord I.calldata
          36)).readWithPadding
          448 356).size ≤ Ethereum.EVM.maxReturnDataSizeByGas := by
        rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide)
          (by rw [attestMemory_size]; decide), ByteArray.size_extract, attestMemory_size]
        native_decide
      have hbound := Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hθ
          hsmall
      have hhiout : out.size < 2 ^ 255 := by omega
      have hlen : 32 ≤ out.size := by omega
      have hbody := attestSourceSuccess hvalue heas' hcall (attestDecodeReturn_ok hlen hhiout)
      obtain ⟨aw'', k''', C''', rd'''⟩ := attestDecodeReturn rd'' hlen hhiout
      have hret := attestReturnWord rd''' (by simp) (by rw [attestDecodedMemory_size]; decide)
        (attestDecodedMemory_freePtr _ _ _) (attestReturnPtr_bounds hhiout).1
      exact hret.reEquivExecutionGen hc hd hdec hbody rfl
        (.returned rfl (bytes32ReturnEncoding _))

end Benchmarks.EAS.Attester

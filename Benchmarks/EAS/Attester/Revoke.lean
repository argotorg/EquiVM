import Benchmarks.EAS.Attester.RevokeCallTrace

/-!
# Attester revoke proof scaffold

Decode two complete bytes32 words (minimum calldata size 68, signed-size guard).
Reach arm 176, decoder 2662, body 2187. Match the three-word request and EXTCODESIZE at
2366 before zero-value CALL 2381. Callee failure reverts; any successful return bytes are
ignored. Account-map effects come entirely from the callee.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables
open attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attesterRevokeBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hc := hcode.trans (deployedRuntime_eq_layout hfit)
  have hd := attesterRevokeDispatch hselector
  have hsz := calldata_size_ge_of_selIs I attesterRevokeSelBytes rfl hselector
  obtain ⟨k, C, rd⟩ := attesterRevokeReachDecode (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hc hvalue hsize hselector
  by_cases hshort : I.calldata.size < 68
  · exact (attesterDecodeTwoWordsRevert rd (by simp) hsz hsize (.inl hshort))
      |>.reEquivDecodingFailed hc hd (attesterRevokeDecodeShort hshort)
  by_cases hhi : 2 ^ 255 + 4 ≤ I.calldata.size
  · exact (attesterDecodeTwoWordsRevert rd (by simp) hsz hsize (.inr hhi))
      |>.reEquivDecodingFailed hc hd (attesterRevokeDecodeHuge hhi)
  have hdec := attesterRevokeDecode (by omega : 68 ≤ I.calldata.size)
    (by omega : I.calldata.size < 2 ^ 255 + 4)
  obtain ⟨k, C, rd⟩ := attesterRevokeReachBody rd (by omega) (by omega) hsize
  obtain ⟨aw, k, C, rd⟩ := revokePrepare rd
  obtain ⟨eas, heas⟩ := eas_of_fit hfit
  have heas' : (restrictImmutables contract imms).get? "_eas" = some (.address eas) := by
    rw [restrictImmutables_get? (by decide), heas]
  have hw : wordsOf imms "_eas" = UInt256.ofNat eas.val := wordsOf_of_get heas rfl
  have ht : eas = AccountAddress.ofUInt256 (UInt256.land solcAddrMask (wordsOf imms "_eas")) := by
    rw [hw, easWord_mask, accountAddress_roundtrip]
  have hguard := evalExpr_codeGuard_of_accounts_eq (σ := σ)
    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl ht
    (revokeSourceReceiver (imms := restrictImmutables contract imms)
      (schema := calldataWord I.calldata 4) (uid := calldataWord I.calldata 36))
  by_cases hzero : extCodeSizeWord σ (UInt256.land solcAddrMask (wordsOf imms "_eas")) = ⟨0⟩
  · have hguard' : evalExpr? config
        (revokeCallFrame (restrictImmutables contract imms) eas
          (calldataWord I.calldata 4) (calldataWord I.calldata 36))
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.extCodeSize (.var "eas")) (.intLit 0)) = .ok (.bool false) := by
      simpa only [hzero] using hguard
    have hbody := revokeSourceNoCode hvalue heas' hguard'
    exact (revokeNoCode rd hzero).reEquivExecutionRevert hc hd hdec hbody
  have hpos : 0 < (extCodeSizeWord σ
      (UInt256.land solcAddrMask (wordsOf imms "_eas"))).toNat := by
    exact Nat.pos_of_ne_zero (fun hz ↦ hzero (uint256_toNat_eq_zero hz))
  simp only [hpos, decide_true] at hguard
  obtain ⟨gasArg, aw, k, C, rd⟩ := revokeReachCall rd hzero
  have hcallDec : decode (immutableLayout.runtime attesterBytecode (wordsOf imms)) ⟨2381⟩ =
      some (.CALL, none) := by
    immutable_decode(immutableLayout, attesterBytecode, wordsOf imms, (⟨2381⟩ : UInt256),
      UInt8.ofNat 241, .CALL, none, immutableLayout_inBounds, immutableTemplate_size64)
  have hencode := revokeRequest_encoding (calldataWord I.calldata 4) (calldataWord I.calldata 36)
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', rd'⟩ := RD.callDepthLimit rd hcallDec hdepth (by simp)
    have hbody := revokeSourceFailure hvalue heas' hguard
      (callNotMade_depthLimit (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hencode hdepth)
    exact (revokeAfterCallFailure rd' (by simp)).reEquivExecutionRevert hc hd hdec hbody
  have hdepthlt : I.depth.val < 1024 := by
    have hbound := I.depth.isLt
    have hne : I.depth.val ≠ 1024 := fun h ↦ hdepth (Fin.ext h)
    omega
  obtain ⟨σ', z, out, Ain, callGas, k', C', ⟨g'', A', hθ⟩, rd', _hout⟩ :=
    RD.call rd hcallDec hdepthlt (by simp)
  have hcall := callCoincides (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (callPerm := true) hdepth ht hencode (by simpa only [Bool.true_and] using hθ)
  cases z with
  | false =>
      have hbody := revokeSourceFailure hvalue heas' hguard hcall
      exact (revokeAfterCallFailure rd' (by simp)).reEquivExecutionRevert hc hd hdec hbody
  | true =>
      have hbody := revokeSourceSuccess hvalue heas' hguard hcall
      exact (revokeAfterCallSuccess rd').reEquivExecutionGen hc hd hdec hbody rfl
        (.fallthrough rfl rfl (by native_decide))

end Benchmarks.EAS.Attester

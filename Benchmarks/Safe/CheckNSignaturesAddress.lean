import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.SignatureAddressDecoder
import Benchmarks.Safe.SignatureCallerSource
import Benchmarks.Safe.SignatureDecodedMemory
import Benchmarks.Safe.CheckNSignaturesTrace
import Benchmarks.Safe.Blocks.Runtime_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeChecknsignaturesAddressBytes32BytesUint256BodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checknsignaturesAddressBytes32BytesUint256Transition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x1f 0xca 0xc7 0xf3 ⟨0x1fcac7f3⟩
    hdispatch checknsignaturesAddressBytes32BytesUint256SelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x1fcac7f3⟩ 2 ⟨697⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_697_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hr := safeRuntime_block_705 (by simp [safeRuntime_block_697_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have h₁ := safeRuntime_block_697_taken (by simp) (by rw [hvalue]; decide)
    (by jump_dest) hentry
  have hdecode := safeRuntime_block_708 (by simp) (by jump_dest) h₁
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata (signatureAddressNames true) (signatureAddressTypes true)
      I.calldata with
  | none =>
    have hr : RDrev safeBytecode (.ofUInt256 g) evm := by
      obtain hr | ⟨len, aw', k', C', hh, hs, hc, hoff, hw, hn, hin, hr⟩ :=
        safeDecodeSignatureAddressEvidence true hdecode hlong hsize (by simp) (by jump_dest)
      · exact hr
      have hd := decodeSignatureAddressValid true hh hs hc hoff hw (by omega) hin
      rw [hdec] at hd
      cases hd
    exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
    obtain ⟨len, hh, hs, hc, hoff, hw, hn, hin, rfl⟩ :=
      decodeSignatureAddressEvidence true hlong hdec
    let payload := I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
      (4 + (calldataWord I.calldata 68).toNat + 32 + len)
    let p : SignatureInput := ⟨AccountAddress.ofUInt256 (calldataWord I.calldata 4),
      calldataWord I.calldata 36, payload, calldataWord I.calldata 100⟩
    have hlen : payload.size = len := by
      dsimp only [payload]
      rw [ByteArray.size_extract]; omega
    have hdec' : decodeCalldataWithMode config.abiDecodeMode
        (checknsignaturesAddressBytes32BytesUint256Transition.params.map Param.name)
        (transitionSignature checknsignaturesAddressBytes32BytesUint256Transition).paramTypes
        I.calldata =
          some (signatureAddressArgs true p.executor p.hash p.signatures p.required) := by
      change decodeCalldata (signatureAddressNames true) (signatureAddressTypes true)
        I.calldata = some (signatureAddressArgs true p.executor p.hash p.signatures p.required)
      simpa only [p, accountAddress_ofUInt256_eq_ofNat_toNat] using hdec
    by_cases hvalid : len ≤ 2 ^ 64 - 192
    · obtain ⟨aw', k', C', h₂⟩ := safeDecodeSignatureAddressValid true hdecode hh hs hc hoff hw
        hvalid hin (by simp) (by jump_dest)
      have h₃ := safeRuntime_block_723 (by simp [signatureDecodedStack]) (by jump_dest) h₂
      have hsmall : p.signatures.size ≤ 2 ^ 64 - 192 := by
        change payload.size ≤ _
        rw [hlen]; exact hvalid
      obtain ⟨hr, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw'', out, k'', C'', hbody,
          hee, hacc, hworld, hstop, _⟩ :=
        safeCheckNSignaturesTrace p evm h₃ rfl rfl rfl rfl (BytesMemory.decoded payload)
          (memoryBytesDecoded_free payload) (memoryBytesDecoded_zero payload) (by decide)
          (memoryBytesInitialEnd_contains payload.size)
          (lt_trans (memoryBytesInitialEnd_bound hsmall) (by decide)) (by omega)
          (by simp) (by jump_dest)
      · have hsource := ExecFuncBody.execBlockRevert
          (safeCheckNSignaturesAddressSource (p := p) (evm := evm) hvalue hsmall hbody)
        exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec'
            hsource (.revert hΞ rfl)
      · have hr := safeRuntime_block_664 (by simp) hstop
        have hsource := ExecFuncBody.execBlockOK
          (safeCheckNSignaturesAddressSource (p := p) (evm := evm) hvalue hsmall hbody)
        exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hsource
            (.success hΞ rfl hacc.symm (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
    · have hr := safeDecodeSignatureAddressTooLarge true hdecode hlong hsize hw
        (by change len < 2 ^ 256; omega) hvalid (by simp) (by jump_dest)
      exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec'
          (signatureCallerInvalid (payload := payload)
            (by rw [hlen]; exact hvalid)
            (by simp [signatureAddressArgs, p, Std.HashMap.getElem?_insert,
              Std.HashMap.getElem_insert])) (.revert hΞ rfl)

/-- Refinement obligation for `checkNSignatures`
(`checknsignaturesAddressBytes32BytesUint256Transition`). -/
theorem safeChecknsignaturesAddressBytes32BytesUint256Refines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checknsignaturesAddressBytes32BytesUint256Transition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeChecknsignaturesAddressBytes32BytesUint256BodyCore hcode hsize hdispatch

end Benchmarks.Safe

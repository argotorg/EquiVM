import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.SignatureLegacyDecoder
import Benchmarks.Safe.ViaIR.SignatureLegacySource
import Benchmarks.Safe.ViaIR.SignatureDecodedMemory
import Benchmarks.Safe.ViaIR.CheckNSignaturesTrace

import Benchmarks.Safe.ViaIR.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
theorem safeChecknsignaturesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checknsignaturesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x12 0xfb 0x68 0xe0 ⟨0x12fb68e0⟩
    hdispatch checknsignaturesSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x12fb68e0⟩ 1 ⟨6581⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_6581_taken (by simp) hvalue (by jump_dest) hentry
    have hr := safeRuntime_block_111 (by simp) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have hdecode := safeRuntime_block_6581_fallthrough (by simp) hvalue hentry
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata (signatureLegacyNames true) (signatureLegacyTypes true)
      I.calldata with
  | none =>
    have hr : RDrev fork safeBytecode (.ofUInt256 g) evm := by
      obtain hr | ⟨dataLen, len, aw', k', C', hh, hs, hdo, hdw, hdn, hdi, hso, hw, hn, hin, hr⟩ :=
        safeDecodeSignatureLegacyEvidence true hdecode hlong hsize (by simp)
      · exact hr
      have hd := decodeSignatureLegacyValid true hh hs hdo hdw hdn hdi hso hw (by omega) hin
      rw [hdec] at hd
      cases hd
    exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
    obtain ⟨dataLen, len, hh, hs, hdo, hdw, hdn, hdi, hso, hw, hn, hin, rfl⟩ :=
      decodeSignatureLegacyEvidence true hlong hdec
    let data := I.calldata.extract (4 + (calldataWord I.calldata 36).toNat + 32)
      (4 + (calldataWord I.calldata 36).toNat + 32 + dataLen)
    let payload := I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
      (4 + (calldataWord I.calldata 68).toNat + 32 + len)
    let p : SignatureInput :=
      ⟨I.source, calldataWord I.calldata 4, payload, calldataWord I.calldata 100⟩
    have hlen : payload.size = len := by
      dsimp only [payload]
      rw [ByteArray.size_extract]; omega
    have hdec' : config.externalABI.decodeCalldata?
        (checknsignaturesTransition.params.map Param.name)
        (transitionSignature checknsignaturesTransition).paramTypes
        I.calldata = some (signatureLegacyArgs true p.hash data p.signatures p.required) := by
      change decodeCalldata (signatureLegacyNames true) (signatureLegacyTypes true)
        I.calldata = some (signatureLegacyArgs true p.hash data p.signatures p.required)
      exact hdec
    by_cases hvalid : len ≤ 2 ^ 64 - 192
    · obtain ⟨aw', k', C', h₂⟩ := safeDecodeSignatureLegacyValid true hdecode
        hh hs hdo hdw hdn hdi hso hw hvalid hin (by simp)
      have hsmall : p.signatures.size ≤ 2 ^ 64 - 192 := by
        change payload.size ≤ _
        rw [hlen]; exact hvalid
      obtain ⟨hr, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw'', out, k'', C'', hbody,
          hee, hacc, hworld, hstop, _⟩ :=
        safeCheckNSignaturesTrace p evm h₂ (accountAddress_roundtrip I.source).symm rfl rfl rfl
          (BytesMemory.decoded payload)
          (memoryBytesDecoded_free payload) (memoryBytesDecoded_zero payload) (by decide)
          (memoryBytesInitialEnd_contains payload.size)
          (lt_trans (memoryBytesInitialEnd_bound hsmall) (by decide)) (by omega)
          (by simp) (by jump_dest)
      · have hsource := ExecFuncBody.execBlockRevert
          (safeCheckNSignaturesLegacySource (p := p) (evm := evm) data hvalue rfl hsmall hbody)
        exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec'
            hsource (.revert hΞ rfl)
      · have hr := safeRuntime_block_109 (by simp) hstop
        have hsource := ExecFuncBody.execBlockOK
          (safeCheckNSignaturesLegacySource (p := p) (evm := evm) data hvalue rfl hsmall hbody)
        exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hsource
            (.success hΞ rfl hacc.symm (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
    · have hr := safeDecodeSignatureLegacyTooLarge true hdecode hlong hsize hw
        (by change len < 2 ^ 256; omega) hvalid (by simp)
      exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec'
          (signatureCallerInvalid (payload := payload)
            (by rw [hlen]; exact hvalid)
            (by simp [signatureLegacyArgs, p, Std.HashMap.getElem?_insert,
              Std.HashMap.getElem_insert])) (.revert hΞ rfl)

/-- Refinement obligation for `checkNSignatures`
(`checknsignaturesTransition`). -/
theorem safeChecknsignaturesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checknsignaturesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeChecknsignaturesBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

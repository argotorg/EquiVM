import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.SignatureLegacyDecoder
import Benchmarks.Safe.SignatureLegacySource
import Benchmarks.Safe.SignatureDecodedMemory
import Benchmarks.Safe.CheckSignaturesTrace
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_009
import Benchmarks.Safe.Blocks.Runtime_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeChecksignaturesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checksignaturesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x93 0x4f 0x3a 0x11 ⟨0x934f3a11⟩
    hdispatch checksignaturesSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x934f3a11⟩ 2 ⟨1123⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_1123_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hr := safeRuntime_block_1131 (by simp [safeRuntime_block_1123_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have h₁ := safeRuntime_block_1123_taken (by simp) (by rw [hvalue]; decide)
    (by jump_dest) hentry
  have hdecode := safeRuntime_block_1134 (by simp) (by jump_dest) h₁
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata (signatureLegacyNames false) (signatureLegacyTypes false)
      I.calldata with
  | none =>
    have hr : RDrev safeBytecode (.ofUInt256 g) evm := by
      obtain hr | ⟨dataLen, len, aw', k', C', hh, hs, hdo, hdw, hdn, hdi, hso, hw, hn, hin, hr⟩ :=
        safeDecodeSignatureLegacyEvidence false hdecode hlong hsize (by simp) (by jump_dest)
      · exact hr
      have hd := decodeSignatureLegacyValid false hh hs hdo hdw hdn hdi hso hw (by omega) hin
      rw [hdec] at hd
      cases hd
    exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
    obtain ⟨dataLen, len, hh, hs, hdo, hdw, hdn, hdi, hso, hw, hn, hin, rfl⟩ :=
      decodeSignatureLegacyEvidence false hlong hdec
    let data := I.calldata.extract (4 + (calldataWord I.calldata 36).toNat + 32)
      (4 + (calldataWord I.calldata 36).toNat + 32 + dataLen)
    let payload := I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
      (4 + (calldataWord I.calldata 68).toNat + 32 + len)
    let p : SignatureCheckInput := ⟨I.source, calldataWord I.calldata 4, payload⟩
    have hlen : payload.size = len := by
      dsimp only [payload]
      rw [ByteArray.size_extract]; omega
    have hdec' : decodeCalldataWithMode config.abiDecodeMode
        (checksignaturesTransition.params.map Param.name)
        (transitionSignature checksignaturesTransition).paramTypes
        I.calldata = some (signatureLegacyArgs false p.hash data p.signatures ⟨0⟩) := by
      change decodeCalldata (signatureLegacyNames false) (signatureLegacyTypes false)
        I.calldata = some (signatureLegacyArgs false p.hash data p.signatures ⟨0⟩)
      simpa only [p, signatureLegacyArgs, Bool.false_eq_true, if_false] using hdec
    by_cases hvalid : len ≤ 2 ^ 64 - 192
    · obtain ⟨aw', k', C', h₂⟩ := safeDecodeSignatureLegacyValid false hdecode
        hh hs hdo hdw hdn hdi hso hw hvalid hin (by simp) (by jump_dest)
      have h₃ := safeRuntime_block_1149 (by simp [signatureLegacyDecodedStack]) (by jump_dest) h₂
      simp only [signatureLegacyDecodedStack, Bool.false_eq_true, if_false,
        List.cons_append, List.nil_append] at h₃
      have h₄ := safeRuntime_block_4272 (by simp) (by jump_dest) h₃
      have hsmall : p.signatures.size ≤ 2 ^ 64 - 192 := by
        change payload.size ≤ _
        rw [hlen]; exact hvalid
      obtain ⟨hr, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw'', out, k'', C'', hbody,
          hee, hacc, hworld, hstop, _⟩ :=
        safeCheckSignaturesTrace p evm h₄ (accountAddress_roundtrip I.source).symm rfl rfl rfl
          (BytesMemory.decoded payload)
          (memoryBytesDecoded_free payload) (memoryBytesDecoded_zero payload) (by decide)
          (memoryBytesInitialEnd_contains payload.size)
          (lt_trans (memoryBytesInitialEnd_bound hsmall) (by decide)) (by omega)
          (by simp) (by jump_dest)
      · have hsource := ExecFuncBody.execBlockRevert
          (safeCheckSignaturesLegacySource (p := p) (evm := evm) data hvalue rfl hsmall hbody)
        exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec'
            hsource (.revert hΞ rfl)
      · have hfinish := safeRuntime_block_4283 (by simp) (by jump_dest) hstop
        have hr := safeRuntime_block_664 (by simp [safeRuntime_block_4283_stack]) hfinish
        have hsource := ExecFuncBody.execBlockOK
          (safeCheckSignaturesLegacySource (p := p) (evm := evm) data hvalue rfl hsmall hbody)
        exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hsource
            (.success hΞ rfl hacc.symm (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
    · have hr := safeDecodeSignatureLegacyTooLarge false hdecode hlong hsize hw
        (by change len < 2 ^ 256; omega) hvalid (by simp) (by jump_dest)
      exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec'
          (signatureCallerInvalid (payload := payload)
            (by rw [hlen]; exact hvalid)
            (by simp [signatureLegacyArgs, p, Std.HashMap.getElem?_insert,
              Std.HashMap.getElem_insert])) (.revert hΞ rfl)

/-- Refinement obligation for `checkSignatures`
(`checksignaturesTransition`). -/
theorem safeChecksignaturesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checksignaturesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeChecksignaturesBodyCore hcode hsize hdispatch

end Benchmarks.Safe

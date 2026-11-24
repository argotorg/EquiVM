import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.SignatureAddressDecoder
import Benchmarks.Safe.ViaIR.SignatureCallerSource
import Benchmarks.Safe.ViaIR.SignatureDecodedMemory
import Benchmarks.Safe.ViaIR.CheckSignaturesTrace

import Benchmarks.Safe.ViaIR.Blocks.Runtime_006
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
theorem safeChecksignaturesAddressBytes32BytesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checksignaturesAddressBytes32BytesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xf8 0x55 0x43 0x8b ⟨0xf855438b⟩
    hdispatch checksignaturesAddressBytes32BytesSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xf855438b⟩ 28 ⟨899⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_899_taken (by simp) hvalue (by jump_dest) hentry
    have hr := safeRuntime_block_589 (by simp [safeRuntime_block_899_taken_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have hdecode := safeRuntime_block_899_fallthrough (by simp) hvalue hentry
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata (signatureAddressNames false) (signatureAddressTypes false)
      I.calldata with
  | none =>
    have hr : RDrev fork safeBytecode (.ofUInt256 g) evm := by
      obtain hr | ⟨len, aw', k', C', hh, hs, hc, hoff, hw, hn, hin, hr⟩ :=
        safeDecodeSignatureAddressEvidence false hdecode hlong hsize (by simp)
      · exact hr
      have hd := decodeSignatureAddressValid false hh hs hc hoff hw (by omega) hin
      rw [hdec] at hd
      cases hd
    exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
    obtain ⟨len, hh, hs, hc, hoff, hw, hn, hin, rfl⟩ :=
      decodeSignatureAddressEvidence false hlong hdec
    let payload := I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
      (4 + (calldataWord I.calldata 68).toNat + 32 + len)
    let p : SignatureCheckInput := ⟨AccountAddress.ofUInt256 (calldataWord I.calldata 4),
      calldataWord I.calldata 36, payload⟩
    have hlen : payload.size = len := by
      dsimp only [payload]
      rw [ByteArray.size_extract]; omega
    have hdec' : config.externalABI.decodeCalldata?
        (checksignaturesAddressBytes32BytesTransition.params.map Param.name)
        (transitionSignature checksignaturesAddressBytes32BytesTransition).paramTypes
        I.calldata = some (signatureAddressArgs false p.executor p.hash p.signatures ⟨0⟩) := by
      change decodeCalldata (signatureAddressNames false) (signatureAddressTypes false)
        I.calldata = some (signatureAddressArgs false p.executor p.hash p.signatures ⟨0⟩)
      simpa only [p, accountAddress_ofUInt256_eq_ofNat_toNat, signatureAddressArgs,
        Bool.false_eq_true, if_false] using hdec
    by_cases hvalid : len ≤ 2 ^ 64 - 192
    · obtain ⟨aw', k', C', h₂⟩ := safeDecodeSignatureAddressValid false hdecode hh hs hc hoff hw
        hvalid hin (by simp)
      have hsmall : p.signatures.size ≤ 2 ^ 64 - 192 := by
        change payload.size ≤ _
        rw [hlen]; exact hvalid
      obtain ⟨hr, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw'', out, k'', C'', hbody,
          hee, hacc, hworld, hstop, _⟩ :=
        safeCheckSignaturesTrace p evm h₂ rfl rfl rfl rfl (BytesMemory.decoded payload)
          (memoryBytesDecoded_free payload) (memoryBytesDecoded_zero payload) (by decide)
          (memoryBytesInitialEnd_contains payload.size)
          (lt_trans (memoryBytesInitialEnd_bound hsmall) (by decide)) (by omega)
          (by simp) (by jump_dest)
      · have hsource := ExecFuncBody.execBlockRevert
          (safeCheckSignaturesAddressSource (p := p) (evm := evm) hvalue hsmall hbody)
        exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec'
            hsource (.revert hΞ rfl)
      · have hr := safeRuntime_block_970 (by simp) hstop
        simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          byteArray_readWithPadding_zero] at hr
        have hsource := ExecFuncBody.execBlockOK
          (safeCheckSignaturesAddressSource (p := p) (evm := evm) hvalue hsmall hbody)
        exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hsource
            (.success hΞ rfl hacc.symm (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
    · have hr := safeDecodeSignatureAddressTooLarge false hdecode hlong hsize hw
        (by change len < 2 ^ 256; omega) hvalid (by simp)
      exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec'
          (signatureCallerInvalid (payload := payload)
            (by rw [hlen]; exact hvalid)
            (by simp [signatureAddressArgs, p, Std.HashMap.getElem?_insert,
              Std.HashMap.getElem_insert])) (.revert hΞ rfl)

/-- Refinement obligation for `checkSignatures`
(`checksignaturesAddressBytes32BytesTransition`). -/
theorem safeChecksignaturesAddressBytes32BytesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checksignaturesAddressBytes32BytesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeChecksignaturesAddressBytes32BytesBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

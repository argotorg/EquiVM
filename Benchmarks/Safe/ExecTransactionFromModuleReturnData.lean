import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.ModuleArgsDecoder
import Benchmarks.Safe.ModuleCalldata
import Benchmarks.Safe.ModuleReturnDataTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeExectransactionfrommodulereturndataBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some exectransactionfrommodulereturndataTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x52 0x29 0x07 0x3f ⟨0x5229073f⟩
    hdispatch exectransactionfrommodulereturndataSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x5229073f⟩ 3 ⟨842⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_842_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hr := safeRuntime_block_850 (by simp [safeRuntime_block_842_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have h₁ := safeRuntime_block_842_taken (by simp) (by rw [hvalue]; decide)
    (by jump_dest) hentry
  have hdecode := safeRuntime_block_853 (by simp) (by jump_dest) h₁
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata ["to", "value", "data", "operation"] moduleCalldataTypes
      I.calldata with
  | none =>
    have hr : RDrev safeBytecode (.ofUInt256 g) evm := by
      rcases safeDecodeModuleArgsEvidence hdecode hlong hsize (by simp) (by jump_dest) with
        hr | ⟨len, aw', k', C', hh, hs, hc, hoff, hw, hn, hin, ho, hr⟩
      · exact hr
      have hd := decodeModuleCalldataValid hh hs hc hoff hw (by omega) hin (by omega)
      rw [hdec] at hd
      cases hd
    exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
    obtain ⟨len, hh, hs, hc, hoff, hw, hn, hin, hop, rfl⟩ :=
      decodeModuleCalldataEvidence hlong hdec
    let payload := I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
      (4 + (calldataWord I.calldata 68).toNat + 32 + len)
    have hlen : payload.size = len := by
      dsimp only [payload]
      rw [ByteArray.size_extract]; omega
    have hdec' : decodeCalldataWithMode config.abiDecodeMode
        (exectransactionfrommodulereturndataTransition.params.map Param.name)
        (transitionSignature exectransactionfrommodulereturndataTransition).paramTypes I.calldata =
        some (moduleArgs (AccountAddress.ofUInt256 (calldataWord I.calldata 4))
          (calldataWord I.calldata 36) payload (calldataWord I.calldata 100)) := by
      simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using hdec
    by_cases hvalid : len ≤ 2 ^ 64 - 192 ∧ (calldataWord I.calldata 100).toNat < 2
    · obtain ⟨aw', k', C', h₂⟩ := safeDecodeModuleArgsValid hdecode hh hs hc hoff hw
        hvalid.1 hin hvalid.2 (by simp) (by jump_dest)
      have h₃ := safeRuntime_block_868 (by simp) (by jump_dest) h₂
      rcases safeModuleReturnDataTrace evm payload h₃ rfl rfl rfl hvalue
        (by rw [hlen]; exact hvalid.1) hvalid.2 (by simp) with
        ⟨hr, hbody⟩ | ⟨hr, hbody⟩ | ⟨frame, evm', σ', z, out, hbody, he, ha, hw', hr⟩
      · exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hbody (.revert hΞ rfl)
      · exact RDstatic.reEquivElim hcode hr fun hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hbody (.staticHalt hΞ rfl)
      · exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hbody
            (.success hΞ rfl ha.symm (.abi (.returned rfl (boolBytesReturnEncoding z out))))
    · have hr : RDrev safeBytecode (.ofUInt256 g) evm := by
        rcases safeDecodeModuleArgsEvidence hdecode hlong hsize (by simp) (by jump_dest) with
          hr | ⟨len', aw', k', C', hh', hs', hc', hoff', hw', hn', hin', ho', hr⟩
        · exact hr
        have hsame : len = len' := by
          have ht := congrArg UInt256.toNat (hw.symm.trans hw')
          rw [ulit_toNat' _ (by change len < 2 ^ 256; omega),
            ulit_toNat' _ (by change len' < 2 ^ 256; omega)] at ht
          exact ht
        exact (hvalid ⟨hsame.symm ▸ hn', ho'⟩).elim
      have hbad : ¬payload.size ≤ 2 ^ 64 - 192 ∨
          ¬(calldataWord I.calldata 100).toNat < 2 := by
        rw [hlen]
        exact not_and_or.mp hvalid
      exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec' (safeModuleInvalidChecks hbad) (.revert hΞ rfl)

/-- Refinement obligation for `execTransactionFromModuleReturnData`
(`exectransactionfrommodulereturndataTransition`). -/
theorem safeExectransactionfrommodulereturndataRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some exectransactionfrommodulereturndataTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeExectransactionfrommodulereturndataBodyCore hcode hsize hdispatch

end Benchmarks.Safe

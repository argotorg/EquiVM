import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.ModuleArgsDecoder
import Benchmarks.Safe.ModuleCalldata
import Benchmarks.Safe.ModuleTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeExectransactionfrommoduleBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some exectransactionfrommoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x46 0x87 0x21 0xa7 ⟨0x468721a7⟩
    hdispatch exectransactionfrommoduleSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x468721a7⟩ 2 ⟨811⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_811_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hr := safeRuntime_block_819 (by simp [safeRuntime_block_811_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have h₁ := safeRuntime_block_811_taken (by simp) (by rw [hvalue]; decide)
    (by jump_dest) hentry
  have hdecode := safeRuntime_block_822 (by simp) (by jump_dest) h₁
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
        (exectransactionfrommoduleTransition.params.map Param.name)
        (transitionSignature exectransactionfrommoduleTransition).paramTypes I.calldata =
        some (moduleArgs (AccountAddress.ofUInt256 (calldataWord I.calldata 4))
          (calldataWord I.calldata 36) payload (calldataWord I.calldata 100)) := by
      simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using hdec
    by_cases hvalid : len ≤ 2 ^ 64 - 192 ∧ (calldataWord I.calldata 100).toNat < 2
    · obtain ⟨aw', k', C', h₂⟩ := safeDecodeModuleArgsValid hdecode hh hs hc hoff hw
        hvalid.1 hin hvalid.2 (by simp) (by jump_dest)
      have h₃ := safeRuntime_block_837 (by simp) (by jump_dest) h₂
      rcases safeModuleTrace evm payload h₃ rfl rfl rfl hvalue
        (by rw [hlen]; exact hvalid.1) hvalid.2 (by simp) with
        ⟨hr, hbody⟩ | ⟨hr, hbody⟩ | ⟨frame, evm', σ', z, hbody, he, ha, hw', hr⟩
      · exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hbody (.revert hΞ rfl)
      · exact RDstatic.reEquivElim hcode hr fun hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hbody (.staticHalt hΞ rfl)
      · exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hbody
            (.success hΞ rfl ha.symm (.abi (returnEquiv_of_encode (boolReturnEncoding z))))
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
        reEquivSelectorExecution hdispatch hdec' (safeModuleInvalid hbad) (.revert hΞ rfl)

/-- Refinement obligation for `execTransactionFromModule`
(`exectransactionfrommoduleTransition`). -/
theorem safeExectransactionfrommoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some exectransactionfrommoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeExectransactionfrommoduleBodyCore hcode hsize hdispatch

end Benchmarks.Safe

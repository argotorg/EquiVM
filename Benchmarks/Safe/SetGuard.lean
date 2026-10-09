import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.GuardFinish
import Benchmarks.Safe.Blocks.Runtime_011
import Benchmarks.Safe.Blocks.Runtime_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeSetguardBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe1 0x9a 0x9d 0xd9 ⟨0xe19a9dd9⟩
    hdispatch setguardSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe19a9dd9⟩ 0 ⟨1439⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hv : I.weiValue = ⟨0⟩
  · have h₁ := safeRuntime_block_1439_taken (by simp)
      (by rw [hv]; decide) (by jump_dest) hentry
    have hd := safeRuntime_block_1450 (by simp) (by jump_dest) h₁
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have hlencheck := solcDecodeLenCheckOk_4_32 hlen hbig hsize
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h₂⟩ := safeDecodeAddress hd (by simp) hlencheck hc (by jump_dest)
          have h₃ := safeRuntime_block_1465 (by simp) (by jump_dest) h₂
          have h₄ := safeRuntime_block_5998 (by simp) (by jump_dest) h₃
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (setguardTransition.params.map Param.name)
              (transitionSignature setguardTransition).paramTypes I.calldata =
              some (guardArgs .transaction (calldataWord I.calldata 4)) :=
            decodeCalldata_address_ok hlen hbig hc
          by_cases ha : I.source = I.codeOwner
          · obtain ⟨_, _, h₅⟩ := safeAuthorizedTrace h₄ (by simp) ha (by jump_dest)
            change RD safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨6006⟩
              [calldataWord I.calldata 4, ⟨664⟩, selWord I] _ _ _ σ _ _ at h₅
            by_cases hz : calldataWord I.calldata 4 = ⟨0⟩
            · obtain ⟨_, _, he⟩ := safeGuardZeroTrace (hz ▸ h₅) (by simp)
              apply safeGuardFinish hcode hdispatch (hz ▸ hdec) (by decide) hv ha
                (by simp [guardArgs, guardName, guardField])
                (by simp [guardArgs, guardName, guardField]) rfl rfl
                (safeGuardCheckZero (kind := .transaction) _) he (by simp)
            · obtain ⟨_, _, _, _, hcallpc⟩ := safeGuardCallSetup h₅ (by simp) hc hz
              obtain ⟨evm', σ', z, out, _, _, _, hcall, hee, hacc, hr, hout⟩ :=
                safeGuardCall hcallpc (by simp)
              cases z with
              | false =>
                  have hrev := safeGuardCallFailureTrace hr (by simp)
                  have hbody := safeGuardSourceRevert (kind := .transaction) hv ha
                    (safeGuardCheckFailed (kind := .transaction) hc hz hcall)
                  exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              | true =>
                  obtain ⟨_, _, _, hdecode⟩ := safeGuardReturnStart hr (by simp)
                  have hb : out.size < 2 ^ 255 := lt_trans hout (by decide)
                  by_cases hl : 32 ≤ out.size
                  · have hbool := safeGuardDecodeLong hl hb
                    by_cases hwz : calldataWord out 0 = ⟨0⟩
                    · have hrev := safeGuardReturnFalse hdecode (by simp) hl hb hwz
                      have hbody := safeGuardSourceRevert (kind := .transaction) hv ha
                        (safeGuardCheckFalse (kind := .transaction) hc hz hcall
                          (by simpa only [if_pos hwz] using hbool))
                      exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                    · by_cases hwo : calldataWord out 0 = ⟨1⟩
                      · obtain ⟨_, _, _, he⟩ := safeGuardReturnTrue hdecode (by simp) hl hb hwo
                        exact safeGuardFinish hcode hdispatch hdec hc hv ha
                          (by simp [guardArgs, guardName, guardField, Std.HashMap.getElem_insert])
                          (by simp [guardArgs, guardName, guardField]) hee hacc
                          (safeGuardCheckTrue (kind := .transaction) hc hz hcall
                            (by simpa only [if_neg hwz, if_pos hwo] using hbool)) he (by simp)
                      · have hrev := safeBoolDecoderNoncanon hdecode (by simp) hl hb
                          (guardDecodedMemory_word (kind := .transaction) out hl) hwz hwo
                        have hbody := safeGuardSourceRevert (kind := .transaction) hv ha
                          (safeGuardCheckInvalid (kind := .transaction) hc hz hcall
                            (by simpa only [if_neg hwz, if_neg hwo] using hbool))
                        exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                          reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                  · have hrev := safeBoolDecoderShort hdecode (by simp) (by omega)
                    have hbody := safeGuardSourceRevert (kind := .transaction) hv ha
                      (safeGuardCheckInvalid (kind := .transaction) hc hz hcall
                        (safeGuardDecodeShort (by omega)))
                    exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                      reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · have hrev := safeUnauthorizedTrace h₄ (by simp [safeRuntime_block_5998_stack]) ha
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeGuardSourceUnauthorized (kind := .transaction) locals hv ha
        · have hrev := safeDecodeAddressNoncanon hd (by simp) hlencheck hc
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hc) hrev
      · have hrev := safeDecodeAddressRevert hd (by simp)
          (solcDecodeLenCheckShort_4_32 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressRevert hd (by simp)
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have hr := safeRuntime_block_1439_fallthrough (by simp) (isZero_eq_zero_of_ne hv) hentry
    have hrev := safeRuntime_block_1447 (by simp [safeRuntime_block_1439_fallthrough_stack]) hr
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hv

/-- Refinement obligation for `setGuard` (`setguardTransition`). -/
theorem safeSetguardRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeSetguardBodyCore hcode hsize hdispatch

end Benchmarks.Safe

import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.GuardFinish
import Benchmarks.Safe.ViaIR.Blocks.Runtime_008
import Benchmarks.Safe.ViaIR.Blocks.Runtime_009

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeSetguardBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe1 0x9a 0x9d 0xd9 ⟨0xe19a9dd9⟩
    hdispatch setguardSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe19a9dd9⟩ 23 ⟨1425⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hv : I.weiValue = ⟨0⟩
  · have h₁ := safeRuntime_block_1425_fallthrough (by simp) hv hentry
    simp only [safeRuntime_block_1425_fallthrough_stack] at h₁
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h1444 := safeRuntime_block_1432_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h₁
        have hd := safeRuntime_block_1444 (by simp) (by jump_dest) h1444
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h₂⟩ := safeDecodeAddress hd (by simp) hc (by jump_dest)
          have h₄ := safeRuntime_block_1451 (by simp) (by jump_dest) h₂
          have hdec : config.externalABI.decodeCalldata?
              (setguardTransition.params.map Param.name)
              (transitionSignature setguardTransition).paramTypes I.calldata =
              some (guardArgs .transaction (calldataWord I.calldata 4)) :=
            decodeCalldata_address_ok hlen hbig hc
          by_cases ha : I.source = I.codeOwner
          · obtain ⟨_, _, h₅⟩ := safeAuthorizedTrace h₄ (by simp) ha (by jump_dest)
            change RD fork safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨1459⟩
              [calldataWord I.calldata 4, ⟨0⟩] _ _ _ σ _ _ at h₅
            by_cases hz : calldataWord I.calldata 4 = ⟨0⟩
            · obtain ⟨_, _, he⟩ := safeGuardZeroTrace (hz ▸ h₅) (by simp)
              apply safeGuardFinish hcode hdispatch (hz ▸ hdec) (by decide) hv ha
                (by simp [guardArgs, guardName])
                (by simp [guardArgs, guardName]) rfl rfl
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
                  obtain ⟨_, _, _, hdecode⟩ :=
                    safeGuardReturnStart hr (by simp) (lt_trans hout (by decide))
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
                          (by simp [guardArgs, guardName, Std.HashMap.getElem_insert])
                          (by simp [guardArgs, guardName]) hee hacc
                          (safeGuardCheckTrue (kind := .transaction) hc hz hcall
                            (by simpa only [if_neg hwz, if_pos hwo] using hbool)) he (by simp)
                      · have hrev := safeBoolDecoderNoncanon hdecode (by simp) (by omega) (by omega)
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
          · have hrev := safeUnauthorizedTrace h₄ (by simp [safeRuntime_block_1451_stack]) ha
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeGuardSourceUnauthorized (kind := .transaction) locals hv ha
        · have hrev := safeDecodeAddressNoncanon hd (by simp) hc
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hc) hrev
      · have h589 := safeRuntime_block_1432_taken (by simp)
          (by rw [hlenWord]
              change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
              rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]; decide)
          (by jump_dest) h₁
        have hrev := safeRuntime_block_589 (by simp) h589
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have h589 := safeRuntime_block_1432_taken (by simp)
        (by rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]; decide)
        (by jump_dest) h₁
      have hrev := safeRuntime_block_589 (by simp) h589
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have h589 := safeRuntime_block_1425_taken (by simp) hv (by jump_dest) hentry
    have hrev := safeRuntime_block_589 (by simp) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hv

/-- Refinement obligation for `setGuard` (`setguardTransition`). -/
theorem safeSetguardRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeSetguardBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

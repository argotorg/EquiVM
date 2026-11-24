import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.ModuleGuardFinish
import Benchmarks.Safe.ViaIR.Blocks.Runtime_010
import Benchmarks.Safe.ViaIR.Blocks.Runtime_009

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeSetmoduleguardBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setmoduleguardTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe0 0x68 0xdf 0x37 ⟨0xe068df37⟩
    hdispatch setmoduleguardSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe068df37⟩ 22 ⟨1716⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hv : I.weiValue = ⟨0⟩
  · have h₁ := safeRuntime_block_1716_fallthrough (by simp) hv hentry
    simp only [safeRuntime_block_1716_fallthrough_stack] at h₁
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h1735 := safeRuntime_block_1723_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h₁
        have hd := safeRuntime_block_1735 (by simp) (by jump_dest) h1735
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h₂⟩ := safeDecodeAddress hd (by simp) hc (by jump_dest)
          have h₄ := safeRuntime_block_1742 (by simp) (by jump_dest) h₂
          have hdec : config.externalABI.decodeCalldata?
              (setmoduleguardTransition.params.map Param.name)
              (transitionSignature setmoduleguardTransition).paramTypes I.calldata =
              some (guardArgs .moduleGuard (calldataWord I.calldata 4)) :=
            decodeCalldata_address_ok hlen hbig hc
          by_cases ha : I.source = I.codeOwner
          · obtain ⟨_, _, h₅⟩ := safeAuthorizedTrace h₄ (by simp) ha (by jump_dest)
            change RD fork safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨1750⟩
              [calldataWord I.calldata 4, ⟨0⟩] _ _ _ σ _ _ at h₅
            by_cases hz : calldataWord I.calldata 4 = ⟨0⟩
            · obtain ⟨_, _, he⟩ := safeModuleGuardZeroTrace (hz ▸ h₅) (by simp)
              apply safeModuleGuardFinish hcode hdispatch (hz ▸ hdec) (by decide) hv ha
                (by simp [guardArgs, guardName])
                (by simp [guardArgs, guardName]) rfl rfl
                (safeGuardCheckZero (kind := .moduleGuard) _) he (by simp)
            · obtain ⟨_, _, _, _, hcallpc⟩ := safeModuleGuardCallSetup h₅ (by simp) hc hz
              obtain ⟨evm', σ', z, out, _, _, _, hcall, hee, hacc, hr, hout⟩ :=
                safeModuleGuardCall hcallpc (by simp)
              cases z with
              | false =>
                  have hrev := safeModuleGuardCallFailureTrace hr (by simp)
                  have hbody := safeGuardSourceRevert (kind := .moduleGuard) hv ha
                    (safeGuardCheckFailed (kind := .moduleGuard) hc hz hcall)
                  exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              | true =>
                  obtain ⟨_, _, _, hdecode⟩ :=
                    safeModuleGuardReturnStart hr (by simp) (lt_trans hout (by decide))
                  have hb : out.size < 2 ^ 255 := lt_trans hout (by decide)
                  by_cases hl : 32 ≤ out.size
                  · have hbool := safeGuardDecodeLong hl hb
                    by_cases hwz : calldataWord out 0 = ⟨0⟩
                    · have hrev := safeModuleGuardReturnFalse hdecode (by simp) hl hb hwz
                      have hbody := safeGuardSourceRevert (kind := .moduleGuard) hv ha
                        (safeGuardCheckFalse (kind := .moduleGuard) hc hz hcall
                          (by simpa only [if_pos hwz] using hbool))
                      exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                    · by_cases hwo : calldataWord out 0 = ⟨1⟩
                      · obtain ⟨_, _, _, he⟩ :=
                          safeModuleGuardReturnTrue hdecode (by simp) hl hb hwo
                        exact safeModuleGuardFinish hcode hdispatch hdec hc hv ha
                          (by simp [guardArgs, guardName, Std.HashMap.getElem_insert])
                          (by simp [guardArgs, guardName]) hee hacc
                          (safeGuardCheckTrue (kind := .moduleGuard) hc hz hcall
                            (by simpa only [if_neg hwz, if_pos hwo] using hbool)) he (by simp)
                      · have hrev := safeBoolDecoderNoncanon hdecode (by simp) (by omega) (by omega)
                          (guardDecodedMemory_word (kind := .moduleGuard) out hl) hwz hwo
                        have hbody := safeGuardSourceRevert (kind := .moduleGuard) hv ha
                          (safeGuardCheckInvalid (kind := .moduleGuard) hc hz hcall
                            (by simpa only [if_neg hwz, if_neg hwo] using hbool))
                        exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                          reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                  · have hrev := safeBoolDecoderShort hdecode (by simp) (by omega)
                    have hbody := safeGuardSourceRevert (kind := .moduleGuard) hv ha
                      (safeGuardCheckInvalid (kind := .moduleGuard) hc hz hcall
                        (safeGuardDecodeShort (by omega)))
                    exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                      reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · have hrev := safeUnauthorizedTrace h₄ (by simp [safeRuntime_block_1742_stack]) ha
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeGuardSourceUnauthorized (kind := .moduleGuard) locals hv ha
        · have hrev := safeDecodeAddressNoncanon hd (by simp) hc
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hc) hrev
      · have h589 := safeRuntime_block_1723_taken (by simp)
          (by rw [hlenWord]
              change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
              rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]; decide)
          (by jump_dest) h₁
        have hrev := safeRuntime_block_589 (by simp) h589
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have h589 := safeRuntime_block_1723_taken (by simp)
        (by rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]; decide)
        (by jump_dest) h₁
      have hrev := safeRuntime_block_589 (by simp) h589
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have h589 := safeRuntime_block_1716_taken (by simp) hv (by jump_dest) hentry
    have hrev := safeRuntime_block_589 (by simp) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hv

/-- Refinement obligation for `setModuleGuard` (`setmoduleguardTransition`). -/
theorem safeSetmoduleguardRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setmoduleguardTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeSetmoduleguardBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

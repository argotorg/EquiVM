import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.AddOwnerTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeAddownerwiththresholdBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (haccount : σ.get? I.codeOwner ≠ none)
    (hdispatch : selectorDispatchMsg contract I.calldata = some addownerwiththresholdTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x0d 0x58 0x2f 0x13 ⟨0x0d582f13⟩
    hdispatch addownerwiththresholdSelectorBytes (by decide)
  obtain ⟨k, C, h6678⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x0d582f13⟩ 0 ⟨6678⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h6684 := safeRuntime_block_6678_fallthrough (by simp) hvalue h6678
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have h6696 := safeRuntime_block_6684_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_64 hlen hbig hsize) h6684
        have h6952 := safeRuntime_block_6696 (by simp) (by jump_dest) h6696
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h6703⟩ := safeDecodeAddress h6952 (by simp) hc (by jump_dest)
          have h9325 := safeRuntime_block_6703 (by simp) (by jump_dest) h6703
          have hdec : config.externalABI.decodeCalldata?
              (addownerwiththresholdTransition.params.map Param.name)
              (transitionSignature addownerwiththresholdTransition).paramTypes I.calldata =
              some (addOwnerArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36)) :=
            decodeCalldata_addr_uint256_ok hlen hbig hc
          by_cases hauth : I.source = I.codeOwner
          · obtain ⟨_, _, h6715⟩ := safeAuthorizedTrace h9325 (by simp) hauth (by jump_dest)
            have h9379 := safeRuntime_block_6715 (by simp) (by jump_dest) h6715
            let evm := initState σ σ₀ (.ofUInt256 g) A I
            let key := calldataWord I.calldata 4
            let threshold := calldataWord I.calldata 36
            change RD fork safeBytecode I (.ofUInt256 g) evm ⟨9379⟩
              [key, ⟨6724⟩, key, threshold, selWord I, ⟨0⟩] _ _ _ σ _ _ at h9379
            by_cases hv : validOwner σ I key
            · by_cases he : ownerLinkAt σ I key = ⟨0⟩
              · have he' : ownerLink evm key = ⟨0⟩ := by rw [ownerLink_eq_at]; exact he
                obtain ⟨mem₁, aw₁, k₁, C₁, hm₁, _, h6724⟩ := safeCanAddOwnerTrace h9379
                  (by simp) hc solcFreePtrMem_size solcFreePtrMem_read64 hv he (by jump_dest)
                cases hperm : I.perm with
                | false =>
                    have hstatic := safeAddOwnerTraceStatic h6724 (by simp) hperm
                    have hbody := safeAddOwnerSourceStatic (fork := fork) evm key threshold hc hvalue hauth hv
                      he' hperm
                    exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                      reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
                | true =>
                    let linked := addOwnerLinks evm key
                    let counted := addOwnerCountState linked
                    let σ₁ := addOwnerLinkAccounts σ I key
                    let σ₂ := addOwnerCountAccounts σ₁ I
                    have hlacc : linked.accountMap = σ₁ := safeAddOwnerLinkAccounts evm key
                    have hlenv : linked.executionEnv = I := safeAddOwnerLinksEnv evm key
                    have hcacc : counted.accountMap = σ₂ := by
                      rw [safeAddOwnerCountAccounts, hlacc, hlenv]
                    have hcenv : counted.executionEnv = I :=
                      (safeAddOwnerCountEnv linked).trans hlenv
                    have hlcount : ownerCount linked = solcSlotWordAt ⟨3⟩ σ₁ I := by
                      rw [ownerCount, storageLoad_codeOwner_eq_solcSlotWordAt linked I ⟨3⟩
                        (by rw [hlenv]), hlacc]
                    have hlpresent : linked.accountMap.get? linked.executionEnv.codeOwner ≠
                        none := by
                      rw [hlacc, hlenv]
                      exact safeAddOwnerLinkAccountPresent σ I key haccount
                    have hccount : ownerCount counted = solcSlotWordAt ⟨3⟩ σ₁ I + ⟨1⟩ := by
                      rw [safeAddOwnerCountValue linked hlpresent, hlcount]
                    have hcthreshold : storedThreshold counted = solcSlotWordAt ⟨4⟩ σ₂ I := by
                      rw [storedThreshold, storageLoad_codeOwner_eq_solcSlotWordAt counted I ⟨4⟩
                        (by rw [hcenv]), hcacc]
                    obtain ⟨_, _, _, _, h7497⟩ := safeAddOwnerLinksTrace h6724 (by simp)
                      hm₁ hc hperm
                    by_cases hno : (ownerCount linked).toNat + 1 < UInt256.size
                    · obtain ⟨_, _, h6831⟩ := safeIncrementTrace h7497 (by simp)
                        (by rwa [hlcount] at hno) (by jump_dest)
                      by_cases ht : storedThreshold counted = threshold
                      · have hret := safeAddOwnerCountUnchanged h6831 (by simp) hperm
                          (by rwa [hcthreshold] at ht)
                        have hbody := ExecFuncBody.execBlockOK
                          (safeAddOwnerPrefix (fork := fork) (hperm := hperm) evm key threshold hc hvalue hauth hv he'
                            (safeAddOwnerTailOK (fork := fork) (hperm := by simpa only [hlenv] using hperm) linked key threshold hno
                              (safeAddOwnerThresholdUnchanged counted key threshold ht)))
                        refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                        exact reEquivSelectorExecution hdispatch hdec hbody
                          (.success hsuccess rfl hcacc.symm
                            (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                      · obtain ⟨_, _, _, h6883⟩ := safeAddOwnerCountChanged h6831 (by simp) hperm
                          (by rwa [hcthreshold] at ht)
                        have h9325' := safeRuntime_block_6883 (by simp) (by jump_dest) h6883
                        obtain ⟨_, _, h6891⟩ := safeAuthorizedTrace h9325' (by simp) hauth
                          (by jump_dest)
                        by_cases hle : threshold.toNat ≤ (ownerCount counted).toNat
                        · by_cases hz : threshold = ⟨0⟩
                          · have hrev := safeAddOwnerThresholdZero (hz ▸ h6891) (by simp)
                            have hbody := ExecFuncBody.execBlockRevert
                              (safeAddOwnerPrefix (fork := fork) (hperm := hperm) evm key threshold hc hvalue hauth hv he'
                                (safeAddOwnerTailRevert (fork := fork) (hperm := by simpa only [hlenv] using hperm) linked key threshold hno
                                  (safeAddOwnerThresholdRevert counted key threshold ht
                                    (hz ▸ safeThresholdSourceZero counted))))
                            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                              reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                          · have hret := safeAddOwnerThresholdTrace h6891 (by simp) hperm
                              (by rwa [hccount] at hle) hz
                            have hbody := ExecFuncBody.execBlockOK
                              (safeAddOwnerPrefix (fork := fork) (hperm := hperm) evm key threshold hc hvalue hauth hv he'
                                (safeAddOwnerTailOK (fork := fork) (hperm := by simpa only [hlenv] using hperm) linked key threshold hno
                                  (safeAddOwnerThresholdChanged (fork := fork) (hperm := by simpa only [hcenv] using hperm) counted key threshold ht hle hz)))
                            refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                            exact reEquivSelectorExecution hdispatch hdec hbody
                              (.success hsuccess rfl
                                (by rw [storageStore_accountMap, hcenv, hcacc])
                                (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                        · have hrev := safeAddOwnerThresholdTooLarge h6891 (by simp)
                            (by rwa [hccount] at hle)
                          have hbody := ExecFuncBody.execBlockRevert
                            (safeAddOwnerPrefix (fork := fork) (hperm := hperm) evm key threshold hc hvalue hauth hv he'
                              (safeAddOwnerTailRevert (fork := fork) (hperm := by simpa only [hlenv] using hperm) linked key threshold hno
                                (safeAddOwnerThresholdRevert counted key threshold ht
                                  (safeThresholdSourceTooLarge counted threshold hle))))
                          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                    · have hrev := safeIncrementOverflow h7497 (by simp)
                        (by rwa [hlcount] at hno)
                      have hbody := ExecFuncBody.execBlockRevert
                        (safeAddOwnerPrefix (fork := fork) (hperm := hperm) evm key threshold hc hvalue hauth hv he'
                          (safeAddOwnerIncrementOverflow linked key threshold hno))
                      exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · have hrev := safeCanAddOwnerTraceExisting h9379 (by simp) hc
                  solcFreePtrMem_size hv he
                have hbody := safeAddOwnerSourceGuardRevert (fork := fork) evm key threshold hvalue hauth
                  (safeCanAddOwnerSourceExisting (fork := fork) evm key hc hv (by rwa [ownerLink_eq_at]))
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeCanAddOwnerTraceInvalid h9379 (by simp) hc
                (by rw [solcFreePtrMem_size]; omega) hv
              have hbody := safeAddOwnerSourceGuardRevert (fork := fork) evm key threshold hvalue hauth
                (safeCanAddOwnerSourceInvalid (fork := fork) evm key hc hv)
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · have hrev := safeUnauthorizedTrace h9325
              (by simp [safeRuntime_block_6703_stack]) hauth
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeAddOwnerSourceUnauthorized _ locals hvalue hauth
        · have hrev := safeDecodeAddressNoncanon h6952 (by simp) hc
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_addr_uint256_none_noncanon hlen hbig hc) hrev
      · have h111 := safeRuntime_block_6684_taken (by simp) (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckShort_4_64 hlong (by omega) hsize]
          decide) (by jump_dest) h6684
        have hrev := safeRuntime_block_111 (by simp) h111
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_addr_uint256_none_short hlong (by omega)) hrev
    · have h111 := safeRuntime_block_6684_taken (by simp) (by
        rw [hlenWord]
        change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
        rw [solcDecodeLenCheckHuge_4_64 (by omega) hsize]
        decide) (by jump_dest) h6684
      have hrev := safeRuntime_block_111 (by simp) h111
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_addr_uint256_none_huge (by omega)) hrev
  · have h111 := safeRuntime_block_6678_taken (by simp) hvalue (by jump_dest) h6678
    have hrev := safeRuntime_block_111 (by simp) h111
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `addOwnerWithThreshold` (`addownerwiththresholdTransition`). -/
theorem safeAddownerwiththresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (haccount : σ.get? I.codeOwner ≠ none)
    (hdispatch : selectorDispatchMsg contract I.calldata = some addownerwiththresholdTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeAddownerwiththresholdBodyCore hcode hsize haccount hdispatch

end Benchmarks.Safe.ViaIR

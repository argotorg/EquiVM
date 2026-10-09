import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.AddOwnerTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeAddownerwiththresholdBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some addownerwiththresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x0d 0x58 0x2f 0x13 ⟨0x0d582f13⟩
    hdispatch addownerwiththresholdSelectorBytes (by decide)
  obtain ⟨k, C, h633⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x0d582f13⟩ 0 ⟨633⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h644 := safeRuntime_block_633_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h633
    have h9112 := safeRuntime_block_644 (by simp) (by jump_dest) h644
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_64 hlen hbig hsize
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h659⟩ := safeDecodeAddressWord h9112 (by simp)
            hcheck hc (by jump_dest)
          have h1736 := safeRuntime_block_659 (by simp) (by jump_dest) h659
          have h6757 := safeRuntime_block_1736 (by simp) (by jump_dest) h1736
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (addownerwiththresholdTransition.params.map Param.name)
              (transitionSignature addownerwiththresholdTransition).paramTypes I.calldata =
              some (addOwnerArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36)) :=
            decodeCalldata_addr_uint256_ok hlen hbig hc
          by_cases hauth : I.source = I.codeOwner
          · obtain ⟨_, _, h1744⟩ := safeAuthorizedTrace h6757 (by simp) hauth (by jump_dest)
            have h6783 := safeRuntime_block_1744 (by simp) (by jump_dest) h1744
            let evm := initState σ σ₀ (.ofUInt256 g) A I
            let key := calldataWord I.calldata 4
            let threshold := calldataWord I.calldata 36
            change RD safeBytecode I (.ofUInt256 g) evm ⟨6783⟩
              [key, ⟨1753⟩, threshold, key, ⟨664⟩, selWord I] _ _ _ σ _ _ at h6783
            by_cases hv : validOwner σ I key
            · by_cases he : ownerLinkAt σ I key = ⟨0⟩
              · have he' : ownerLink evm key = ⟨0⟩ := by rw [ownerLink_eq_at]; exact he
                obtain ⟨mem₁, aw₁, k₁, C₁, hm₁, _, h1753⟩ := safeCanAddOwnerTrace h6783
                  (by simp) hc solcFreePtrMem_size solcFreePtrMem_read64 hv he (by jump_dest)
                cases hperm : I.perm with
                | false =>
                    have hstatic := safeAddOwnerTraceStatic h1753 (by simp) hperm
                    have hbody := safeAddOwnerSourceStatic evm key threshold hc hvalue hauth hv
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
                    have hccount : ownerCount counted = solcSlotWordAt ⟨3⟩ σ₂ I := by
                      rw [ownerCount, storageLoad_codeOwner_eq_solcSlotWordAt counted I ⟨3⟩
                        (by rw [hcenv]), hcacc]
                    have hcthreshold : storedThreshold counted = solcSlotWordAt ⟨4⟩ σ₂ I := by
                      rw [storedThreshold, storageLoad_codeOwner_eq_solcSlotWordAt counted I ⟨4⟩
                        (by rw [hcenv]), hcacc]
                    obtain ⟨_, _, _, _, h11161⟩ := safeAddOwnerLinksTrace h1753 (by simp)
                      hm₁ hc hperm
                    by_cases hno : (ownerCount linked).toNat + 1 < UInt256.size
                    · obtain ⟨_, _, h1863⟩ := safeIncrementTrace h11161 (by simp)
                        (by rwa [hlcount] at hno) (by jump_dest)
                      by_cases ht : storedThreshold counted = threshold
                      · have hret := safeAddOwnerCountUnchanged h1863 (by simp) hperm
                          (by rwa [hcthreshold] at ht)
                        have hbody := ExecFuncBody.execBlockOK
                          (safeAddOwnerPrefix evm key threshold hc hvalue hauth hv he'
                            (safeAddOwnerTailOK linked key threshold hno
                              (safeAddOwnerThresholdUnchanged counted key threshold ht)))
                        refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                        exact reEquivSelectorExecution hdispatch hdec hbody
                          (.success hsuccess rfl hcacc.symm
                            (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                      · obtain ⟨_, _, _, h3415⟩ := safeAddOwnerCountChanged h1863 (by simp) hperm
                          (by rwa [hcthreshold] at ht)
                        have h6757' := safeRuntime_block_3415 (by simp) (by jump_dest) h3415
                        obtain ⟨_, _, h3423⟩ := safeAuthorizedTrace h6757' (by simp) hauth
                          (by jump_dest)
                        by_cases hle : threshold.toNat ≤ (ownerCount counted).toNat
                        · by_cases hz : threshold = ⟨0⟩
                          · have hrev := safeThresholdTraceZero (hz ▸ h3423) (by simp)
                            have hbody := ExecFuncBody.execBlockRevert
                              (safeAddOwnerPrefix evm key threshold hc hvalue hauth hv he'
                                (safeAddOwnerTailRevert linked key threshold hno
                                  (safeAddOwnerThresholdRevert counted key threshold ht
                                    (hz ▸ safeThresholdSourceZero counted))))
                            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                              reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                          · obtain ⟨_, _, h3474⟩ := safeThresholdReach h3423 (by simp)
                              (by rwa [hccount] at hle) hz
                            obtain ⟨_, _, _, _, h1936⟩ := safeThresholdTrace h3474 (by simp)
                              hperm (by jump_dest)
                            have h664 := safeRuntime_block_1936 (by simp) (by jump_dest) h1936
                            have hret := safeRuntime_block_664 (by simp
                              [safeRuntime_block_1936_stack]) h664
                            have hbody := ExecFuncBody.execBlockOK
                              (safeAddOwnerPrefix evm key threshold hc hvalue hauth hv he'
                                (safeAddOwnerTailOK linked key threshold hno
                                  (safeAddOwnerThresholdChanged counted key threshold ht hle hz)))
                            refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                            exact reEquivSelectorExecution hdispatch hdec hbody
                              (.success hsuccess rfl
                                (by rw [storageStore_accountMap, hcenv, hcacc])
                                (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                        · have hrev := safeThresholdTraceTooLarge h3423 (by simp)
                            (by rwa [hccount] at hle)
                          have hbody := ExecFuncBody.execBlockRevert
                            (safeAddOwnerPrefix evm key threshold hc hvalue hauth hv he'
                              (safeAddOwnerTailRevert linked key threshold hno
                                (safeAddOwnerThresholdRevert counted key threshold ht
                                  (safeThresholdSourceTooLarge counted threshold hle))))
                          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                    · have hrev := safeIncrementOverflow h11161 (by simp)
                        (by rwa [hlcount] at hno)
                      have hbody := ExecFuncBody.execBlockRevert
                        (safeAddOwnerPrefix evm key threshold hc hvalue hauth hv he'
                          (safeAddOwnerIncrementOverflow linked key threshold hno))
                      exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · have hrev := safeCanAddOwnerTraceExisting h6783 (by simp) hc
                  solcFreePtrMem_size hv he
                have hbody := safeAddOwnerSourceGuardRevert evm key threshold hvalue hauth
                  (safeCanAddOwnerSourceExisting evm key hc hv (by rwa [ownerLink_eq_at]))
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeCanAddOwnerTraceInvalid h6783 (by simp) hc
                (by rw [solcFreePtrMem_size]; omega) hv
              have hbody := safeAddOwnerSourceGuardRevert evm key threshold hvalue hauth
                (safeCanAddOwnerSourceInvalid evm key hc hv)
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · have hrev := safeUnauthorizedTrace h6757
              (by simp [safeRuntime_block_1736_stack]) hauth
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeAddOwnerSourceUnauthorized _ locals hvalue hauth
        · have hrev := safeDecodeAddressWordNoncanon h9112 (by simp) hcheck hc
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_addr_uint256_none_noncanon hlen hbig hc) hrev
      · have hrev := safeDecodeAddressWordRevert h9112 (by simp)
          (solcDecodeLenCheckShort_4_64 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_addr_uint256_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressWordRevert h9112 (by simp)
        (solcDecodeLenCheckHuge_4_64 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_addr_uint256_none_huge (by omega)) hrev
  · have h641 := safeRuntime_block_633_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h633
    have hrev := safeRuntime_block_641 (by simp [safeRuntime_block_633_fallthrough_stack]) h641
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `addOwnerWithThreshold` (`addownerwiththresholdTransition`). -/
theorem safeAddownerwiththresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some addownerwiththresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeAddownerwiththresholdBodyCore hcode hsize hdispatch

end Benchmarks.Safe

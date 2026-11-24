import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.AddressAddressWordDecoder
import Benchmarks.Safe.ViaIR.RemoveOwnerTrace
import Benchmarks.Safe.ViaIR.IRLengthCheck

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeRemoveownerBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some removeownerTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xf8 0xdc 0x5d 0xd9 ⟨0xf8dc5dd9⟩
    hdispatch removeownerSelectorBytes (by decide)
  obtain ⟨k, C, h592⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xf8dc5dd9⟩ 29 ⟨592⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h599 := safeRuntime_block_592_fallthrough (by simp) hvalue h592
    simp only [safeRuntime_block_592_fallthrough_stack] at h599
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 100 ≤ I.calldata.size
      · have h611 := safeRuntime_block_599_fallthrough (by simp)
          (by rw [hlenWord]; exact solcCalldataStaticLenCheckOk (words := 3) hlen hbig hsize) h599
        by_cases hp : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · by_cases hc : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · obtain ⟨_, _, h626⟩ := safeDecodeAddressAddressWord h611 (by simp) hp hc
            have h9325 := safeRuntime_block_626 (by simp) (by jump_dest) h626
            have hdec : config.externalABI.decodeCalldata?
                (removeownerTransition.params.map Param.name)
                (transitionSignature removeownerTransition).paramTypes I.calldata =
                some (removeOwnerArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                  (calldataWord I.calldata 68)) :=
              decodeCalldata_address_address_uint256_ok hlen hbig hp hc
            by_cases hauth : I.source = I.codeOwner
            · obtain ⟨_, _, h639⟩ := safeAuthorizedTrace h9325 (by simp) hauth (by jump_dest)
              let evm := initState σ σ₀ (.ofUInt256 g) A I
              let prev := calldataWord I.calldata 4
              let key := calldataWord I.calldata 36
              let threshold := calldataWord I.calldata 68
              change RD fork safeBytecode I (.ofUInt256 g) evm ⟨639⟩
                [key, prev, threshold, ⟨0⟩] _ _ _ σ _ _ at h639
              have hcount : ownerCount evm = solcSlotWordAt ⟨3⟩ σ I :=
                storageLoad_codeOwner_eq_solcSlotWordAt evm I ⟨3⟩ rfl
              by_cases hz : ownerCount evm = ⟨0⟩
              · have hzero : solcSlotWordAt ⟨3⟩ σ I = ⟨0⟩ := hcount.symm.trans hz
                have hrev := safeDecrementUnderflow h639 (by simp) hzero
                have hbody := safeRemoveOwnerUnderflow (fork := fork) evm prev key threshold hvalue hauth hz
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · obtain ⟨_, _, h649⟩ := safeDecrementTrace h639 (by simp)
                  (by rwa [hcount] at hz)
                cases hperm : I.perm with
                | false =>
                    have hstatic := safeRemoveOwnerCountStatic h649 (by simp) hperm
                    have hbody := safeRemoveOwnerStatic (fork := fork) evm prev key threshold hvalue hauth hz hperm
                    exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                      reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
                | true =>
                    let counted := removeOwnerCountState evm
                    let σ₁ := removeOwnerCountAccounts σ I
                    have hcacc : counted.accountMap = σ₁ := safeRemoveOwnerCountAccounts evm
                    have hcenv : counted.executionEnv = I := safeRemoveOwnerCountEnv evm
                    have hcounted : ownerCount counted =
                        UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩ := by
                      rw [safeRemoveOwnerCountValue evm hz, hcount]
                    by_cases hle : threshold.toNat ≤ (ownerCount counted).toNat
                    · obtain ⟨_, _, h663⟩ := safeRemoveOwnerCountReach h649 (by simp) hperm
                        (by rwa [hcounted] at hle)
                      have h10772 := safeRuntime_block_663 (by simp) (by jump_dest) h663
                      by_cases hv : validOwner counted.accountMap counted.executionEnv key
                      · by_cases hl : ownerLink counted prev = key
                        · obtain ⟨mem₁, aw₁, k₁, C₁, hm₁, _, h672⟩ :=
                            safeCanRemoveOwnerTrace h10772 (by simp) hp hc solcFreePtrMem_size
                              solcFreePtrMem_read64 (by rwa [hcacc, hcenv] at hv)
                              (by rwa [ownerLink_eq_at, hcacc, hcenv] at hl) (by jump_dest)
                          obtain ⟨_, _, _, _, h748⟩ := safeRemoveOwnerLinksTrace h672
                            (by simp) hm₁ hp hc hperm
                          let linked := removeOwnerLinks counted prev key
                          let σ₂ := removeOwnerLinkAccounts σ₁ I prev key
                          have hlacc : linked.accountMap = σ₂ := by
                            rw [safeRemoveOwnerLinkAccounts, hcacc, hcenv]
                          have hlenv : linked.executionEnv = I :=
                            (safeRemoveOwnerLinksEnv counted prev key).trans hcenv
                          have hlcount : ownerCount linked = solcSlotWordAt ⟨3⟩ σ₂ I := by
                            rw [ownerCount, storageLoad_codeOwner_eq_solcSlotWordAt linked I ⟨3⟩
                              (by rw [hlenv]), hlacc]
                          have hlthreshold : storedThreshold linked = solcSlotWordAt ⟨4⟩ σ₂ I := by
                            rw [storedThreshold,
                              storageLoad_codeOwner_eq_solcSlotWordAt linked I ⟨4⟩
                                (by rw [hlenv]), hlacc]
                          have hb := safeRemoveOwnerLocal₁ prev key threshold "threshold" (by
                            decide)
                          have he := safeRemoveOwnerEvalThreshold₁ linked prev key threshold
                          by_cases ht : storedThreshold linked = threshold
                          · have hret := safeRemoveOwnerThresholdUnchanged h748 (by simp) hperm
                              (by rwa [hlthreshold] at ht)
                            have hbody := ExecFuncBody.execBlockOK
                              (safeRemoveOwnerPrefix (fork := fork) (hperm := hperm) evm prev key threshold hvalue hauth hz
                                (safeRemoveOwnerLinksPrefix (fork := fork) (hperm := by simpa only [hcenv] using hperm) counted prev key threshold hp hc hle
                                  hv hl
                                  (safeThresholdChangeUnchanged linked _ threshold hb he ht)))
                            refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                            exact reEquivSelectorExecution hdispatch hdec hbody
                              (.success hsuccess rfl hlacc.symm
                                (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                          · obtain ⟨_, _, _, h796⟩ := safeRemoveOwnerThresholdChanged h748
                              (by simp) hperm (by rwa [hlthreshold] at ht)
                            have h9325' := safeRuntime_block_796 (by simp) (by jump_dest) h796
                            obtain ⟨_, _, h804⟩ := safeAuthorizedTrace h9325' (by simp) hauth
                              (by jump_dest)
                            by_cases hle' : threshold.toNat ≤ (ownerCount linked).toNat
                            · by_cases htz : threshold = ⟨0⟩
                              · have hrev := safeRemoveOwnerThresholdZero (htz ▸ h804) (by simp)
                                have hbody := ExecFuncBody.execBlockRevert
                                  (safeRemoveOwnerPrefix (fork := fork) (hperm := hperm) evm prev key threshold hvalue hauth hz
                                    (safeRemoveOwnerLinksPrefix (fork := fork) (hperm := by simpa only [hcenv] using hperm) counted prev key threshold hp hc hle
                                      hv hl (safeThresholdChangeRevert linked _ threshold hb he ht
                                        (htz ▸ safeThresholdSourceZero linked))))
                                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                              · have hret := safeRemoveOwnerThresholdTrace h804 (by simp) hperm
                                  (by rwa [hlcount] at hle') htz
                                have hbody := ExecFuncBody.execBlockOK
                                  (safeRemoveOwnerPrefix (fork := fork) (hperm := hperm) evm prev key threshold hvalue hauth hz
                                    (safeRemoveOwnerLinksPrefix (fork := fork) (hperm := by simpa only [hcenv] using hperm) counted prev key threshold hp hc hle
                                      hv hl (safeThresholdChangeChanged (fork := fork) (hperm := by simpa only [hlenv] using hperm) linked _ threshold hb he ht
                                        hle' htz)))
                                refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                                exact reEquivSelectorExecution hdispatch hdec hbody
                                  (.success hsuccess rfl
                                    (by rw [storageStore_accountMap, hlenv, hlacc])
                                    (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                            · have hrev := safeRemoveOwnerThresholdTooLarge h804 (by simp)
                                (by rwa [hlcount] at hle')
                              have hbody := ExecFuncBody.execBlockRevert
                                (safeRemoveOwnerPrefix (fork := fork) (hperm := hperm) evm prev key threshold hvalue hauth hz
                                  (safeRemoveOwnerLinksPrefix (fork := fork) (hperm := by simpa only [hcenv] using hperm) counted prev key threshold hp hc hle
                                    hv hl (safeThresholdChangeRevert linked _ threshold hb he ht
                                      (safeThresholdSourceTooLarge linked threshold hle'))))
                              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                        · have hrev := safeCanRemoveOwnerTraceUnlinked h10772 (by simp) hp hc
                            solcFreePtrMem_size (by rwa [hcacc, hcenv] at hv)
                            (by rwa [ownerLink_eq_at, hcacc, hcenv] at hl)
                          have hbody := ExecFuncBody.execBlockRevert
                            (safeRemoveOwnerPrefix (fork := fork) (hperm := hperm) evm prev key threshold hvalue hauth hz
                              (safeRemoveOwnerGuardRevert counted prev key threshold hle
                                (safeCanRemoveOwnerSourceUnlinked counted prev key hp hc hv hl)))
                          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                      · have hrev := safeCanRemoveOwnerTraceInvalid h10772 (by simp) hc
                          (by rw [solcFreePtrMem_size]; omega) (by rwa [hcacc, hcenv] at hv)
                        have hbody := ExecFuncBody.execBlockRevert
                          (safeRemoveOwnerPrefix (fork := fork) (hperm := hperm) evm prev key threshold hvalue hauth hz
                            (safeRemoveOwnerGuardRevert counted prev key threshold hle
                              (safeCanRemoveOwnerSourceInvalid counted prev key hc hv)))
                        exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                          reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                    · have hrev := safeRemoveOwnerCountRevert h649 (by simp) hperm
                        (by rwa [hcounted] at hle)
                      have hbody := ExecFuncBody.execBlockRevert
                        (safeRemoveOwnerPrefix (fork := fork) (hperm := hperm) evm prev key threshold hvalue hauth hz
                          (safeRemoveOwnerCountTooSmall counted prev key threshold hle))
                      exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeUnauthorizedTrace h9325
                (by simp [safeRuntime_block_626_stack]) hauth
              exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
                safeRemoveOwnerUnauthorized _ locals hvalue hauth
          · have hrev := safeDecodeAddressAddressWordNoncanon1 h611 (by simp) hp hc
            exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
              (decodeCalldata_address_address_uint256_none_noncanon1 hlen hbig hp hc) hrev
        · have hrev := safeDecodeAddressAddressWordNoncanon0 h611 (by simp) hp
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_address_uint256_none_noncanon0 hlen hbig hp) hrev
      · have h589 := safeRuntime_block_599_taken (by simp) (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
            (UInt256.ofNat (32 * 3)) ≠ ⟨0⟩
          rw [solcCalldataStaticLenCheckShort (words := 3) hlong (by omega) hsize (by decide)]
          decide) (by jump_dest) h599
        have hrev := safeRuntime_block_589 (by simp) h589
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_address_uint256_none_short hlong (by omega)) hrev
    · have h589 := safeRuntime_block_599_taken (by simp) (by
        rw [hlenWord]
        change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
          (UInt256.ofNat (32 * 3)) ≠ ⟨0⟩
        rw [solcCalldataStaticLenCheckHuge (words := 3) (by omega) hsize (by decide)]
        decide) (by jump_dest) h599
      have hrev := safeRuntime_block_589 (by simp) h589
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_address_uint256_none_huge (by omega)) hrev
  · have h589 := safeRuntime_block_592_taken (by simp) hvalue (by jump_dest) h592
    have hrev := safeRuntime_block_589 (by simp [safeRuntime_block_592_taken_stack]) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `removeOwner` (`removeownerTransition`). -/
theorem safeRemoveownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some removeownerTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeRemoveownerBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.AddressAddressWordDecoder
import Benchmarks.Safe.RemoveOwnerTrace
import Benchmarks.Safe.Blocks.Runtime_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeRemoveownerBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some removeownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xf8 0xdc 0x5d 0xd9 ⟨0xf8dc5dd9⟩
    hdispatch removeownerSelectorBytes (by decide)
  obtain ⟨k, C, h1657⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xf8dc5dd9⟩ 2 ⟨1657⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1668 := safeRuntime_block_1657_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1657
    have h11079 := safeRuntime_block_1668 (by simp) (by jump_dest) h1668
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 100 ≤ I.calldata.size
      · have hcheck := solcCalldataStaticLenCheckOk (words := 3) hlen hbig hsize
        by_cases hp : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · by_cases hc : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · obtain ⟨_, _, h1683⟩ := safeDecodeAddressAddressWord h11079 (by simp)
              hcheck hp hc (by jump_dest)
            have h6566 := safeRuntime_block_1683 (by simp) (by jump_dest) h1683
            have h6757 := safeRuntime_block_6566 (by simp) (by jump_dest) h6566
            have hdec : decodeCalldataWithMode config.abiDecodeMode
                (removeownerTransition.params.map Param.name)
                (transitionSignature removeownerTransition).paramTypes I.calldata =
                some (removeOwnerArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                  (calldataWord I.calldata 68)) :=
              decodeCalldata_address_address_uint256_ok hlen hbig hp hc
            by_cases hauth : I.source = I.codeOwner
            · obtain ⟨_, _, h6574⟩ := safeAuthorizedTrace h6757 (by simp) hauth (by jump_dest)
              obtain ⟨_, _, h11663⟩ := safeRuntime_block_6574 (by simp) (by jump_dest) h6574
              let evm := initState σ σ₀ (.ofUInt256 g) A I
              let prev := calldataWord I.calldata 4
              let key := calldataWord I.calldata 36
              let threshold := calldataWord I.calldata 68
              change RD safeBytecode I (.ofUInt256 g) evm ⟨11663⟩
                [solcSlotWordAt ⟨3⟩ σ I, ⟨6589⟩, ⟨0⟩, ⟨3⟩, threshold, threshold,
                  key, prev, ⟨664⟩, selWord I] _ _ _ σ _ _ at h11663
              have hcount : ownerCount evm = solcSlotWordAt ⟨3⟩ σ I :=
                storageLoad_codeOwner_eq_solcSlotWordAt evm I ⟨3⟩ rfl
              by_cases hz : ownerCount evm = ⟨0⟩
              · have hzero : solcSlotWordAt ⟨3⟩ σ I = ⟨0⟩ := hcount.symm.trans hz
                have hrev := safeDecrementUnderflow (hzero ▸ h11663) (by simp)
                have hbody := safeRemoveOwnerUnderflow evm prev key threshold hvalue hauth hz
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · obtain ⟨_, _, h6589⟩ := safeDecrementTrace h11663 (by simp)
                  (by rwa [hcount] at hz) (by jump_dest)
                cases hperm : I.perm with
                | false =>
                    have hstatic := safeRemoveOwnerCountStatic h6589 (by simp) hperm
                    have hbody := safeRemoveOwnerStatic evm prev key threshold hvalue hauth hz hperm
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
                    · obtain ⟨_, _, h6617⟩ := safeRemoveOwnerCountReach h6589 (by simp) hperm
                        (by rwa [hcounted] at hle)
                      have h8528 := safeRuntime_block_6617 (by simp) (by jump_dest) h6617
                      by_cases hv : validOwner counted.accountMap counted.executionEnv key
                      · by_cases hl : ownerLink counted prev = key
                        · obtain ⟨mem₁, aw₁, k₁, C₁, hm₁, _, h6627⟩ :=
                            safeCanRemoveOwnerTrace h8528 (by simp) hp hc solcFreePtrMem_size
                              solcFreePtrMem_read64 (by rwa [hcacc, hcenv] at hv)
                              (by rwa [ownerLink_eq_at, hcacc, hcenv] at hl) (by jump_dest)
                          obtain ⟨_, _, _, _, _, h6700⟩ := safeRemoveOwnerLinksTrace h6627
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
                          · have hret := safeRemoveOwnerThresholdUnchanged h6700 (by simp) hperm
                              (by rwa [hlthreshold] at ht)
                            have hbody := ExecFuncBody.execBlockOK
                              (safeRemoveOwnerPrefix evm prev key threshold hvalue hauth hz
                                (safeRemoveOwnerLinksPrefix counted prev key threshold hp hc hle
                                  hv hl
                                  (safeThresholdChangeUnchanged linked _ threshold hb he ht)))
                            refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                            exact reEquivSelectorExecution hdispatch hdec hbody
                              (.success hsuccess rfl hlacc.symm
                                (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                          · obtain ⟨_, _, _, h3415⟩ := safeRemoveOwnerThresholdChanged h6700
                              (by simp) hperm (by rwa [hlthreshold] at ht)
                            have h6757' := safeRuntime_block_3415 (by simp) (by jump_dest) h3415
                            obtain ⟨_, _, h3423⟩ := safeAuthorizedTrace h6757' (by simp) hauth
                              (by jump_dest)
                            by_cases hle' : threshold.toNat ≤ (ownerCount linked).toNat
                            · by_cases htz : threshold = ⟨0⟩
                              · have hrev := safeThresholdTraceZero (htz ▸ h3423) (by simp)
                                have hbody := ExecFuncBody.execBlockRevert
                                  (safeRemoveOwnerPrefix evm prev key threshold hvalue hauth hz
                                    (safeRemoveOwnerLinksPrefix counted prev key threshold hp hc hle
                                      hv hl (safeThresholdChangeRevert linked _ threshold hb he ht
                                        (htz ▸ safeThresholdSourceZero linked))))
                                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                              · obtain ⟨_, _, h3474⟩ := safeThresholdReach h3423 (by simp)
                                  (by rwa [hlcount] at hle') htz
                                obtain ⟨_, _, _, _, h6752⟩ := safeThresholdTrace h3474 (by simp)
                                  hperm (by jump_dest)
                                have h664 := safeRuntime_block_6752 (by simp) (by jump_dest) h6752
                                have hret := safeRuntime_block_664
                                  (by simp [safeRuntime_block_6752_stack]) h664
                                have hbody := ExecFuncBody.execBlockOK
                                  (safeRemoveOwnerPrefix evm prev key threshold hvalue hauth hz
                                    (safeRemoveOwnerLinksPrefix counted prev key threshold hp hc hle
                                      hv hl (safeThresholdChangeChanged linked _ threshold hb he ht
                                        hle' htz)))
                                refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                                exact reEquivSelectorExecution hdispatch hdec hbody
                                  (.success hsuccess rfl
                                    (by rw [storageStore_accountMap, hlenv, hlacc])
                                    (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                            · have hrev := safeThresholdTraceTooLarge h3423 (by simp)
                                (by rwa [hlcount] at hle')
                              have hbody := ExecFuncBody.execBlockRevert
                                (safeRemoveOwnerPrefix evm prev key threshold hvalue hauth hz
                                  (safeRemoveOwnerLinksPrefix counted prev key threshold hp hc hle
                                    hv hl (safeThresholdChangeRevert linked _ threshold hb he ht
                                      (safeThresholdSourceTooLarge linked threshold hle'))))
                              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                        · have hrev := safeCanRemoveOwnerTraceUnlinked h8528 (by simp) hp hc
                            solcFreePtrMem_size (by rwa [hcacc, hcenv] at hv)
                            (by rwa [ownerLink_eq_at, hcacc, hcenv] at hl)
                          have hbody := ExecFuncBody.execBlockRevert
                            (safeRemoveOwnerPrefix evm prev key threshold hvalue hauth hz
                              (safeRemoveOwnerGuardRevert counted prev key threshold hle
                                (safeCanRemoveOwnerSourceUnlinked counted prev key hp hc hv hl)))
                          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                      · have hrev := safeCanRemoveOwnerTraceInvalid h8528 (by simp) hc
                          (by rw [solcFreePtrMem_size]; omega) (by rwa [hcacc, hcenv] at hv)
                        have hbody := ExecFuncBody.execBlockRevert
                          (safeRemoveOwnerPrefix evm prev key threshold hvalue hauth hz
                            (safeRemoveOwnerGuardRevert counted prev key threshold hle
                              (safeCanRemoveOwnerSourceInvalid counted prev key hc hv)))
                        exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                          reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                    · have hrev := safeRemoveOwnerCountRevert h6589 (by simp) hperm
                        (by rwa [hcounted] at hle)
                      have hbody := ExecFuncBody.execBlockRevert
                        (safeRemoveOwnerPrefix evm prev key threshold hvalue hauth hz
                          (safeRemoveOwnerCountTooSmall counted prev key threshold hle))
                      exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeUnauthorizedTrace h6757
                (by simp [safeRuntime_block_6566_stack]) hauth
              exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
                safeRemoveOwnerUnauthorized _ locals hvalue hauth
          · have hrev := safeDecodeAddressAddressWordNoncanon1 h11079 (by simp) hcheck hp hc
            exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
              (decodeCalldata_address_address_uint256_none_noncanon1 hlen hbig hp hc) hrev
        · have hrev := safeDecodeAddressAddressWordNoncanon0 h11079 (by simp) hcheck hp
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_address_uint256_none_noncanon0 hlen hbig hp) hrev
      · have hrev := safeDecodeAddressAddressWordRevert h11079 (by simp)
          (solcCalldataStaticLenCheckShort (words := 3) hlong (by omega) hsize (by decide))
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_address_uint256_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressAddressWordRevert h11079 (by simp)
        (solcCalldataStaticLenCheckHuge (words := 3) (by omega) hsize (by decide))
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_address_uint256_none_huge (by omega)) hrev
  · have h1665 := safeRuntime_block_1657_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1657
    have hrev := safeRuntime_block_1665 (by simp [safeRuntime_block_1657_fallthrough_stack]) h1665
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `removeOwner` (`removeownerTransition`). -/
theorem safeRemoveownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some removeownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeRemoveownerBodyCore hcode hsize hdispatch

end Benchmarks.Safe

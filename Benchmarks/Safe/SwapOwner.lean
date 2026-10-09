import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.SwapOwnerTrace
import Benchmarks.Safe.TripleDecoders
import Benchmarks.Safe.TripleCalldata
import Benchmarks.Safe.Blocks.Runtime_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeSwapownerBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some swapownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe3 0x18 0xb5 0x2b ⟨0xe318b52b⟩
    hdispatch swapownerSelectorBytes (by decide)
  obtain ⟨k, C, h1470⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe318b52b⟩ 1 ⟨1470⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1481 := safeRuntime_block_1470_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1470
    have h10923 := safeRuntime_block_1481 (by simp) (by jump_dest) h1481
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 100 ≤ I.calldata.size
      · have hcheck := solcCalldataStaticLenCheckOk (words := 3) hlen hbig hsize
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · by_cases hc2 : (calldataWord I.calldata 68).toNat < EVM.addressModulus
            · obtain ⟨_, _, h1496⟩ := safeDecodeAddressTriple h10923 (by simp)
                hcheck hc0 hc1 hc2 (by jump_dest)
              have h6248 := safeRuntime_block_1496 (by simp) (by jump_dest) h1496
              have h6757 := safeRuntime_block_6248 (by simp) (by jump_dest) h6248
              have hdec : decodeCalldataWithMode config.abiDecodeMode
                  (swapownerTransition.params.map Param.name)
                  (transitionSignature swapownerTransition).paramTypes I.calldata =
                  some (swapOwnerArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                    (calldataWord I.calldata 68)) := by
                simpa only [hc0, hc1, hc2, and_self, if_true] using
                  (decodeAddressTriple (x := "prevOwner") (y := "oldOwner") (z := "newOwner")
                    hlen hbig)
              by_cases hauth : I.source = I.codeOwner
              · obtain ⟨_, _, h6256⟩ := safeAuthorizedTrace h6757 (by simp) hauth (by jump_dest)
                have h6783 := safeRuntime_block_6256 (by simp) (by jump_dest) h6256
                let evm := initState σ σ₀ (.ofUInt256 g) A I
                let prev := calldataWord I.calldata 4
                let old := calldataWord I.calldata 36
                let new := calldataWord I.calldata 68
                change RD safeBytecode I (.ofUInt256 g) evm ⟨6783⟩
                  [new, ⟨6265⟩, new, old, prev, ⟨664⟩, selWord I] _ _ _ σ _ _ at h6783
                by_cases hvn : validOwner σ I new
                · by_cases he : ownerLinkAt σ I new = ⟨0⟩
                  · have he' : ownerLink evm new = ⟨0⟩ := by rw [ownerLink_eq_at]; exact he
                    obtain ⟨mem₁, aw₁, k₁, C₁, hm₁, h64₁, h6265⟩ := safeCanAddOwnerTrace h6783
                      (by simp) hc2 solcFreePtrMem_size solcFreePtrMem_read64 hvn he (by jump_dest)
                    have h8528 := safeRuntime_block_6265 (by simp) (by jump_dest) h6265
                    by_cases hvo : validOwner σ I old
                    · by_cases hl : ownerLinkAt σ I prev = old
                      · have hl' : ownerLink evm prev = old := by rw [ownerLink_eq_at]; exact hl
                        obtain ⟨mem₂, aw₂, k₂, C₂, hm₂, _, h6275⟩ := safeCanRemoveOwnerTrace h8528
                          (by simp) hc0 hc1 hm₁ h64₁ hvo hl (by jump_dest)
                        cases hperm : I.perm with
                        | false =>
                            have hstatic := safeSwapOwnerTraceStatic h6275 (by simp) hperm
                            have hbody := safeSwapOwnerSourceStatic evm prev old new hc0 hc1 hc2
                              hvalue hauth hvn he' hvo hl' hperm
                            exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                              reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
                        | true =>
                            have hret := safeSwapOwnerTrace h6275 (by simp) hm₂ hc0 hc1 hc2 hperm
                            have hbody := safeSwapOwnerSource evm prev old new hc0 hc1 hc2
                              hvalue hauth hvn he' hvo hl'
                            refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                            exact reEquivSelectorExecution hdispatch hdec hbody
                              (.success hsuccess rfl (safeSwapOwnerAccounts evm prev old new).symm
                                (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                      · have hrev := safeCanRemoveOwnerTraceUnlinked h8528 (by simp)
                          hc0 hc1 hm₁ hvo hl
                        have hbody := safeSwapOwnerSourceRemoveRevert evm prev old new hc2 hvalue
                          hauth hvn he' (safeCanRemoveOwnerSourceUnlinked evm prev old hc0 hc1
                            hvo (by rwa [ownerLink_eq_at]))
                        exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                          reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                    · have hrev := safeCanRemoveOwnerTraceInvalid h8528 (by simp) hc1
                        (by omega) hvo
                      have hbody := safeSwapOwnerSourceRemoveRevert evm prev old new hc2 hvalue
                        hauth hvn he' (safeCanRemoveOwnerSourceInvalid evm prev old hc1 hvo)
                      exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                  · have hrev := safeCanAddOwnerTraceExisting h6783 (by simp) hc2
                      solcFreePtrMem_size hvn he
                    have hbody := safeSwapOwnerSourceAddRevert evm prev old new hvalue hauth
                      (safeCanAddOwnerSourceExisting evm new hc2 hvn (by rwa [ownerLink_eq_at]))
                    exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                      reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
                · have hrev := safeCanAddOwnerTraceInvalid h6783 (by simp) hc2
                    (by rw [solcFreePtrMem_size]; omega) hvn
                  have hbody := safeSwapOwnerSourceAddRevert evm prev old new hvalue hauth
                    (safeCanAddOwnerSourceInvalid evm new hc2 hvn)
                  exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · have hrev := safeUnauthorizedTrace h6757
                  (by simp [safeRuntime_block_6248_stack]) hauth
                exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
                  safeSwapOwnerSourceUnauthorized _ locals hvalue hauth
            · have hrev := safeDecodeAddressTripleNoncanon2 h10923 (by simp) hcheck hc0 hc1 hc2
              exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
                (by simpa only [hc0, hc1, hc2, and_false, if_false] using
                  (decodeAddressTriple (x := "prevOwner") (y := "oldOwner") (z := "newOwner")
                    hlen hbig)) hrev
          · have hrev := safeDecodeAddressTripleNoncanon1 h10923 (by simp) hcheck hc0 hc1
            exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
              (by simpa only [hc0, hc1, false_and, and_false, if_false] using
                (decodeAddressTriple (x := "prevOwner") (y := "oldOwner") (z := "newOwner")
                  hlen hbig)) hrev
        · have hrev := safeDecodeAddressTripleNoncanon0 h10923 (by simp) hcheck hc0
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (by simpa only [hc0, false_and, if_false] using
              (decodeAddressTriple (x := "prevOwner") (y := "oldOwner") (z := "newOwner")
                hlen hbig)) hrev
      · have hrev := safeDecodeAddressTripleRevert h10923 (by simp)
          (solcCalldataStaticLenCheckShort (words := 3) hlong (by omega) hsize (by decide))
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeAddressTripleShort hlong (by omega)) hrev
    · have hrev := safeDecodeAddressTripleRevert h10923 (by simp)
        (solcCalldataStaticLenCheckHuge (words := 3) (by omega) hsize (by decide))
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeAddressTripleHuge (by omega)) hrev
  · have h1478 := safeRuntime_block_1470_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1470
    have hrev := safeRuntime_block_1478 (by simp [safeRuntime_block_1470_fallthrough_stack]) h1478
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `swapOwner` (`swapownerTransition`). -/
theorem safeSwapownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some swapownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeSwapownerBodyCore hcode hsize hdispatch

end Benchmarks.Safe

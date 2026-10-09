import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.ModulesAllocation
import Benchmarks.Safe.ModulesLoopFinish
import Benchmarks.Safe.ModulesReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeGetmodulespaginatedBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getmodulespaginatedTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xcc 0x2f 0x84 0x52 ⟨0xcc2f8452⟩
    hdispatch getmodulespaginatedSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xcc2f8452⟩ 3 ⟨1270⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h₁ := safeRuntime_block_1270_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) hentry
    have hdecode := safeRuntime_block_1281 (by simp) (by jump_dest) h₁
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_64 hlen hbig hsize
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h₂⟩ := safeDecodeAddressWord hdecode (by simp) hcheck hc (by jump_dest)
          have h₃ := safeRuntime_block_1296 (by simp) (by jump_dest) h₂
          let evm := initState σ σ₀ (.ofUInt256 g) A I
          let start := calldataWord I.calldata 4
          let pageSize := calldataWord I.calldata 36
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (getmodulespaginatedTransition.params.map Param.name)
              (transitionSignature getmodulespaginatedTransition).paramTypes I.calldata =
              some (modulesArgs start pageSize) := decodeCalldata_addr_uint256_ok hlen hbig hc
          change RD safeBytecode I (.ofUInt256 g) evm ⟨4815⟩
            [pageSize, start, ⟨1301⟩, selWord I] _ _ _ σ _ _ at h₃
          obtain ⟨mem₄, aw₄, k₄, C₄, h₄, hm₄, hr₄⟩ := safeModulesStartCheck h₃
            (by simp) hc solcFreePtrMem_size solcFreePtrMem_read64
          have hlink : moduleLink evm = moduleLinkAt σ I := by
            funext w
            exact moduleLink_eq_at evm w
          by_cases hs : start = ⟨1⟩ ∨ moduleLinkAt σ I start ≠ ⟨0⟩
          · have hs' : start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩ := by rwa [hlink]
            simp only [hs, not_true_eq_false, decide_false] at h₄
            have h₅ := safeRuntime_block_4850_taken (by simp) (by decide) (by jump_dest) h₄
            change RD safeBytecode I (.ofUInt256 g) evm ⟨4872⟩
              [⟨0⟩, ⟨96⟩, pageSize, start, ⟨1301⟩, selWord I] mem₄ aw₄ _ σ _ _ at h₅
            by_cases hz : pageSize = ⟨0⟩
            · have hrev := safeModulesZeroSize (hz ▸ h₅) (by simp)
              have hbody := safeModulesSourceZero evm start pageSize hc hvalue hs' hz
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · obtain ⟨_, _, h₆⟩ := safeModulesSizeCheck h₅ (by simp) hz
              by_cases hn : pageSize.toNat ≤ 2 ^ 64 - 1
              · obtain ⟨aw₇, k₇, C₇, h₇⟩ := safeModulesAllocate (n := pageSize.toNat)
                  (by simpa only [u256_ofNat_toNat] using h₆) (by simp) hn
                  (fun he ↦ hz (u256_inj he)) hc hsize hm₄ hr₄
                have hm₇ := (safeAddressArrayAllocated mem₄ pageSize.toNat hm₄).scratch start ⟨1⟩
                obtain ⟨words, next, hp⟩ := LinkedPage.exists (moduleLinkAt σ I)
                  pageSize.toNat (moduleLinkAt σ I start)
                have hcanon := hp.canonical (solcAddrMask_result_canonical _)
                  (fun _ ↦ solcAddrMask_result_canonical _)
                have hps : LinkedPage (moduleLink evm) pageSize.toNat (moduleLink evm start)
                    words next := by simpa only [hlink] using hp
                obtain ⟨mem₈, aw₈, k₈, C₈, h₈, hm₈⟩ := safeModulesLoop (doneWords := []) h₇
                  (by simp) (by simpa using hm₇) hn (by simp)
                  (solcAddrMask_result_canonical _) hp
                simp only [List.nil_append] at h₈ hm₈
                by_cases hg : next = ⟨1⟩ ∨ 0 < words.length
                · obtain ⟨aw₉, k₉, C₉, h₉⟩ := safeModulesFinish h₈ (by simp) hm₈ hn
                    hp.length_le hcanon.2 hg (by jump_dest)
                  have hnext : (modulesPageNext words next).toNat < EVM.addressModulus := by
                    unfold modulesPageNext
                    split
                    · exact hcanon.2
                    · have hw := List.getLastD_mem_cons (l := words) (a := (⟨0⟩ : UInt256))
                      rcases List.mem_cons.mp hw with hw | hw
                      · rw [hw]; decide
                      · exact hcanon.1 _ hw
                  have hret := safeModulesReturn h₉ (by simp) hm₈ hn hp.length_le hcanon.1 hnext
                  obtain ⟨locals, hbody⟩ := safeModulesSourceSuccess evm start pageSize hc hvalue
                    hs' hz hn hps hg
                  exact RDret.reEquivElim hcode hret fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody
                      (.success hΞ rfl rfl (.abi (.returned rfl
                        (modulesReturnEncoding words (modulesPageNext words next) hcanon.1 hnext))))
                · have hnil : words = [] := List.eq_nil_of_length_eq_zero (by omega)
                  subst words
                  have hrev := safeModulesFinishEmpty h₈ (by simp) hcanon.2 (by simpa using hg)
                  have hbody := safeModulesSourceEmpty evm start pageSize hc hvalue hs' hz hn hps
                    (by simpa using hg)
                  exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · have hrev := safeModulesLargeSize h₆ (by simp) hn
                have hbody := safeModulesSourceLarge evm start pageSize hc hvalue hs' hz hn
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · simp only [hs, not_false_eq_true, decide_true] at h₄
            have hrev := safeModulesInvalidStart h₄ (by simp)
            have hbody := safeModulesSourceInvalid evm start pageSize hc hvalue (by rwa [hlink])
            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
              reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
        · have hrev := safeDecodeAddressWordNoncanon hdecode (by simp) hcheck hc
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_addr_uint256_none_noncanon hlen hbig hc) hrev
      · have hrev := safeDecodeAddressWordRevert hdecode (by simp)
          (solcDecodeLenCheckShort_4_64 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_addr_uint256_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressWordRevert hdecode (by simp)
        (solcDecodeLenCheckHuge_4_64 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_addr_uint256_none_huge (by omega)) hrev
  · have h₁ := safeRuntime_block_1270_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hrev := safeRuntime_block_1278 (by simp [safeRuntime_block_1270_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getModulesPaginated` (`getmodulespaginatedTransition`). -/
theorem safeGetmodulespaginatedRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getmodulespaginatedTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeGetmodulespaginatedBodyCore hcode hsize hdispatch

end Benchmarks.Safe

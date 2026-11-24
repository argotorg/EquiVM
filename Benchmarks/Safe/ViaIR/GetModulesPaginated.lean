import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.ModulesAllocation
import Benchmarks.Safe.ViaIR.ModulesLoopFinish
import Benchmarks.Safe.ViaIR.ModulesReturn

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeGetmodulespaginatedBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getmodulespaginatedTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xcc 0x2f 0x84 0x52 ⟨0xcc2f8452⟩
    hdispatch getmodulespaginatedSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xcc2f8452⟩ 18 ⟨2530⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h₁ := safeRuntime_block_2530_fallthrough (by simp) hvalue hentry
    simp only [safeRuntime_block_2530_fallthrough_stack] at h₁
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have h2549 := safeRuntime_block_2537_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_64 hlen hbig hsize) h₁
        have hdecode := safeRuntime_block_2549 (by simp) (by jump_dest) h2549
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h₃⟩ := safeDecodeAddress hdecode (by simp) hc (by jump_dest)
          let evm := initState σ σ₀ (.ofUInt256 g) A I
          let start := calldataWord I.calldata 4
          let pageSize := calldataWord I.calldata 36
          have hdec : config.externalABI.decodeCalldata?
              (getmodulespaginatedTransition.params.map Param.name)
              (transitionSignature getmodulespaginatedTransition).paramTypes I.calldata =
              some (modulesArgs start pageSize) := decodeCalldata_addr_uint256_ok hlen hbig hc
          change RD fork safeBytecode I (.ofUInt256 g) evm ⟨2556⟩
            [start, ⟨0⟩] _ _ _ σ _ _ at h₃
          obtain ⟨mem₄, aw₄, k₄, C₄, dummy, h₄, hm₄, hr₄⟩ := safeModulesStartCheck h₃
            (by simp) hc solcFreePtrMem_size solcFreePtrMem_read64
          have hlink : moduleLink evm = moduleLinkAt σ I := by
            funext w
            exact moduleLink_eq_at evm w
          by_cases hs : start = ⟨1⟩ ∨ moduleLinkAt σ I start ≠ ⟨0⟩
          · have hs' : start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩ := by rwa [hlink]
            simp only [hs, not_true_eq_false, decide_false] at h₄
            have h₅ := safeRuntime_block_2583_fallthrough (by simp) (by decide) h₄
            change RD fork safeBytecode I (.ofUInt256 g) evm ⟨2589⟩
              [pageSize, start, ⟨0⟩] mem₄ aw₄ _ σ _ _ at h₅
            by_cases hz : pageSize = ⟨0⟩
            · have hrev := safeModulesZeroSize (hz ▸ h₅) (by simp)
              have hbody := safeModulesSourceZero (fork := fork) evm start pageSize hc hvalue hs' hz
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · obtain ⟨_, _, h₆⟩ := safeModulesSizeCheck h₅ (by simp) hz
              by_cases hn : pageSize.toNat ≤ 2 ^ 59 - 6
              · have hb : pageSize.toNat ≤ 2 ^ 64 - 1 := by omega
                obtain ⟨aw₇, k₇, C₇, h₇⟩ := safeModulesAllocate (n := pageSize.toNat)
                  (by simpa only [u256_ofNat_toNat] using h₆) (by simp) hn hsize hm₄ hr₄
                have hm₇ := (safeModulesAllocated mem₄ pageSize.toNat hm₄).scratch start ⟨1⟩
                obtain ⟨words, next, hp⟩ := LinkedPage.exists (moduleLinkAt σ I)
                  pageSize.toNat (moduleLinkAt σ I start)
                have hcanon := hp.canonical (solcAddrMask_result_canonical _)
                  (fun _ ↦ solcAddrMask_result_canonical _)
                have hps : LinkedPage (moduleLink evm) pageSize.toNat (moduleLink evm start)
                    words next := by simpa only [hlink] using hp
                obtain ⟨mem₈, aw₈, k₈, C₈, h₈, hm₈⟩ := safeModulesLoop (doneWords := []) h₇
                  (by simp) (by simpa using hm₇) hb (by simp)
                  (solcAddrMask_result_canonical _) hp
                simp only [List.nil_append] at h₈ hm₈
                by_cases hg : next = ⟨1⟩ ∨ 0 < words.length
                · obtain ⟨aw₉, k₉, C₉, scratch, h₉⟩ := safeModulesFinish h₈ (by simp) hm₈ hb
                    hp.length_le hcanon.2 hcanon.1 hg
                  have hnext : (modulesPageNext words next).toNat < EVM.addressModulus := by
                    unfold modulesPageNext
                    split
                    · exact hcanon.2
                    · have hw := List.getLastD_mem_cons (l := words) (a := (⟨0⟩ : UInt256))
                      rcases List.mem_cons.mp hw with hw | hw
                      · rw [hw]; decide
                      · exact hcanon.1 _ hw
                  have hret := safeModulesReturn h₉ (by simp) hm₈ hb hp.length_le hcanon.1 hnext
                  obtain ⟨locals, hbody⟩ := safeModulesSourceSuccess evm start pageSize hc hvalue
                    hs' hz hn hps hg
                  exact RDret.reEquivElim hcode hret fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody
                      (.success hΞ rfl rfl (.abi (.returned rfl
                        (modulesReturnEncoding words (modulesPageNext words next) hcanon.1 hnext))))
                · have hnil : words = [] := List.eq_nil_of_length_eq_zero (by omega)
                  subst words
                  have hrev := safeModulesFinishEmpty h₈ (by simp) hcanon.2 (by simpa using hg)
                  have hbody := safeModulesSourceEmpty (fork := fork) evm start pageSize hc hvalue hs' hz hn hps
                    (by simpa using hg)
                  exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · have hrev := safeModulesLargeSize h₆ (by simp) hn hr₄
                have hbody := safeModulesSourceLarge (fork := fork) evm start pageSize hc hvalue hs' hz hn
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · simp only [hs, not_false_eq_true, decide_true] at h₄
            have hrev := safeModulesInvalidStart h₄ (by simp)
            have hbody := safeModulesSourceInvalid (fork := fork) evm start pageSize hc hvalue (by rwa [hlink])
            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
              reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
        · have hrev := safeDecodeAddressNoncanon hdecode (by simp) hc
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_addr_uint256_none_noncanon hlen hbig hc) hrev
      · have h589 := safeRuntime_block_2537_taken (by simp)
          (by rw [hlenWord]
              change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
              rw [solcDecodeLenCheckShort_4_64 hlong (by omega) hsize]; decide)
          (by jump_dest) h₁
        have hrev := safeRuntime_block_589 (by simp) h589
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_addr_uint256_none_short hlong (by omega)) hrev
    · have h589 := safeRuntime_block_2537_taken (by simp)
        (by rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckHuge_4_64 (by omega) hsize]; decide)
        (by jump_dest) h₁
      have hrev := safeRuntime_block_589 (by simp) h589
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_addr_uint256_none_huge (by omega)) hrev
  · have h589 := safeRuntime_block_2530_taken (by simp) hvalue (by jump_dest) hentry
    have hrev := safeRuntime_block_589 (by simp) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getModulesPaginated` (`getmodulespaginatedTransition`). -/
theorem safeGetmodulespaginatedRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getmodulespaginatedTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeGetmodulespaginatedBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

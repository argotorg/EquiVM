import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.WordPairDecoder
import Benchmarks.Safe.StorageAtLoop
import Benchmarks.Safe.StorageAtReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem safeGetstorageatBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getstorageatTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x56 0x24 0xb2 0x5b ⟨0x5624b25b⟩
    hdispatch getstorageatSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x5624b25b⟩ 0 ⟨887⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h₁ := safeRuntime_block_887_taken (by simp) (by rw [hvalue]; decide)
      (by jump_dest) hentry
    have hdecode := safeRuntime_block_898 (by simp) (by jump_dest) h₁
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · obtain ⟨_, _, h₂⟩ := safeDecodeWordPair hdecode (by simp)
          (solcDecodeLenCheckOk_4_64 hlen hbig hsize) (by jump_dest)
        have h₃ := safeRuntime_block_913 (by simp) (by jump_dest) h₂
        let evm := initState σ σ₀ (.ofUInt256 g) A I
        let offset := calldataWord I.calldata 4
        let len := calldataWord I.calldata 36
        have hdec : decodeCalldataWithMode config.abiDecodeMode
            (getstorageatTransition.params.map Param.name)
            (transitionSignature getstorageatTransition).paramTypes I.calldata =
            some (storageAtArgs offset len) := decodeWordPair hlen hbig
        change RD safeBytecode I (.ofUInt256 g) evm ⟨3053⟩
          [len, offset, ⟨918⟩, selWord I] _ _ _ σ _ _ at h₃
        by_cases hg : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1
        · have h₄ := safeStorageAtLengthCheck h₃ (by simp) hg
          obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeStorageAtAllocate h₄ (by simp) hsize
          by_cases hsmall : len.toNat < 2 ^ 251
          · have hs : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat = 32 * len.toNat := by
              simpa only [u256_ofNat_toNat] using ushl5_ofNat_toNat len.toNat hsmall
            have hn : len.toNat ≤ 2 ^ 64 - 1 := by omega
            have hsword : UInt256.shiftLeft len (UInt256.ofNat 5) =
                UInt256.ofNat (32 * len.toNat) := by
              apply u256_inj
              rw [hs, ulit_toNat' _ (by change 32 * len.toNat < 2 ^ 256; omega)]
            rw [hsword, storageAtAllocatedMemory_wordBuffer len.toNat hn] at h₅
            have hm := safeWordBufferAllocated solcFreePtrMem len.toNat
              (UInt256.ofNat (32 * len.toNat)) solcFreePtrMem_size
            obtain ⟨ws, ls, ms, aw', k', C', hsrc, hls, hms, hrd⟩ :=
              safeStorageAtLoop evm (n := len.toNat) (doneWords := []) (fuel := len.toNat)
                (by simpa only [u256_ofNat_toNat] using h₅) (by simp)
                (by simpa only [List.nil_append] using hm)
                (by simpa only [u256_ofNat_toNat] using safeStorageAtInitialLocals offset len)
                hn (by simp) (by jump_dest)
            have hret := safeStorageAtReturnTrace hrd (by simp) hms hn
            have hbody : ExecTransitionBody config contract evm (storageAtArgs offset len)
                getstorageatTransition.body
                (.returned { contract := contract, locals := ls } evm
                  (some [.bytes (wordBytes ws)])) :=
              .execBlockRet (safeStorageAtPrefix evm offset len hvalue hg
                (.consNormal hsrc (.consReturn (.return
                  (evalExprs?_singleton (evalLocalValue hls.result))))))
            exact RDret.reEquivElim hcode hret fun _ _ hΞ ↦
              reEquivSelectorExecution hdispatch hdec hbody
                (.success hΞ rfl rfl (.abi (returnEquiv_of_encode (wordBufferReturnEncoding ws))))
          · have hoog := safeStorageAtHugeOOG h₅ (by simp) (by omega)
            exact reEquiv_outOfGas (xi_error_of_X_sat_local
              (by rw [← hcode] at hoog; exact hoog))
        · have hrev := safeStorageAtLengthFail h₃ (by simp) hg
          have hbody := safeStorageAtLengthRevert evm offset len hvalue hg
          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
      · have hrev := safeDecodeWordPairRevert hdecode (by simp)
          (solcDecodeLenCheckShort_4_64 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeWordPairShort hlong (by omega)) hrev
    · have hrev := safeDecodeWordPairRevert hdecode (by simp)
        (solcDecodeLenCheckHuge_4_64 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeWordPairHuge (by omega)) hrev
  · have h₁ := safeRuntime_block_887_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hrev := safeRuntime_block_895 (by simp [safeRuntime_block_887_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getStorageAt` (`getstorageatTransition`). -/
theorem safeGetstorageatRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getstorageatTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeGetstorageatBodyCore hcode hsize hdispatch

end Benchmarks.Safe

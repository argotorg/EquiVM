import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.WordPairDecoder
import Benchmarks.Safe.ViaIR.StorageAtLoop
import Benchmarks.Safe.ViaIR.StorageAtReturn

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem safeGetstorageatBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getstorageatTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x56 0x24 0xb2 0x5b ⟨0x5624b25b⟩
    hdispatch getstorageatSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x5624b25b⟩ 7 ⟨6090⟩ hcode hsize hlong hword (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have hdecode := safeRuntime_block_6090_fallthrough (by simp) hvalue hentry
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · obtain ⟨_, _, h₃⟩ := safeDecodeWordPair hdecode (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_64 hlen hbig hsize)
        let evm := initState σ σ₀ (.ofUInt256 g) A I
        let offset := calldataWord I.calldata 4
        let len := calldataWord I.calldata 36
        have hdec : config.externalABI.decodeCalldata?
            (getstorageatTransition.params.map Param.name)
            (transitionSignature getstorageatTransition).paramTypes I.calldata =
            some (storageAtArgs offset len) := decodeWordPair hlen hbig
        change RD fork safeBytecode I (.ofUInt256 g) evm ⟨7181⟩
          [UInt256.shiftLeft len (UInt256.ofNat 5), ⟨6127⟩, offset, len,
            UInt256.shiftLeft len (UInt256.ofNat 5), selWord I, ⟨0⟩] _ _ _ σ _ _ at h₃
        have ha := safeStorageAtShiftAligned len
        by_cases hg : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 161
        · obtain ⟨_, _, h₄⟩ := safeStorageAtLengthCheck h₃ (by simp) (by omega) ha
            (by jump_dest)
          obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeStorageAtAllocate h₄ (by simp) hsize hg ha
          by_cases hsmall : len.toNat < 2 ^ 251
          · have hs : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat = 32 * len.toNat := by
              simpa only [u256_ofNat_toNat] using ushl5_ofNat_toNat len.toNat hsmall
            have hn : len.toNat ≤ 2 ^ 64 - 1 := by omega
            have hsword : UInt256.shiftLeft len (UInt256.ofNat 5) =
                UInt256.ofNat (32 * len.toNat) := by
              apply u256_inj
              rw [hs, ulit_toNat' _ (by change 32 * len.toNat < 2 ^ 256; omega)]
            rw [hsword] at h₅
            have hm := storageAtAllocatedMemory_wordBuffer len.toNat hn
            obtain ⟨ws, ls, ms, aw', k', C', hsrc, hls, hms, hrd⟩ :=
              safeStorageAtLoop evm (n := len.toNat) (doneWords := []) (fuel := len.toNat)
                (by simpa only [u256_ofNat_toNat] using h₅) (by simp)
                (by simpa only [List.nil_append] using hm)
                (by simpa only [u256_ofNat_toNat] using safeStorageAtInitialLocals offset len)
                hn (by simp)
            have hret := safeStorageAtReturnTrace hrd (by simp) hms hn
            have hbody : ExecTransitionBody fork config contract evm (storageAtArgs offset len)
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
        · have hrev := safeStorageAtLengthFail h₃ (by simp) ha hg
          have hbody := safeStorageAtLengthRevert (fork := fork) evm offset len hvalue hg
          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
      · have hrev := safeDecodeWordPairRevert hdecode (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckShort_4_64 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeWordPairShort hlong (by omega)) hrev
    · have hrev := safeDecodeWordPairRevert hdecode (by simp)
        (by rw [hlenWord]; exact solcDecodeLenCheckHuge_4_64 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeWordPairHuge (by omega)) hrev
  · have h111 := safeRuntime_block_6090_taken (by simp) hvalue (by jump_dest) hentry
    have hrev := safeRuntime_block_111 (by simp) h111
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getStorageAt` (`getstorageatTransition`). -/
theorem safeGetstorageatRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getstorageatTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeGetstorageatBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

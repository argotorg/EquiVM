import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Storage
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def signedMessagesArgs (key : UInt256) : Store :=
  (∅ : Store).insert "arg0" (wordBytes32Value key)

theorem safeSignedMessagesSource (evm : EVM.State) (key : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (signedMessagesArgs key) signedmessagesTransition.body
      (.returned { contract := contract, locals := signedMessagesArgs key } evm
        (some [.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨7⟩)).toNat)])) := by
  apply uint256GetterBodyReturns evm (signedMessagesArgs key)
    (er := { base := "signedMessages", steps := [.mindex
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))] }) hvalue
  · simp [signedMessagesArgs, signedMessagesRef]
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      signedMessagesRef, signedMessagesArgs,
      evalExpr?, valueToKey?, wordBytes32Value, abiBytes32Width,
      word_toBytesBE_length_32, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (wordLoc (mapSlot (keyValueToWord
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) ⟨7⟩) (.int uint256Int))) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)) = key
      from keyValueToWord_fixedBytes32 key]
    rfl

set_option maxRecDepth 100000 in
theorem safeSignedMessagesTrace {I g s0 σ k C} {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨957⟩ (key :: ⟨974⟩ :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 4 ≤ 1024) :
    RDret safeBytecode g s0 σ (solcSlotWordAt (mapSlot key ⟨7⟩) σ I).toByteArray := by
  obtain ⟨_, _, h974⟩ := safeRuntime_block_957 hov (by jump_dest) h
  have hret := safeReturnWordFromScratch h974 (by simp; omega)
    (solcMappingHashMem_size ⟨7⟩ key) (solcMappingHashMem_read64 ⟨7⟩ key)
  change RDret safeBytecode g s0 σ (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (solcMappingHashMem ⟨7⟩ key)) σ I).toByteArray at hret
  rw [show keccakWord ⟨0⟩ (UInt256.ofNat 64) (solcMappingHashMem ⟨7⟩ key) =
    mapSlot key ⟨7⟩ from solcMappingKeccakSlot ⟨7⟩ key] at hret
  exact hret

set_option maxRecDepth 100000 in
theorem safeSignedmessagesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some signedmessagesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x5a 0xe6 0xbd 0x37 ⟨0x5ae6bd37⟩
    hdispatch signedmessagesSelectorBytes (by decide)
  obtain ⟨k, C, h931⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x5ae6bd37⟩ 1 ⟨931⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h942 := safeRuntime_block_931_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h931
    have h9894 := safeRuntime_block_942 (by simp) (by jump_dest) h942
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · obtain ⟨_, _, h957⟩ := safeDecodeWord h9894 (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hbig hsize) (by jump_dest)
        have hret := safeSignedMessagesTrace h957 (by simp)
        have hbody := safeSignedMessagesSource (initState σ σ₀ (.ofUInt256 g) A I)
          (calldataWord I.calldata 4) hvalue
        refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
        exact reEquivSelectorExecution hdispatch (decodeCalldataBytes32Word hlen hbig) hbody
          (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
            (by simpa [uint256, solcSlotWordAt, initState, Solm.EVM.storageLoad,
              State.lookupAccount] using
                (uint256ReturnEncoding
                  (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨7⟩) σ I))))))
      · have hrev := safeDecodeWordRevert h9894 (by simp)
          (solcDecodeLenCheckShort_4_32 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_bytes32_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeWordRevert h9894 (by simp)
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_bytes32_none_huge (by omega)) hrev
  · have h939 := safeRuntime_block_931_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h931
    have hrev := safeRuntime_block_939 (by simp [safeRuntime_block_931_fallthrough_stack]) h939
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `signedMessages` (`signedmessagesTransition`). -/
theorem safeSignedmessagesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some signedmessagesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeSignedmessagesBodyCore hcode hsize hdispatch

end Benchmarks.Safe

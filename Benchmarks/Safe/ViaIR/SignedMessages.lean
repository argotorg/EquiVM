import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.Blocks.Runtime_028
import Benchmarks.Safe.ViaIR.Blocks.Runtime_029

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def signedMessagesArgs (key : UInt256) : Store :=
  (∅ : Store).insert "arg0" (wordBytes32Value key)

theorem safeSignedMessagesSource (evm : EVM.State) (key : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody fork config contract evm (signedMessagesArgs key) signedmessagesTransition.body
      (.returned { contract := contract, locals := signedMessagesArgs key } evm
        (some [.int (Int.ofNat
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨7⟩)).toNat)])) := by
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
theorem safeSignedMessagesTrace {I g s0 σ k C} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6066⟩ R solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 4 ≤ 1024) :
    RDret fork safeBytecode g s0 σ
      (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨7⟩) σ I).toByteArray := by
  let key := calldataWord I.calldata 4
  let mem := twoWordHashMem key ⟨7⟩ solcFreePtrMem
  have hmem : mem.size = 96 := twoWordHashMem_size_96 key ⟨7⟩ solcFreePtrMem_size
  have hptr : memLoad ⟨64⟩ mem = ⟨128⟩ := mloadFreePtrValue (by rw [hmem]; decide)
    (twoWordHashMem_read64 key ⟨7⟩ solcFreePtrMem_size solcFreePtrMem_read64)
  have hslot : keccakWord ⟨0⟩ ⟨64⟩ mem = mapSlot key ⟨7⟩ :=
    twoWordHashMem_solcMappingSlot ⟨7⟩ key solcFreePtrMem_size
  have hret := safeRuntime_block_6066 hov h
  change RDret fork safeBytecode g s0 σ
    (((solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ mem) σ I).toByteArray.write 0 mem
      (memLoad ⟨64⟩ mem).toNat 32).readWithPadding (memLoad ⟨64⟩ mem).toNat 32) at hret
  rw [hptr, hslot] at hret
  change RDret fork safeBytecode g s0 σ
    ((solcScratchReturnMem mem (solcSlotWordAt (mapSlot key ⟨7⟩) σ I)).readWithPadding
      128 32) at hret
  rw [solcScratchReturnMem_read128 _ hmem] at hret
  exact hret

set_option maxRecDepth 100000 in
theorem safeSignedmessagesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some signedmessagesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x5a 0xe6 0xbd 0x37 ⟨0x5ae6bd37⟩
    hdispatch signedmessagesSelectorBytes (by decide)
  obtain ⟨k, C, h6048⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x5ae6bd37⟩ 8 ⟨6048⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h6054 := safeRuntime_block_6048_fallthrough (by simp) hvalue h6048
    have hlenWord := safeIRArgumentSizeSub hlong hsize
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h6066 := safeRuntime_block_6054_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h6054
        have hret := safeSignedMessagesTrace h6066 (by simp)
        have hbody := safeSignedMessagesSource (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
          (calldataWord I.calldata 4) hvalue
        refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
        exact reEquivSelectorExecution hdispatch (decodeCalldataBytes32Word hlen hbig) hbody
          (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
            (by simpa [uint256, solcSlotWordAt, initState, Stele.EVM.storageLoad,
              State.lookupAccount] using
                (uint256ReturnEncoding
                  (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨7⟩) σ I))))))
      · have h111 := safeRuntime_block_6054_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]
            decide)
          (by jump_dest) h6054
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_bytes32_none_short hlong (by omega))
          (safeRuntime_block_111 (by simp) h111)
    · have h111 := safeRuntime_block_6054_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]
          decide)
        (by jump_dest) h6054
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_bytes32_none_huge (by omega)) (safeRuntime_block_111 (by simp) h111)
  · have h111 := safeRuntime_block_6048_taken (by simp) hvalue (by jump_dest) h6048
    exact reEquivSelectorRevert hcode hdispatch (safeRuntime_block_111 (by simp) h111)
      fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `signedMessages` (`signedmessagesTransition`). -/
theorem safeSignedmessagesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some signedmessagesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeSignedmessagesBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

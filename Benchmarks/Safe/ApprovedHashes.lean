import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Calldata
import Benchmarks.Safe.Storage
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_009

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def approvedHashesArgs (owner key : UInt256) : Store :=
  ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat owner.toNat))).insert
    "arg1" (wordBytes32Value key)

theorem safeApprovedHashesSource (evm : EVM.State) (owner key : UInt256)
    (hcanon : owner.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (approvedHashesArgs owner key)
      approvedhashesTransition.body
      (.returned { contract := contract, locals := approvedHashesArgs owner key } evm
        (some [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (mapSlot key (mapSlot owner ⟨8⟩))).toNat)])) := by
  apply uint256GetterBodyReturns evm (approvedHashesArgs owner key)
    (er := { base := "approvedHashes", steps :=
      [.mindex (.address (AccountAddress.ofNat owner.toNat)),
        .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))] }) hvalue
  · simp [approvedHashesArgs, approvedHashesRef]
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      approvedHashesRef, approvedHashesArgs, evalExpr?, valueToKey?,
      wordBytes32Value, abiBytes32Width, word_toBytesBE_length_32,
      EvalResult.bind, EvalResult.ofOption, bind, pure, Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (wordLoc (mapSlot (keyValueToWord
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) (mapSlot
        (keyValueToWord (.address (AccountAddress.ofNat owner.toNat))) ⟨8⟩)) (.int uint256Int))) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)) = key
      from keyValueToWord_fixedBytes32 key, keyValueToWord_address_of_canonical owner hcanon]
    rfl

theorem safeApprovedHashesMemory (owner key : UInt256) :
    safeRuntime_block_1095_memory (mem := solcFreePtrMem) (x0 := key) (x1 := owner) =
      solcNestedMappingHashMem ⟨8⟩ owner key := by
  change key.toByteArray.write 0 ((keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (solcMappingHashMem ⟨8⟩ owner)).toByteArray.write 0 (solcMappingHashMem ⟨8⟩ owner) 32 32)
    0 32 = _
  rw [show keccakWord ⟨0⟩ (UInt256.ofNat 64) (solcMappingHashMem ⟨8⟩ owner) =
    solcMappingSlot ⟨8⟩ owner from solcMappingKeccakSlot ⟨8⟩ owner]
  rfl

set_option maxRecDepth 100000 in
theorem safeApprovedHashesTrace {I g s0 σ k C} {owner key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨1095⟩ (key :: owner :: ⟨974⟩ :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 7 ≤ 1024) :
    RDret safeBytecode g s0 σ (solcSlotWordAt (mapSlot key (mapSlot owner ⟨8⟩)) σ I).toByteArray
      := by
  obtain ⟨_, _, h974⟩ := safeRuntime_block_1095 hov (by jump_dest) h
  have hstack : safeRuntime_block_1095_stack (ee := I) (mem := solcFreePtrMem) (σ := σ)
      (x0 := key) (x1 := owner) (x2 := ⟨974⟩) (R := R) =
      solcSlotWordAt (mapSlot key (mapSlot owner ⟨8⟩)) σ I :: ⟨974⟩ :: R := by
    change solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_1095_memory (mem := solcFreePtrMem) (x0 := key) (x1 := owner))) σ I ::
      ⟨974⟩ :: R = _
    rw [safeApprovedHashesMemory]
    rw [show keccakWord ⟨0⟩ (UInt256.ofNat 64) (solcNestedMappingHashMem ⟨8⟩ owner key) =
      mapSlot key (mapSlot owner ⟨8⟩) from solcNestedMappingKeccakSlot ⟨8⟩ owner key]
  rw [hstack, safeApprovedHashesMemory] at h974
  exact safeReturnWordFromScratch h974 (by simp; omega)
    (solcNestedMappingHashMem_size ⟨8⟩ owner key) (solcNestedMappingHashMem_read64 ⟨8⟩ owner key)

set_option maxRecDepth 100000 in
theorem safeApprovedhashesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvedhashesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x7d 0x83 0x29 0x74 ⟨0x7d832974⟩
    hdispatch approvedhashesSelectorBytes (by decide)
  obtain ⟨k, C, h1069⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x7d832974⟩ 1 ⟨1069⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1080 := safeRuntime_block_1069_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1069
    have h9112 := safeRuntime_block_1080 (by simp) (by jump_dest) h1080
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_64 hlen hbig hsize
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h1095⟩ := safeDecodeAddressWord h9112 (by simp) hcheck hcanon (by jump_dest)
          have hret := safeApprovedHashesTrace h1095 (by simp)
          have hbody := safeApprovedHashesSource (initState σ σ₀ (.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hcanon hvalue
          refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
          exact reEquivSelectorExecution hdispatch (decodeAddressBytes32 hlen hbig hcanon)
            hbody (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
              (by simpa [uint256, solcSlotWordAt, initState, Solm.EVM.storageLoad,
                State.lookupAccount] using (uint256ReturnEncoding
                (solcSlotWordAt (mapSlot (calldataWord I.calldata 36)
                  (mapSlot (calldataWord I.calldata 4) ⟨8⟩)) σ I))))))
        · have hrev := safeDecodeAddressWordNoncanon h9112 (by simp) hcheck hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeAddressBytes32Noncanon hlen hbig hcanon) hrev
      · have hrev := safeDecodeAddressWordRevert h9112 (by simp)
          (solcDecodeLenCheckShort_4_64 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeAddressBytes32Short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressWordRevert h9112 (by simp)
        (solcDecodeLenCheckHuge_4_64 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeAddressBytes32Huge (by omega)) hrev
  · have h1077 := safeRuntime_block_1069_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1069
    have hrev := safeRuntime_block_1077 (by simp [safeRuntime_block_1069_fallthrough_stack]) h1077
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `approvedHashes` (`approvedhashesTransition`). -/
theorem safeApprovedhashesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvedhashesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeApprovedhashesBodyCore hcode hsize hdispatch

end Benchmarks.Safe

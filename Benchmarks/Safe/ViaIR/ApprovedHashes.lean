import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.Storage
import Benchmarks.Safe.ViaIR.Blocks.Runtime_020

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def approvedHashesArgs (owner key : UInt256) : Store :=
  ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat owner.toNat))).insert
    "arg1" (wordBytes32Value key)

theorem safeApprovedHashesSource (evm : EVM.State) (owner key : UInt256)
    (hcanon : owner.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody fork config contract evm (approvedHashesArgs owner key)
      approvedhashesTransition.body
      (.returned { contract := contract, locals := approvedHashesArgs owner key } evm
        (some [.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
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
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem owner ⟨8⟩ solcFreePtrMem))
      (twoWordHashMem owner ⟨8⟩ solcFreePtrMem)) = mapSlot key (mapSlot owner ⟨8⟩) := by
  rw [show keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem owner ⟨8⟩ solcFreePtrMem) =
    mapSlot owner ⟨8⟩ from twoWordHashMem_solcMappingSlot ⟨8⟩ owner solcFreePtrMem_size]
  exact twoWordHashMem_solcMappingSlot (mapSlot owner ⟨8⟩) key
    (twoWordHashMem_size_96 owner ⟨8⟩ solcFreePtrMem_size)

set_option maxRecDepth 100000 in
theorem safeApprovedHashesTrace {I g s0 σ k C} {owner : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4327⟩ (owner :: solcAddrMask :: ⟨0⟩ :: ⟨64⟩ :: ⟨32⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 6 ≤ 1024) (hcanon : owner.toNat < EVM.addressModulus) :
    RDret fork safeBytecode g s0 σ
      (solcSlotWordAt (mapSlot (calldataWord I.calldata 36) (mapSlot owner ⟨8⟩)) σ I).toByteArray
      := by
  let key := calldataWord I.calldata 36
  let inner := twoWordHashMem owner ⟨8⟩ solcFreePtrMem
  let mem := twoWordHashMem key (keccakWord ⟨0⟩ ⟨64⟩ inner) inner
  have hinner : inner.size = 96 := twoWordHashMem_size_96 owner ⟨8⟩ solcFreePtrMem_size
  have hmem : mem.size = 96 := twoWordHashMem_size_96 _ _ hinner
  have hptr : memLoad ⟨64⟩ mem = ⟨128⟩ := mloadFreePtrValue (by rw [hmem]; decide)
    (twoWordHashMem_read64 _ _ hinner
      (twoWordHashMem_read64 owner ⟨8⟩ solcFreePtrMem_size solcFreePtrMem_read64))
  have hslot : keccakWord ⟨0⟩ ⟨64⟩ mem = mapSlot key (mapSlot owner ⟨8⟩) :=
    safeApprovedHashesMemory owner key
  have hret := safeRuntime_block_4327 hov h
  rw [solcAddrMask_clean hcanon] at hret
  change RDret fork safeBytecode g s0 σ
    (((solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ mem) σ I).toByteArray.write 0 mem
      (memLoad ⟨64⟩ mem).toNat 32).readWithPadding (memLoad ⟨64⟩ mem).toNat 32) at hret
  rw [hptr, hslot] at hret
  change RDret fork safeBytecode g s0 σ
    ((solcScratchReturnMem mem (solcSlotWordAt (mapSlot key (mapSlot owner ⟨8⟩)) σ I)).readWithPadding
      128 32) at hret
  rw [solcScratchReturnMem_read128 _ hmem] at hret
  exact hret

set_option maxRecDepth 100000 in
theorem safeApprovedhashesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvedhashesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x7d 0x83 0x29 0x74 ⟨0x7d832974⟩
    hdispatch approvedhashesSelectorBytes (by decide)
  obtain ⟨k, C, h4287⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x7d832974⟩ 12 ⟨4287⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h4294 := safeRuntime_block_4287_fallthrough (by simp) hvalue h4287
    simp only [safeRuntime_block_4287_fallthrough_stack] at h4294
    have hlenWord := safeIRArgumentSizeSub hlong hsize
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have h4306 := safeRuntime_block_4294_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_64 hlen hbig hsize) h4294
        have h6952 := safeRuntime_block_4306 (by simp) (by jump_dest) h4306
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h4327⟩ := safeDecodeAddress h6952
            (by simp [safeRuntime_block_4306_stack]) hcanon (by jump_dest)
          simp only [safeRuntime_block_4306_stack, safeAddressMask] at h4327
          have hret := safeApprovedHashesTrace h4327 (by simp) hcanon
          have hbody := safeApprovedHashesSource (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hcanon hvalue
          refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
          exact reEquivSelectorExecution hdispatch (decodeAddressBytes32 hlen hbig hcanon)
            hbody (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
              (by simpa [uint256, solcSlotWordAt, initState, Stele.EVM.storageLoad,
                State.lookupAccount] using (uint256ReturnEncoding
                (solcSlotWordAt (mapSlot (calldataWord I.calldata 36)
                  (mapSlot (calldataWord I.calldata 4) ⟨8⟩)) σ I))))))
        · have hrev := safeDecodeAddressNoncanon h6952
            (by simp [safeRuntime_block_4306_stack]) hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeAddressBytes32Noncanon hlen hbig hcanon) hrev
      · have h589 := safeRuntime_block_4294_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_64 hlong (by omega) hsize]
            decide) (by jump_dest) h4294
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeAddressBytes32Short hlong (by omega)) (safeRuntime_block_589 (by simp) h589)
    · have h589 := safeRuntime_block_4294_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_64 (by omega) hsize]
          decide) (by jump_dest) h4294
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeAddressBytes32Huge (by omega)) (safeRuntime_block_589 (by simp) h589)
  · have h589 := safeRuntime_block_4287_taken (by simp) hvalue (by jump_dest) h4287
    exact reEquivSelectorRevert hcode hdispatch (safeRuntime_block_589 (by simp) h589)
      fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `approvedHashes` (`approvedhashesTransition`). -/
theorem safeApprovedhashesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvedhashesTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeApprovedhashesBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

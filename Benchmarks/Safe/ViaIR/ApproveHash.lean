import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.Membership
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_004
import Benchmarks.Safe.ViaIR.Blocks.Runtime_012

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def approveHashArgs (key : UInt256) : Store :=
  (∅ : Store).insert "hashToApprove" (wordBytes32Value key)

def approveHashFrame (key : UInt256) : Frame :=
  { contract := contract, locals := approveHashArgs key }

def approveHashSlot (I : ExecutionEnv) (key : UInt256) : UInt256 :=
  mapSlot key (mapSlot (solcSourceWord I) ⟨8⟩)

def approveHashOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWordAt (mapSlot (solcSourceWord I) ⟨2⟩) σ I) solcAddrMask

theorem safeApproveHashGuard (evm : EVM.State) (key : UInt256) :
    evalExpr? config (approveHashFrame key) evm (neE (.storage (ownersRef sender)) zeroAddr) =
      .ok (.bool (decide (approveHashOwnerWord evm.accountMap evm.executionEnv ≠ ⟨0⟩))) := by
  apply evalAddressNonzero (solcAddrMask_result_canonical _)
  apply evalExpr_storage_scalar_value (er := { base := "owners", steps :=
      [.mindex (.address evm.executionEnv.source)] })
    (loc := addressOffset0Loc (mapSlot (solcSourceWord evm.executionEnv) ⟨2⟩))
  · simp [approveHashFrame, approveHashArgs, ownersRef]
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      ownersRef, sender, evalExpr?, envValue, valueToKey?, EvalResult.bind,
      EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (addrLoc (mapSlot
      (keyValueToWord (.address evm.executionEnv.source)) ⟨2⟩))) = _
    rw [keyValueToWord_address]
    rfl
  · exact storageLocLoad_address_offset0 evm (mapSlot (solcSourceWord evm.executionEnv) ⟨2⟩)

theorem safeAssignApprovedHash (evm : EVM.State) (key : UInt256) :
    assignStorageRef? config (approveHashFrame key) evm .storage
      (approvedHashesRef sender (.var "hashToApprove")) (.int 1) =
      .ok (approveHashFrame key,
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (approveHashSlot evm.executionEnv
          key) ⟨1⟩) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "approvedHashes", steps :=
      [.mindex (.address evm.executionEnv.source),
        .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))] })
    (loc := uint256Loc (approveHashSlot evm.executionEnv key))
  · simp [approveHashFrame, approveHashArgs, approvedHashesRef]
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      approvedHashesRef, sender, approveHashFrame, approveHashArgs, evalExpr?, envValue,
      valueToKey?, wordBytes32Value, abiBytes32Width, word_toBytesBE_length_32,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (wordLoc (mapSlot (keyValueToWord
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)))
      (mapSlot (keyValueToWord (.address evm.executionEnv.source)) ⟨8⟩)) (.int uint256Int))) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)) = key
      from keyValueToWord_fixedBytes32 key, keyValueToWord_address]
    rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm (approveHashSlot evm.executionEnv key) ⟨1⟩

theorem safeApproveHashSource (evm : EVM.State) (key : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (howner : approveHashOwnerWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (approveHashArgs key) approvehashTransition.body
      (.returned (approveHashFrame key)
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner (approveHashSlot evm.executionEnv
          key) ⟨1⟩)
        none) := by
  refine .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [howner] using safeApproveHashGuard evm key))
      (.consNormal (.assign (hperm := Or.inr hperm) (by simp [evalExpr?, pure]) (safeAssignApprovedHash evm key))
        (.consNormal (.emit (hperm := by simpa only [storageStore_executionEnv] using hperm) (vals := [wordBytes32Value key, .address evm.executionEnv.source]) ?_)
          .nil))))
  simp [evalExprs?, evalExpr?, sender, envValue, approveHashFrame, approveHashArgs,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem safeApproveHashSourceStatic (evm : EVM.State) (key : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (howner : approveHashOwnerWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (approveHashArgs key) approvehashTransition.body
      .staticViolation := by
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [howner] using safeApproveHashGuard evm key))
      (.consStatic (.assignStatic (by simp [evalExpr?, pure])
        (safeAssignApprovedHash evm key) hperm))))

theorem safeApproveHashSourceRevert (evm : EVM.State) (key : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (howner : approveHashOwnerWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody fork config contract evm (approveHashArgs key) approvehashTransition.body
      .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [howner] using safeApproveHashGuard evm key))

theorem safeApproveHashSlot (I : ExecutionEnv) (key : UInt256) (mem : ByteArray)
    (hmem : mem.size = 96) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key
      (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem (solcSourceWord I) ⟨8⟩ mem))
      (twoWordHashMem (solcSourceWord I) ⟨8⟩ mem)) = approveHashSlot I key := by
  rw [twoWordHashMemMapSlot (solcSourceWord I) ⟨8⟩ hmem]
  exact twoWordHashMemMapSlot _ _ (twoWordHashMem_size_96 _ _ hmem)

theorem safeApproveHashTrace {I g s0 σ k C aw mem rdata} {key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2420⟩ (key :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hmem : mem.size = 96) (hperm : I.perm = true) :
    RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ (approveHashSlot I key) ⟨1⟩)
      ByteArray.empty := by
  have hret := safeRuntime_block_2420 hov hperm h
  let mem' := twoWordHashMem key
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem (solcSourceWord I) ⟨8⟩ mem))
    (twoWordHashMem (solcSourceWord I) ⟨8⟩ mem)
  change RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) mem') ⟨1⟩) (mem'.readWithPadding 0 0) at hret
  rw [byteArray_readWithPadding_zero, safeApproveHashSlot I key mem hmem] at hret
  exact hret

theorem safeApproveHashTraceStatic {I g s0 σ k C aw mem rdata} {key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2420⟩ (key :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have houter := evm_run h with
    [caller, dup3, genMstore, push1 ⟨8⟩, push1 ⟨32⟩, genMstore,
      push1 ⟨64⟩, dup3, genKeccak256]
  have hstore := evm_run houter with
    [dup2, dup4, genMstore, push1 ⟨32⟩, genMstore, push1 ⟨1⟩,
      push1 ⟨64⟩, dup4, genKeccak256]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeApproveHashTraceRevert {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2485⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  exact safeRuntime_block_2485 (by omega) h

theorem safeApproveHashCheck (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1)) (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (safeRuntime_block_2389_taken_memory (ee := I) (mem := solcFreePtrMem) (x0 := ⟨0⟩))) σ I) =
      approveHashOwnerWord σ I := by
  rw [safeAddressMask]
  change UInt256.land solcAddrMask (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem)) σ I) = _
  rw [twoWordHashMemMapSlot _ _ solcFreePtrMem_size, u256_land_comm]
  rfl

theorem safeApprovehashBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvehashTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xd4 0xd9 0xbd 0xcd ⟨0xd4d9bdcd⟩
    hdispatch approvehashSelectorBytes (by decide)
  obtain ⟨k, C, h2370⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xd4d9bdcd⟩ 19 ⟨2370⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h2377 := safeRuntime_block_2370_fallthrough (by simp) hvalue h2370
    simp only [safeRuntime_block_2370_fallthrough_stack] at h2377
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h2389 := safeRuntime_block_2377_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h2377
        have hdec : config.externalABI.decodeCalldata?
            (approvehashTransition.params.map Param.name)
            (transitionSignature approvehashTransition).paramTypes I.calldata =
            some (approveHashArgs (calldataWord I.calldata 4)) := decodeCalldataBytes32Word hlen
              hbig
        have hcheck := safeApproveHashCheck σ I
        dsimp only [solcSlotWordAt, safeRuntime_block_2389_taken_memory] at hcheck
        by_cases howner : approveHashOwnerWord σ I = ⟨0⟩
        · obtain ⟨_, _, h2485⟩ := safeRuntime_block_2389_taken (by simp)
            (by rw [hcheck, howner]; decide) (by jump_dest) h2389
          have hrev := safeApproveHashTraceRevert h2485
            (by simp [safeRuntime_block_2389_taken_stack])
          have hbody := safeApproveHashSourceRevert (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
            (calldataWord I.calldata 4) hvalue howner
          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
        · obtain ⟨_, _, h2420⟩ := safeRuntime_block_2389_fallthrough (by simp)
            (by rw [hcheck]; exact isZero_eq_zero_of_ne howner) h2389
          cases hperm : I.perm with
          | false =>
              have hstatic := safeApproveHashTraceStatic h2420 (by simp) hperm
              have hbody := safeApproveHashSourceStatic (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hvalue howner hperm
              exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
          | true =>
              have hret := safeApproveHashTrace h2420 (by simp)
                (twoWordHashMem_size_96 (solcSourceWord I) ⟨2⟩ solcFreePtrMem_size) hperm
              have hbody := safeApproveHashSource (fork := fork) (hperm := by assumption) (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hvalue howner
              refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
              exact reEquivSelectorExecution hdispatch hdec hbody
                (.success hsuccess rfl (by simp only [storageStore_accountMap]; rfl)
                  (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
      · have h589 := safeRuntime_block_2377_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]
            decide) (by jump_dest) h2377
        have hrev := safeRuntime_block_589 (by simp) h589
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_bytes32_none_short hlong (by omega)) hrev
    · have h589 := safeRuntime_block_2377_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]
          decide) (by jump_dest) h2377
      have hrev := safeRuntime_block_589 (by simp) h589
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_bytes32_none_huge (by omega)) hrev
  · have h589 := safeRuntime_block_2370_taken (by simp) hvalue (by jump_dest) h2370
    have hrev := safeRuntime_block_589 (by simp) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `approveHash` (`approvehashTransition`). -/
theorem safeApprovehashRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvehashTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeApprovehashBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Membership
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_010
import Benchmarks.Safe.Blocks.Runtime_011
import Benchmarks.Safe.Blocks.Runtime_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

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
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveHashSlot evm.executionEnv
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
    (howner : approveHashOwnerWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (approveHashArgs key) approvehashTransition.body
      (.returned (approveHashFrame key)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveHashSlot evm.executionEnv
          key) ⟨1⟩)
        none) := by
  refine .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [howner] using safeApproveHashGuard evm key))
      (.consNormal (.assign (by simp [evalExpr?, pure]) (safeAssignApprovedHash evm key))
        (.consNormal (.emit (vals := [wordBytes32Value key, .address evm.executionEnv.source]) ?_)
          .nil))))
  simp [evalExprs?, evalExpr?, sender, envValue, approveHashFrame, approveHashArgs,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem safeApproveHashSourceStatic (evm : EVM.State) (key : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (howner : approveHashOwnerWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (approveHashArgs key) approvehashTransition.body
      .staticViolation := by
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [howner] using safeApproveHashGuard evm key))
      (.consStatic (.assignStatic (by simp [evalExpr?, pure])
        (safeAssignApprovedHash evm key) hperm))))

theorem safeApproveHashSourceRevert (evm : EVM.State) (key : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (howner : approveHashOwnerWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (approveHashArgs key) approvehashTransition.body
      .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [howner] using safeApproveHashGuard evm key))

theorem safeApproveHashSlot (I : ExecutionEnv) (key : UInt256) (mem : ByteArray)
    (hmem : mem.size = 96) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_5240_memory (ee := I) (mem := mem) (x0 := key)) = approveHashSlot I key
        := by
  change keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem (solcSourceWord I) ⟨8⟩ mem))
    (twoWordHashMem (solcSourceWord I) ⟨8⟩ mem)) = _
  rw [twoWordHashMemMapSlot (solcSourceWord I) ⟨8⟩ hmem]
  exact twoWordHashMemMapSlot _ _ (twoWordHashMem_size_96 _ _ hmem)

theorem safeApproveHashTrace {I g s0 σ k C aw mem rdata} {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5240⟩ (key :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hmem : mem.size = 96) (hperm : I.perm = true) :
    RDret safeBytecode g s0 (sstoreAccountMap I.codeOwner σ (approveHashSlot I key) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, h664⟩ := safeRuntime_block_5240 hov hperm (by jump_dest) h
  have hret := safeRuntime_block_664 (by simp [safeRuntime_block_5240_stack]; omega) h664
  change RDret safeBytecode g s0 (sstoreAccountMap I.codeOwner σ
    (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_5240_memory (ee := I) (mem := mem) (x0 := key))) ⟨1⟩)
    ByteArray.empty at hret
  rwa [safeApproveHashSlot I key mem hmem] at hret

theorem safeApproveHashTraceStatic {I g s0 σ k C aw mem rdata} {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5240⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hperm : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  have hcaller := evm_run h with [jumpdest, caller, push0, dup2, dup2, genMstore]
  have houter := evm_run hcaller with
    [push1 ⟨8⟩, push1 ⟨32⟩, swap1, dup2, genMstore, push1 ⟨64⟩, dup1, dup4, genKeccak256]
  have hinner := evm_run houter with
    [dup6, dup5, genMstore, swap1, swap2, genMstore, dup1, dup3, genKeccak256]
  have hstore := evm_run hinner with [push1 ⟨1⟩, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeApproveHashTraceRevert {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5224⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h6898 := safeRuntime_block_5224 (by omega) (by jump_dest) h
  exact safeRuntime_block_6898 (by simp; omega) h6898

theorem safeApproveHashCheck (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1)) (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (safeRuntime_block_5195_taken_memory (ee := I) (mem := solcFreePtrMem))) σ I) =
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
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xd4 0xd9 0xbd 0xcd ⟨0xd4d9bdcd⟩
    hdispatch approvehashSelectorBytes (by decide)
  obtain ⟨k, C, h1315⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xd4d9bdcd⟩ 0 ⟨1315⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1326 := safeRuntime_block_1315_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1315
    have h9894 := safeRuntime_block_1326 (by simp) (by jump_dest) h1326
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · obtain ⟨_, _, h1341⟩ := safeDecodeWord h9894 (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hbig hsize) (by jump_dest)
        have h5195 := safeRuntime_block_1341 (by simp) (by jump_dest) h1341
        have hdec : decodeCalldataWithMode config.abiDecodeMode
            (approvehashTransition.params.map Param.name)
            (transitionSignature approvehashTransition).paramTypes I.calldata =
            some (approveHashArgs (calldataWord I.calldata 4)) := decodeCalldataBytes32Word hlen
              hbig
        by_cases howner : approveHashOwnerWord σ I = ⟨0⟩
        · obtain ⟨_, _, h5224⟩ := safeRuntime_block_5195_fallthrough (by simp)
            ((safeApproveHashCheck σ I).trans howner) h5195
          have hrev := safeApproveHashTraceRevert h5224 (by simp)
          have hbody := safeApproveHashSourceRevert (initState σ σ₀ (.ofUInt256 g) A I)
            (calldataWord I.calldata 4) hvalue howner
          exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
        · obtain ⟨_, _, h5240⟩ := safeRuntime_block_5195_taken (by simp)
            (fun he ↦ howner ((safeApproveHashCheck σ I).symm.trans he)) (by jump_dest) h5195
          cases hperm : I.perm with
          | false =>
              have hstatic := safeApproveHashTraceStatic h5240 (by simp) hperm
              have hbody := safeApproveHashSourceStatic (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hvalue howner hperm
              exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
          | true =>
              have hret := safeApproveHashTrace h5240 (by simp)
                (twoWordHashMem_size_96 (solcSourceWord I) ⟨2⟩ solcFreePtrMem_size) hperm
              have hbody := safeApproveHashSource (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hvalue howner
              refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
              exact reEquivSelectorExecution hdispatch hdec hbody
                (.success hsuccess rfl (by simp only [storageStore_accountMap]; rfl)
                  (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
      · have hrev := safeDecodeWordRevert h9894 (by simp)
          (solcDecodeLenCheckShort_4_32 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_bytes32_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeWordRevert h9894 (by simp)
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_bytes32_none_huge (by omega)) hrev
  · have h1323 := safeRuntime_block_1315_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1315
    have hrev := safeRuntime_block_1323 (by simp [safeRuntime_block_1315_fallthrough_stack]) h1323
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `approveHash` (`approvehashTransition`). -/
theorem safeApprovehashRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvehashTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeApprovehashBodyCore hcode hsize hdispatch

end Benchmarks.Safe

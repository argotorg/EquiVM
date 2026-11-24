import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Membership
import Benchmarks.Safe.ViaIR.Routines
import Benchmarks.Safe.ViaIR.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def isOwnerArgs (key : UInt256) : Store :=
  (∅ : Store).insert "owner" (.address (AccountAddress.ofNat key.toNat))

theorem safeIsOwnerSource (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody fork config contract evm (isOwnerArgs key) isownerTransition.body
      (.returned { contract := contract, locals := isOwnerArgs key } evm
        (some [.bool (addressMembership key (UInt256.land
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨2⟩))
          solcAddrMask))])) := by
  apply nonpayableReturnExprBodyReturns hvalue
  apply evalAddressMembership hcanon (solcAddrMask_result_canonical _)
  · simp [isOwnerArgs, evalExpr?, EvalResult.ofOption]
  · apply evalExpr_storage_scalar_value (er := { base := "owners", steps :=
        [.mindex (.address (AccountAddress.ofNat key.toNat))] })
      (loc := addressOffset0Loc (mapSlot key ⟨2⟩))
    · simp [isOwnerArgs, ownersRef]
    · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        ownersRef, isOwnerArgs, evalExpr?, valueToKey?, EvalResult.bind,
        EvalResult.ofOption, bind, pure]
    · rfl
    · rfl
    · change some (StorageAddr.leaf (addrLoc (mapSlot
        (keyValueToWord (.address (AccountAddress.ofNat key.toNat))) ⟨2⟩))) = _
      rw [keyValueToWord_address_of_canonical key hcanon]
      rfl
    · exact storageLocLoad_address_offset0 evm (mapSlot key ⟨2⟩)

set_option maxRecDepth 100000 in
theorem safeIsOwnerTrace {I g s0 σ k C} {key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6420⟩ (key :: solcAddrMask :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 7 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus) :
    RDret fork safeBytecode g s0 σ (addressMembership key
      (UInt256.land (solcSlotWordAt (mapSlot key ⟨2⟩) σ I) solcAddrMask)).toUInt256.toByteArray := by
  by_cases hs : key = ⟨1⟩
  · have h6432 := safeRuntime_block_6420_fallthrough (by omega)
      (by rw [solcAddrMask_clean hcanon, hs]; decide) h
    simp only [safeRuntime_block_6420_fallthrough_stack, solcAddrMask_clean hcanon, hs] at h6432
    have hret := safeReturnIsZeroFromScratch h6432 (by simp; omega)
      solcFreePtrMem_size solcFreePtrMem_read64
    simpa [addressMembership, hs] using hret
  · have heq : UInt256.eq key (UInt256.ofNat 1) = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he))
    have h6444 := safeRuntime_block_6420_taken (by omega)
      (by rw [solcAddrMask_clean hcanon, heq]; decide) (by jump_dest) h
    simp only [safeRuntime_block_6420_taken_stack, solcAddrMask_clean hcanon] at h6444
    obtain ⟨_, _, h6432⟩ := safeRuntime_block_6444 (by omega) (by jump_dest) h6444
    simp only [safeRuntime_block_6444_stack, safeRuntime_block_6444_memory,
      safeAddressMask] at h6432
    change RD fork safeBytecode I g s0 ⟨6432⟩
      (UInt256.isZero (UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key ⟨2⟩ solcFreePtrMem)) σ I)
        solcAddrMask) :: ⟨32⟩ :: R) (twoWordHashMem key ⟨2⟩ solcFreePtrMem) _ _ σ _ _ at h6432
    rw [twoWordHashMemMapSlot key ⟨2⟩ solcFreePtrMem_size] at h6432
    have hret := safeReturnIsZeroFromScratch h6432 (by simp; omega)
      (twoWordHashMem_size_96 key ⟨2⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 key ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    rw [normalizedNonzeroWord] at hret
    simpa [addressMembership, hs] using hret

set_option maxRecDepth 100000 in
theorem safeIsownerBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some isownerTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x2f 0x54 0xbf 0x6e ⟨0x2f54bf6e⟩
    hdispatch isownerSelectorBytes (by decide)
  obtain ⟨k, C, h6387⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x2f54bf6e⟩ 4 ⟨6387⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h6393 := safeRuntime_block_6387_fallthrough (by simp) hvalue h6387
    have hlenWord := safeIRArgumentSizeSub hlong hsize
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h6405 := safeRuntime_block_6393_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h6393
        have h6952 := safeRuntime_block_6405 (by simp) (by jump_dest) h6405
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h6420⟩ := safeDecodeAddress h6952
            (by simp [safeRuntime_block_6405_stack]) hcanon (by jump_dest)
          simp only [safeRuntime_block_6405_stack, safeAddressMask] at h6420
          have hret := safeIsOwnerTrace h6420 (by simp) hcanon
          have hbody := safeIsOwnerSource (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
            (calldataWord I.calldata 4) hcanon hvalue
          refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
          exact reEquivSelectorExecution hdispatch (decodeCalldata_address_ok hlen hbig hcanon)
            hbody (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
              (by simpa [bool, solcSlotWordAt, initState, Stele.EVM.storageLoad,
                State.lookupAccount] using (boolReturnEncoding (addressMembership
                (calldataWord I.calldata 4) (UInt256.land
                  (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨2⟩) σ I) solcAddrMask)))))))
        · have hrev := safeDecodeAddressNoncanon h6952
            (by simp [safeRuntime_block_6405_stack]) hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hcanon) hrev
      · have h111 := safeRuntime_block_6393_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]
            decide) (by jump_dest) h6393
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega))
          (safeRuntime_block_111 (by simp) h111)
    · have h111 := safeRuntime_block_6393_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]
          decide) (by jump_dest) h6393
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) (safeRuntime_block_111 (by simp) h111)
  · have h111 := safeRuntime_block_6387_taken (by simp) hvalue (by jump_dest) h6387
    exact reEquivSelectorRevert hcode hdispatch (safeRuntime_block_111 (by simp) h111)
      fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `isOwner` (`isownerTransition`). -/
theorem safeIsownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some isownerTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeIsownerBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR

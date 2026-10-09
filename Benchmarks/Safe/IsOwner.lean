import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Membership
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def isOwnerArgs (key : UInt256) : Store :=
  (∅ : Store).insert "owner" (.address (AccountAddress.ofNat key.toNat))

theorem safeIsOwnerSource (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (isOwnerArgs key) isownerTransition.body
      (.returned { contract := contract, locals := isOwnerArgs key } evm
        (some [.bool (addressMembership key (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨2⟩))
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
    (h : RD safeBytecode I g s0 ⟨2859⟩ (key :: ⟨759⟩ :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 7 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus) :
    RDret safeBytecode g s0 σ (addressMembership key
      (UInt256.land (solcSlotWordAt (mapSlot key ⟨2⟩) σ I) solcAddrMask)).toUInt256.toByteArray :=
        by
  by_cases hs : key = ⟨1⟩
  · have h2907 := safeRuntime_block_2859_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hcanon, hs]; decide) (by jump_dest) h
    have h759 := safeRuntime_block_2907 (by omega) (by jump_dest) h2907
    simp only [safeRuntime_block_2907_stack, hs, safeAddressMask,
      show UInt256.land (⟨1⟩ : UInt256) solcAddrMask = ⟨1⟩ by decide] at h759
    have hret := safeReturnBoolFromScratch (b := false) h759 (by omega)
      solcFreePtrMem_size solcFreePtrMem_read64
    simpa [addressMembership, hs] using hret
  · have h2879 := safeRuntime_block_2859_fallthrough (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hcanon]
          exact uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he).symm)) h
    obtain ⟨_, _, h2907⟩ := safeRuntime_block_2879 (by simp; omega) h2879
    have h759 := safeRuntime_block_2907 (by omega) (by jump_dest) h2907
    simp only [safeRuntime_block_2907_stack, safeRuntime_block_2879_memory,
      safeAddressMask, solcAddrMask_clean_left hcanon] at h759
    change RD safeBytecode I g s0 ⟨759⟩
      (UInt256.isZero (UInt256.isZero (UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key ⟨2⟩ solcFreePtrMem)) σ I)
        solcAddrMask)) :: R) (twoWordHashMem key ⟨2⟩ solcFreePtrMem) _ _ σ _ _ at h759
    rw [twoWordHashMemMapSlot key ⟨2⟩ solcFreePtrMem_size, normalizedNonzeroWord] at h759
    have hret := safeReturnBoolFromScratch h759 (by omega)
      (twoWordHashMem_size_96 key ⟨2⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 key ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    simpa [addressMembership, hs] using hret

set_option maxRecDepth 100000 in
theorem safeIsownerBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some isownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x2f 0x54 0xbf 0x6e ⟨0x2f54bf6e⟩
    hdispatch isownerSelectorBytes (by decide)
  obtain ⟨k, C, h780⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x2f54bf6e⟩ 1 ⟨780⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h791 := safeRuntime_block_780_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h780
    have h9591 := safeRuntime_block_791 (by simp) (by jump_dest) h791
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_32 hlen hbig hsize
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h806⟩ := safeDecodeAddress h9591 (by simp) hcheck hcanon (by jump_dest)
          have h2859 := safeRuntime_block_806 (by simp) (by jump_dest) h806
          have hret := safeIsOwnerTrace h2859 (by simp) hcanon
          have hbody := safeIsOwnerSource (initState σ σ₀ (.ofUInt256 g) A I)
            (calldataWord I.calldata 4) hcanon hvalue
          refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
          exact reEquivSelectorExecution hdispatch (decodeCalldata_address_ok hlen hbig hcanon)
            hbody (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
              (by simpa [bool, solcSlotWordAt, initState, Solm.EVM.storageLoad,
                State.lookupAccount] using (boolReturnEncoding (addressMembership
                (calldataWord I.calldata 4) (UInt256.land
                  (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨2⟩) σ I) solcAddrMask)))))))
        · have hrev := safeDecodeAddressNoncanon h9591 (by simp) hcheck hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hcanon) hrev
      · have hrev := safeDecodeAddressRevert h9591 (by simp)
          (solcDecodeLenCheckShort_4_32 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressRevert h9591 (by simp)
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have h788 := safeRuntime_block_780_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h780
    have hrev := safeRuntime_block_788 (by simp [safeRuntime_block_780_fallthrough_stack]) h788
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `isOwner` (`isownerTransition`). -/
theorem safeIsownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some isownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeIsownerBodyCore hcode hsize hdispatch

end Benchmarks.Safe

import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.ModuleMembership
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def isModuleEnabledArgs (key : UInt256) : Store :=
  (∅ : Store).insert "module" (.address (AccountAddress.ofNat key.toNat))

theorem safeIsModuleEnabledSource (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (isModuleEnabledArgs key) ismoduleenabledTransition.body
      (.returned { contract := contract, locals := isModuleEnabledArgs key } evm
        (some [.bool (addressMembership key (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨1⟩))
          solcAddrMask))])) := by
  apply nonpayableReturnExprBodyReturns hvalue
  apply evalAddressMembership hcanon (solcAddrMask_result_canonical _)
  · simp [isModuleEnabledArgs, evalExpr?, EvalResult.ofOption]
  · apply evalExpr_storage_scalar_value (er := { base := "modules", steps :=
        [.mindex (.address (AccountAddress.ofNat key.toNat))] })
      (loc := addressOffset0Loc (mapSlot key ⟨1⟩))
    · simp [isModuleEnabledArgs, modulesRef]
    · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        modulesRef, isModuleEnabledArgs, evalExpr?, valueToKey?, EvalResult.bind,
        EvalResult.ofOption, bind, pure]
    · rfl
    · rfl
    · change some (StorageAddr.leaf (addrLoc (mapSlot
        (keyValueToWord (.address (AccountAddress.ofNat key.toNat))) ⟨1⟩))) = _
      rw [keyValueToWord_address_of_canonical key hcanon]
      rfl
    · exact storageLocLoad_address_offset0 evm (mapSlot key ⟨1⟩)

set_option maxRecDepth 100000 in
theorem safeIsModuleEnabledTrace {I g s0 σ k C} {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2802⟩ (key :: ⟨759⟩ :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 7 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus) :
    RDret safeBytecode g s0 σ (addressMembership key
      (UInt256.land (solcSlotWordAt (mapSlot key ⟨1⟩) σ I) solcAddrMask)).toUInt256.toByteArray :=
        by
  obtain ⟨mem', aw', k', C', hret, hmem, hread⟩ := safeModuleMembership h hov hcanon
    solcFreePtrMem_size solcFreePtrMem_read64 (by jump_dest)
  exact safeReturnBoolFromScratch hret (by omega) hmem hread

set_option maxRecDepth 100000 in
theorem safeIsmoduleenabledBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some ismoduleenabledTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x2d 0x9a 0xd5 0x3d ⟨0x2d9ad53d⟩
    hdispatch ismoduleenabledSelectorBytes (by decide)
  obtain ⟨k, C, h728⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x2d9ad53d⟩ 0 ⟨728⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h739 := safeRuntime_block_728_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h728
    have h9591 := safeRuntime_block_739 (by simp) (by jump_dest) h739
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_32 hlen hbig hsize
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h754⟩ := safeDecodeAddress h9591 (by simp) hcheck hcanon (by jump_dest)
          have h2802 := safeRuntime_block_754 (by simp) (by jump_dest) h754
          have hret := safeIsModuleEnabledTrace h2802 (by simp) hcanon
          have hbody := safeIsModuleEnabledSource (initState σ σ₀ (.ofUInt256 g) A I)
            (calldataWord I.calldata 4) hcanon hvalue
          refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
          exact reEquivSelectorExecution hdispatch (decodeCalldata_address_ok hlen hbig hcanon)
            hbody (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
              (by simpa [bool, solcSlotWordAt, initState, Solm.EVM.storageLoad,
                State.lookupAccount] using (boolReturnEncoding (addressMembership
                (calldataWord I.calldata 4) (UInt256.land
                  (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I) solcAddrMask)))))))
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
  · have h736 := safeRuntime_block_728_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h728
    have hrev := safeRuntime_block_736 (by simp [safeRuntime_block_728_fallthrough_stack]) h736
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `isModuleEnabled` (`ismoduleenabledTransition`). -/
theorem safeIsmoduleenabledRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some ismoduleenabledTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeIsmoduleenabledBodyCore hcode hsize hdispatch

end Benchmarks.Safe

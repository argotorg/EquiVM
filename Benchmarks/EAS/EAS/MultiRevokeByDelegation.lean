import Benchmarks.EAS.EAS.MultiDelegatedRevokeRun
import Benchmarks.EAS.EAS.DelegatedBatchArrayDecode

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easMultiRevokeByDelegationBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 15)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 15) rfl hsel
  have hd : dispatchMsg contract I.calldata = some multiRevokeByDelegationTransition := by
    apply easDispatch_multiRevokeByDelegation (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hplans : easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = [DelegatedBatchSite.revoke.plan] :=
    easPlans_of_selector hsel (by native_decide)
  obtain ⟨k,C,rd⟩ := easReachMultiRevokeByDelegationBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases h36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2^255+4
    · have r1 := easBlocks.eas_block_1182_fallthrough (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_32 h36 hbig hsize) rd
      have hdec := decodeDelegatedBatch .revoke "multiDelegatedRequests" easPlanTable h36 hbig hsize hplans
      have hhead := easDelegatedBatchArrayDecode v .revoke (by simp) hsize r1
      by_cases hv : wordArrayValid I.calldata
      · rw [if_pos hv] at hhead hdec
        obtain ⟨a2,k2,C2,r2⟩ := hhead
        let args := (∅ : Store).insert "multiDelegatedRequests" (.array
          (delegatedBatchValues .revoke I.calldata (UInt256.ofNat (wordArrayOffset I.calldata+36)) (wordArrayLength I.calldata)))
        let L1 := easEntryLocals args I.calldata
        have hprefix := easPayableEntryPrefix_ok (fork := fork) (cfg := config)
          (frame := {contract := contract,locals := args,immutables := immStore v})
          (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hsz hsize (by change I.calldata.size-4 < 2^255; omega)
        have hreq : L1.get? "multiDelegatedRequests" = some (.array
            (delegatedBatchValues .revoke I.calldata (UInt256.ofNat (wordArrayOffset I.calldata+36)) (wordArrayLength I.calldata))) := by
          simp (disch := decide) only [L1,easEntryLocals,store_get_ne]
          exact store_get_self _ _ _
        have hheap : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat 224)) := by
          simp (disch := decide) only [L1,easEntryLocals,store_get_ne,store_get_self]
          rfl
        have hrun := multiDelegatedRevokePublicRun v (by simp) SourceState.init hv hreq hheap r2
        rcases hrun with ⟨L2,e2,σ2,hsrc,hs2,hret⟩ | ⟨hsrc,hrev⟩ | ⟨hsrc,hstatic⟩
        · refine RDret.reEquivExecutionGen (retVal := none)
            (cs := {contract := contract,locals := L2,immutables := immStore v}) (evm'' := e2)
            hcode hret hd hdec ?_ hs2.accounts (returnEquiv.fallthrough (dvs := []) rfl (by native_decide) (by native_decide))
          rw [multiDelegatedRevoke_body]
          apply ExecFuncBody.execBlockOK
          simpa only [multiDelegatedRevokeLoop,List.append_assoc] using execBlock_append hprefix hsrc
        · refine RDrev.reEquivExecutionRevert hcode hrev hd hdec ?_
          rw [multiDelegatedRevoke_body]
          apply ExecFuncBody.execBlockRevert
          simpa only [multiDelegatedRevokeLoop,List.append_assoc] using execBlock_append hprefix hsrc
        · refine RDstatic.reEquivStaticHalt hcode hstatic hd hdec ?_
          rw [multiDelegatedRevoke_body]
          apply ExecFuncBody.execBlockStatic
          simpa only [multiDelegatedRevokeLoop,List.append_assoc] using execBlock_append hprefix hsrc
      · rw [if_neg hv] at hhead hdec
        exact RDrev.reEquivDecodingFailed hcode hhead hd hdec
    · have r1 := easBlocks.eas_block_1182_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]; exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) r1
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (decodeSolc_none_head ["multiDelegatedRequests"] [.dynamicArray DelegatedBatchSite.revoke.abi] easPlanTable 32 rfl (by native_decide) hsz
          (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true) (solcDecodeLenCheckHuge_4_32 (by omega) hsize)))
  · have r1 := easBlocks.eas_block_1182_taken (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by decide))
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) r1
    exact RDrev.reEquivDecodingFailed hcode hr hd
      (decodeSolc_none_head ["multiDelegatedRequests"] [.dynamicArray DelegatedBatchSite.revoke.abi] easPlanTable 32 rfl (by native_decide) hsz
        (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true) (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize)))

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.AttestPublicRun
import Benchmarks.EAS.EAS.AttestPrelude
import Benchmarks.EAS.EAS.CalldataPlans

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easAttestBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 20)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 20) rfl hsel
  have hd : dispatchMsg contract I.calldata = some attestTransition := by
    apply easDispatch_attest (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hplans : easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = [attestRequestPlan] :=
    easPlans_of_selector hsel (by native_decide)
  obtain ⟨k,C,rd⟩ := easReachAttestBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases h36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2^255+4
    · have rd1 := easBlocks.eas_block_407_fallthrough (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_32 h36 hbig hsize) rd
      have hdec := decodeAttest "request" easPlanTable hsz
        (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false) (solcDecodeLenCheckOk_4_32 h36 hbig hsize)) hplans
      have hhead := easAttestHead v (by simp) rd1
      by_cases hh : attestHeadValid I.calldata
      · obtain ⟨a2,k2,C2,r2⟩ := hhead.1 hh
        have hp := easAttestPrepare (heap := UInt256.ofNat 224) v (by simp) rfl (by decide) (by decide)
          (by native_decide) r2
        by_cases href : requestReferenceValid I.calldata (attestRoot I.calldata) (attestRoot I.calldata+UInt256.ofNat 32)
        · obtain ⟨a3,k3,C3,r3⟩ := hp.1 href
          by_cases hdata : requestDataValid I.calldata (attestRequestData I.calldata (attestRoot I.calldata))
          · have hv : attestValid I.calldata := ⟨hh.1,hh.2,href,hdata⟩
            rw [if_pos hv] at hdec
            let args := (∅ : Store).insert "request" (attestRequestValue I.calldata (attestRoot I.calldata))
            have hprefix := attestPublicPrefixSource (fork := fork) (L := args) (imms := immStore v)
              (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hsz hsize (by change I.calldata.size-4 < 2^255; omega)
            have hreq : (attestPublicPrefixLocals args I.calldata).get? "request" =
                some (attestRequestValue I.calldata (attestRoot I.calldata)) := by
              simp (disch := decide) only [attestPublicPrefixLocals,allocateBlockLocals_get,easEntryLocals,store_get_ne]
              exact store_get_self _ _ _
            have hheap : (attestPublicPrefixLocals args I.calldata).get? "$EAS.freeMemory" = some (.int (Int.ofNat 480)) := by
              simp only [attestPublicPrefixLocals,allocateBlockLocals,unpackHeapLocals,store_get_self]
            have hrun := attestPublicRun v (by simp) SourceState.init hbig hdata hreq hheap r3
            rcases hrun with ⟨L',evm',σ',uid,hsrc,hstate,hret⟩ | ⟨hsrc,hrev⟩ | ⟨hsrc,hstatic⟩
            · refine RDret.reEquivExecutionGen (retVal := some [wordBytes32Value uid])
                (cs := {contract := contract,locals := L',immutables := immStore v}) (evm'' := evm')
                hcode hret hd hdec ?_ hstate.accounts (returnEquiv_of_encode (bytes32ReturnEncoding uid))
              rw [attestPublic_body]
              apply ExecFuncBody.execBlockRet
              simpa only [attestPublicTail,List.append_assoc] using execBlock_append hprefix hsrc
            · refine RDrev.reEquivExecutionRevert hcode hrev hd hdec ?_
              rw [attestPublic_body]
              apply ExecFuncBody.execBlockRevert
              simpa only [attestPublicTail,List.append_assoc] using execBlock_append hprefix hsrc
            · refine RDstatic.reEquivStaticHalt hcode hstatic hd hdec ?_
              rw [attestPublic_body]
              apply ExecFuncBody.execBlockStatic
              simpa only [attestPublicTail,List.append_assoc] using execBlock_append hprefix hsrc
          · rw [if_neg (fun h => hdata h.2.2.2)] at hdec
            have hr := easCopyRequest_branches (heap := UInt256.ofNat 480) v (by simp) (by decide) (by decide)
              attestPublicArrayMemory_facts.2.2.1 (by rw [easPatchedValidJumps v]; jump_dest) r3
            exact RDrev.reEquivDecodingFailed hcode (hr.2 (fun h => hdata (requestCopyRunValid_data h))) hd hdec
        · rw [if_neg (fun h => href h.2.2.1)] at hdec
          exact RDrev.reEquivDecodingFailed hcode (hp.2 href) hd hdec
      · rw [if_neg (fun h => hh ⟨h.1,h.2.1⟩)] at hdec
        exact RDrev.reEquivDecodingFailed hcode (hhead.2 hh) hd hdec
    · have r1 := easBlocks.eas_block_407_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]; exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) r1
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (decodeSolc_none_head ["request"] [attestRequestABI] easPlanTable 32 rfl (by native_decide) hsz
          (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true) (solcDecodeLenCheckHuge_4_32 (by omega) hsize)))
  · have r1 := easBlocks.eas_block_407_taken (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by decide))
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) r1
    exact RDrev.reEquivDecodingFailed hcode hr hd
      (decodeSolc_none_head ["request"] [attestRequestABI] easPlanTable 32 rfl (by native_decide) hsz
        (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true) (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize)))

end Benchmarks.EAS.EAS

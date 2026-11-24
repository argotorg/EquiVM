import Benchmarks.EAS.EAS.RevokePublicRun
import Benchmarks.EAS.EAS.Dispatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easRevokeBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 4)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 4) rfl hsel
  have hd : dispatchMsg contract I.calldata = some revokeTransition := by
    apply easDispatch_revoke (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hplans : easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = [] :=
    easPlans_of_selector hsel (by native_decide)
  obtain ⟨k,C,rd⟩ := easReachRevokeBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : 100 ≤ I.calldata.size ∧ I.calldata.size < 2^255+4
  · have hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
      solcCalldataStaticLenCheckOk (words := 3) hv.1 hv.2 hsize
    have hdec := decodeRevoke "request" easPlanTable hsize hv.1
      (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := false) hcheck) hplans
    have r1 := easBlocks.eas_block_3545_fallthrough (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact hcheck) rd
    obtain ⟨a2,k2,C2,r2⟩ := easRevokePublicPrepare v (by simp) hsize hv.1 hv.2 r1
    let args := (∅ : Store).insert "request" (revokeRequestValue I.calldata)
    have hprefix := revokePublicPrefixSource (fork := fork) (L := args) (imms := immStore v)
      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hsz hsize (by change I.calldata.size-4 < 2^255; omega)
    have hreq : (revokePublicPrefixLocals args I.calldata).get? "request" = some (revokeRequestValue I.calldata) := by
      simp (disch := decide) only [revokePublicPrefixLocals,allocateBlockLocals_get,easEntryLocals,store_get_ne]
      exact store_get_self _ _ _
    have hheap : (revokePublicPrefixLocals args I.calldata).get? "$EAS.freeMemory" = some (.int (Int.ofNat 416)) := by
      simp only [revokePublicPrefixLocals,allocateBlockLocals,unpackHeapLocals,store_get_self]
    have hrun := revokePublicRun v (by simp) SourceState.init hreq hheap hsize r2
    rcases hrun with ⟨L',evm',σ',hsrc,hs,hret⟩ | ⟨hsrc,hrev⟩ | ⟨hsrc,hstatic⟩
    · refine RDret.reEquivExecutionGen (retVal := none)
        (cs := {contract := contract,locals := L',immutables := immStore v}) (evm'' := evm')
        hcode hret hd hdec ?_ hs.accounts ?_
      · rw [revokePublic_body]
        apply ExecFuncBody.execBlockOK
        simpa only [revokePublicTail,List.append_assoc] using execBlock_append hprefix hsrc
      · exact returnEquiv.fallthrough (dvs := []) rfl (by native_decide) (by native_decide)
    · refine RDrev.reEquivExecutionRevert hcode hrev hd hdec ?_
      rw [revokePublic_body]
      apply ExecFuncBody.execBlockRevert
      simpa only [revokePublicTail,List.append_assoc] using execBlock_append hprefix hsrc
    · refine RDstatic.reEquivStaticHalt hcode hstatic hd hdec ?_
      rw [revokePublic_body]
      apply ExecFuncBody.execBlockStatic
      simpa only [revokePublicTail,List.append_assoc] using execBlock_append hprefix hsrc
  · have hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
      by_cases h100 : 100 ≤ I.calldata.size
      · exact solcCalldataStaticLenCheckHuge (words := 3) (by omega) hsize (by decide)
      · exact solcCalldataStaticLenCheckShort (words := 3) hsz (by omega) hsize (by decide)
    have r1 := easBlocks.eas_block_3545_taken (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact ne_of_eq_of_ne hcheck (by decide)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) r1
    exact RDrev.reEquivDecodingFailed hcode hr hd
      (decodeSolc_none_head ["request"] [revokeRequestABI] easPlanTable 96 rfl (by native_decide) hsz
        (solcSLT_sub4_of_check (need := ⟨96⟩) (bit := true) hcheck))

end Benchmarks.EAS.EAS

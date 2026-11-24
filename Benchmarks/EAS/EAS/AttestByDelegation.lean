import Benchmarks.EAS.EAS.DelegatedAttestRun
import Benchmarks.EAS.EAS.DelegatedAttestEntry
import Benchmarks.EAS.EAS.Dispatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easAttestByDelegationBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 13)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 13) rfl hsel
  have hd : dispatchMsg contract I.calldata = some attestByDelegationTransition := by
    apply easDispatch_attestByDelegation (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hplans : easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = [] :=
    easPlans_of_selector hsel (by native_decide)
  obtain ⟨k,C,rd⟩ := easReachAttestByDelegationBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : 36 ≤ I.calldata.size ∧ I.calldata.size < 2^255+4
  · have hcheck := solcDecodeLenCheckOk_4_32 hv.1 hv.2 hsize
    have hdec := decodeDelegatedAttest "delegatedRequest" easPlanTable hsz
      (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false) hcheck) hplans
    have r1 := easBlocks.eas_block_1890_fallthrough (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact hcheck) rd
    have hr := easDelegatedAttestEntry v (by simp) hv.2 r1
    by_cases hc : delegatedAttestValid I.calldata
    · rw [if_pos hc] at hdec
      let root := attestRoot I.calldata
      let r := delegatedAttestRecord I.calldata root
      let args := (∅ : Store).insert "delegatedRequest" r.tuple
      have hprefix := delegatedAttestPrefixSource (fork := fork) (L := args) (imms := immStore v)
        (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (r := r) (store_get_self _ _ _) hsz hsize
        (by change I.calldata.size-4 < 2^255; omega)
      by_cases ha : copyRequestValid 352 r.data.data.size ∧ copyRequestNext 352 r.data.data.size+96 ≤ 2^64-1
      · have hready : delegatedAttestEntryReady I.calldata := ⟨hc,ha⟩
        obtain ⟨a2,k2,C2,r2⟩ := hr.1 hready
        have hreq : (delegatedAttestPrefixLocals args I.calldata r).get? "delegatedRequest" = some r.struct := store_get_self _ _ _
        have hheap : (delegatedAttestPrefixLocals args I.calldata r).get? "$EAS.freeMemory" =
            some (.int (Int.ofNat (delegatedAttestCopyHeap I.calldata root+96))) := by
          simp (disch := decide) only [delegatedAttestPrefixLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
          rfl
        have hroot := delegatedAttestRoot_bounds hc.1
        have href := requestReference_of_eager hv.2 hroot.1 (by have := hroot.2; change (attestRoot I.calldata).toNat < 2^254; omega)
          hc.2.2.1 hc.2.2.2.1
        have hrun := delegatedAttestRun v (by simp) SourceState.init hreq hheap ⟨hc.2.2,ha⟩ hv.2 href r2
        have hfull := hrun.prepend (hprefix.1 ha)
        rcases hfull with ⟨frame',evm',σ',uid,hsrc,hs,hret⟩ | ⟨hsrc,hrev⟩ | ⟨hsrc,hstatic⟩
        · refine RDret.reEquivExecutionGen (retVal := some [wordBytes32Value uid]) (cs := frame') (evm'' := evm')
            hcode hret hd hdec ?_ hs.accounts (returnEquiv_of_encode (bytes32ReturnEncoding uid))
          rw [delegatedAttest_body]
          apply ExecFuncBody.execBlockRet
          simpa only [List.append_assoc] using hsrc
        · refine RDrev.reEquivExecutionRevert hcode hrev hd hdec ?_
          rw [delegatedAttest_body]
          apply ExecFuncBody.execBlockRevert
          simpa only [List.append_assoc] using hsrc
        · refine RDstatic.reEquivStaticHalt hcode hstatic hd hdec ?_
          rw [delegatedAttest_body]
          apply ExecFuncBody.execBlockStatic
          simpa only [List.append_assoc] using hsrc
      · have hrev := hr.2 (fun h => ha h.2)
        refine RDrev.reEquivExecutionRevert hcode hrev hd hdec ?_
        rw [delegatedAttest_body,List.append_assoc]
        apply ExecFuncBody.execBlockRevert
        exact execBlock_append_term (hprefix.2 ha) (by intros; exact nofun)
    · rw [if_neg hc] at hdec
      exact RDrev.reEquivDecodingFailed hcode (hr.2 (fun h => hc h.1)) hd hdec
  · have hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
      by_cases h36 : 36 ≤ I.calldata.size
      · exact solcDecodeLenCheckHuge_4_32 (by omega) hsize
      · exact solcDecodeLenCheckShort_4_32 hsz (by omega) hsize
    have r1 := easBlocks.eas_block_1890_taken (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact ne_of_eq_of_ne hcheck (by decide)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) r1
    exact RDrev.reEquivDecodingFailed hcode hr hd
      (decodeSolc_none_head ["delegatedRequest"] [delegatedAttestABI] easPlanTable 32 rfl (by native_decide) hsz
        (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true) hcheck))

end Benchmarks.EAS.EAS

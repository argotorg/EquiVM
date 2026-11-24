import Benchmarks.EAS.EAS.DelegatedRevokeRun
import Benchmarks.EAS.EAS.DelegatedRevokePrepare
import Benchmarks.EAS.EAS.Dispatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easRevokeByDelegationBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 16)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 16) rfl hsel
  have hd : dispatchMsg contract I.calldata = some revokeByDelegationTransition := by
    apply easDispatch_revokeByDelegation (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hplans : easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = [] :=
    easPlans_of_selector hsel (by native_decide)
  obtain ⟨k,C,rd⟩ := easReachRevokeByDelegationBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : 228 ≤ I.calldata.size ∧ I.calldata.size < 2^255+4
  · have hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨224⟩ = ⟨0⟩ :=
      solcCalldataStaticLenCheckOk (words := 7) hv.1 hv.2 hsize
    have hdec := decodeDelegatedRevoke "delegatedRequest" easPlanTable hsize hv.1
      (solcSLT_sub4_of_check (need := ⟨224⟩) (bit := false) hcheck) hplans
    have r1 := easBlocks.eas_block_922_fallthrough (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact hcheck) rd
    have hr := easDelegatedRevokePrepare v (by simp) hsize hv.1 hv.2 r1
    by_cases hc : delegatedRevokeClean I.calldata 4
    · rw [if_pos hc] at hdec
      obtain ⟨a2,k2,C2,r2⟩ := hr.1 hc
      let r := delegatedRevokeRecord I.calldata 4
      let args := (∅ : Store).insert "delegatedRequest" r.tuple
      have hprefix := delegatedRevokePrefixSource (fork := fork) (L := args) (imms := immStore v)
        (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (r := r) (store_get_self _ _ _) hsz hsize
        (by change I.calldata.size-4 < 2^255; omega)
      have hreq : (delegatedRevokePrefixLocals args I.calldata r).get? "delegatedRequest" = some r.struct := store_get_self _ _ _
      have hheap : (delegatedRevokePrefixLocals args I.calldata r).get? "$EAS.freeMemory" = some (.int (Int.ofNat 512)) := by
        simp (disch := decide) only [delegatedRevokePrefixLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
      have hrun := delegatedRevokeRun v (by simp) SourceState.init hreq hheap hc hsize hv.1 hv.2 r2
      have hfull := hrun.prepend hprefix
      rcases hfull with ⟨frame',evm',σ',hsrc,hs,hret⟩ | ⟨hsrc,hrev⟩ | ⟨hsrc,hstatic⟩
      · refine RDret.reEquivExecutionGen (retVal := none) (cs := frame') (evm'' := evm')
          hcode hret hd hdec ?_ hs.accounts ?_
        · rw [delegatedRevoke_body]
          apply ExecFuncBody.execBlockOK
          simpa only [List.append_assoc] using hsrc
        · exact returnEquiv.fallthrough (dvs := []) rfl (by native_decide) (by native_decide)
      · refine RDrev.reEquivExecutionRevert hcode hrev hd hdec ?_
        rw [delegatedRevoke_body]
        apply ExecFuncBody.execBlockRevert
        simpa only [List.append_assoc] using hsrc
      · refine RDstatic.reEquivStaticHalt hcode hstatic hd hdec ?_
        rw [delegatedRevoke_body]
        apply ExecFuncBody.execBlockStatic
        simpa only [List.append_assoc] using hsrc
    · rw [if_neg hc] at hdec
      exact RDrev.reEquivDecodingFailed hcode (hr.2 hc) hd hdec
  · have hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨224⟩ = ⟨1⟩ := by
      by_cases h228 : 228 ≤ I.calldata.size
      · exact solcCalldataStaticLenCheckHuge (words := 7) (by omega) hsize (by decide)
      · exact solcCalldataStaticLenCheckShort (words := 7) hsz (by omega) hsize (by decide)
    have r1 := easBlocks.eas_block_922_taken (immWords := wordsOf (immStore v)) (by simp)
      (by rw [easCalldataSub4 hsz hsize]; exact ne_of_eq_of_ne hcheck (by decide)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) r1
    exact RDrev.reEquivDecodingFailed hcode hr hd
      (decodeSolc_none_head ["delegatedRequest"] [delegatedRevokeABI] easPlanTable 224 rfl (by native_decide) hsz
        (solcSLT_sub4_of_check (need := ⟨224⟩) (bit := true) hcheck))

end Benchmarks.EAS.EAS

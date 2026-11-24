import Benchmarks.EAS.EAS.AttestCall
import Benchmarks.EAS.EAS.AttestPublicSource
import Benchmarks.EAS.EAS.AttestPublicMemory
import Benchmarks.EAS.EAS.AttestControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestPublicTail : Body := [attestPublicCopy] ++ attestPublicCopyUnpack ++
  attestPublicRequests ++ [attestPublicCall] ++ attestPublicFinish

theorem attestPublicRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw root : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+44 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hsize : ee.calldata.size < 2^255+4) (hd : requestDataValid ee.calldata (attestRequestData ee.calldata root))
    (hreq : L.get? "request" = some (attestRequestValue ee.calldata root))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat 480)))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
      (attestRequestData ee.calldata root::UInt256.ofNat ee.calldata.size::UInt256.ofNat 557::root::UInt256.ofNat 224::
        UInt256.ofNat 587::UInt256.ofNat 32::UInt256.ofNat 594::UInt256.ofNat 32::R)
      attestPublicArrayMemory aw rdata σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (uid : UInt256),
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestPublicTail
        (.returned {contract := contract,locals := L',immutables := immStore v} evm' (some [wordBytes32Value uid])) ∧
      SourceState s0 ee σ' evm' ∧ RDret fork (deployedRuntime v) g s0 σ' uid.toByteArray) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestPublicTail .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestPublicTail .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  let r := requestDataRecord ee.calldata (attestRequestData ee.calldata root)
  let schema := calldataWord ee.calldata root.toNat
  let next := copyRequestNext 480 r.data.size
  let L1 := allocateBlockLocals L next
  let L2 := attestPublicRequestsLocals L1 r
  have he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm attestPublicCopyArgs =
      .ok [r.tuple,.int (Int.ofNat 480)] := by
    simp only [attestPublicCopyArgs,evalExprs?,evalExpr?,hreq,hh,attestRequestValue,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  have hs := copyRequestCall_branches (fork := fork) (retVar := "allocation$allocation") he
  have hr := easCopyRequest_branches (heap := UInt256.ofNat 480) v
    (by simp only [List.length_cons]; omega) (by decide) (by decide) attestPublicArrayMemory_facts.2.2.1
    (by rw [easPatchedValidJumps v]; jump_dest) rd
  have hg := requestCopyRunValid_iff (heap := UInt256.ofNat 480) hd
  by_cases hv : copyRequestValid 480 r.data.size
  · have hc := hs.1 hv
    obtain ⟨a1,k1,C1,r1⟩ := hr.1 (hg.mpr hv)
    have hm := attestPublicInputMemory_view ee.calldata root hsize hd hv
    have hcopy := requestCopyMemory_views attestPublicArrayMemory ee.calldata (attestRequestData ee.calldata root)
      (UInt256.ofNat 480) (by decide) (by decide) hsize hd hv
    have hlen : memLoad (UInt256.ofNat 224) (attestPublicCopiedMemory ee.calldata root) = ⟨1⟩ :=
      (memLoad_of_prefix hcopy.1 _ (by decide) (by decide)
        (by have := attestPublicArrayMemory_facts.1; change 256 ≤ _; omega)).trans attestPublicArrayMemory_facts.2.1
    have hcover : 256 ≤ (attestPublicCopiedMemory ee.calldata root).size := by
      have hc : 480 ≤ (attestPublicCopiedMemory ee.calldata root).size := le_trans attestPublicArrayMemory_facts.1 hcopy.1.size
      omega
    obtain ⟨a2,k2,C2,r2⟩ := easAttestArraySet (array := UInt256.ofNat 224) (ptr := UInt256.ofNat 480) (root := root)
      (mem := attestPublicCopiedMemory ee.calldata root) v (by simp only [List.length_cons]; omega) (by decide) hcover
      (by rw [hlen]; decide) r1
    have hu : ExecBlock fork config
        (resumeAfterInternalCall {contract := contract,locals := L,immutables := immStore v}
          "allocation$allocation" (some [.tuple [],.int (Int.ofNat next)])) evm attestPublicCopyUnpack
        (.ok {contract := contract,locals := L1,immutables := immStore v} evm) := by
      change ExecBlock fork config
        {contract := contract,locals := L.insert "allocation$allocation" (.tuple [.tuple [],.int (Int.ofNat next)]),immutables := immStore v}
        evm attestPublicCopyUnpack (.ok {contract := contract,locals := L1,immutables := immStore v} evm)
      apply unpackHeapResult (store_get_self _ _ _)
        (by simpa only [store_get_ne _ _ (by decide : ("allocation$allocation" == "$EAS.freeMemory") = false)] using hh)
        (by decide) (by decide)
    have hreq1 : L1.get? "request" = some (.tuple [wordBytes32Value schema,r.tuple]) :=
      (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hreq
    have hreq2 : L2.get? "request" = some (.tuple [wordBytes32Value schema,r.tuple]) := by
      simpa only [L2,attestPublicRequestsLocals,store_get_ne _ _ (by decide : ("requests" == "request") = false)] using hreq1
    have hheap2 : L2.get? "$EAS.freeMemory" = some (.int (Int.ofNat next)) := by
      simp (disch := decide) only [L2,attestPublicRequestsLocals,L1,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
    have hrequests : L2.get? "requests" = some (.array [r.tuple]) := store_get_self _ _ _
    have hinit := execBlock_append (ExecBlock.consNormal hc ExecBlock.nil)
      (execBlock_append hu (attestPublicRequestsSource hreq1))
    have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by have := hv.2.2.1; change next < 2^256; omega)
    have heCall : evalExprs? config {contract := contract,locals := L2,immutables := immStore v} evm attestPublicCallArgs =
        .ok [wordBytes32Value schema,.array ([r].map AttestationRequestRecord.tuple),.address ee.source,
          .int (Int.ofNat ee.weiValue.toNat),.bool true,.int (Int.ofNat (UInt256.ofNat next).toNat)] := by
      simp only [attestPublicCallArgs,evalExprs?,evalExpr?,hreq2,hheap2,hrequests,EvalResult.ofOption,bind,EvalResult.bind,pure,envValue,hstate.env,hn]
      rfl
    have hrun := attestCallRun (retVar := "__c0$allocation") v .single heCall
      (by simp only [List.length_cons]; omega) hstate
      (by rw [hn]; exact hm.1) (by rw [hn]; exact hv.2.2.1) hm.2.1 hm.2.2 (fun _ => rfl)
      (by change ee.calldata.size < 2^256; omega) (by rw [easPatchedValidJumps v]; jump_dest) r2
    rcases hrun with ⟨evm',σ',mem',out,a3,k3,C3,heap',uids,used,hstate',_,_,hlen',_,_,hview,_,hcall,r3⟩ |
      ⟨hcall,hrev⟩ | ⟨hcall,hstatic⟩
    · obtain ⟨uid,rfl⟩ := List.length_eq_one_iff.mp hlen'
      have hret := easAttestPublicReturn v (by omega) hview r3
      have hfinish := attestPublicFinishSource (fork := fork) (evm := evm') (imms := immStore v)
        (L := L2.insert "__c0$allocation" (.tuple [attestationsResultValue [uid] used,.int (Int.ofNat heap')]))
        (store_get_self _ _ _) (by simpa only [store_get_ne _ _ (by decide : ("__c0$allocation" == "$EAS.freeMemory") = false)] using hheap2)
      let Lfinal := unpackHeapLocals
        (L2.insert "__c0$allocation" (.tuple [attestationsResultValue [uid] used,.int (Int.ofNat heap')]))
        "__c0" "$EAS.freeMemory" (attestationsResultValue [uid] used) heap'
      refine Or.inl ⟨Lfinal,evm',σ',uid,?_,hstate',hret⟩
      simpa only [attestPublicTail,List.append_assoc,List.singleton_append] using
        execBlock_append hinit (ExecBlock.consNormal hcall hfinish)
    · refine Or.inr (Or.inl ⟨?_,hrev⟩)
      simpa only [attestPublicTail,List.append_assoc,List.singleton_append] using
        execBlock_append hinit (ExecBlock.consRevert (stmts := attestPublicFinish) hcall)
    · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
      simpa only [attestPublicTail,List.append_assoc,List.singleton_append] using
        execBlock_append hinit (ExecBlock.consStatic (stmts := attestPublicFinish) hcall)
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert (hs.2 hv),hr.2 (fun h => hv (hg.mp h))⟩)

end Benchmarks.EAS.EAS

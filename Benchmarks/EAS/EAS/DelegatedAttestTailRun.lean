import Benchmarks.EAS.EAS.DelegatedAttestTailMemory
import Benchmarks.EAS.EAS.DelegatedAttestTailEVM
import Benchmarks.EAS.EAS.DelegatedAttestSource
import Benchmarks.EAS.EAS.PublicWordRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem delegatedAttestFinishSource {cfg : Config} {frame : Frame} {evm : EVM.State} {uid used : UInt256}
    (h : frame.locals.get? "__c1" = some (attestationsResultValue [uid] used)) :
    ExecBlock fork cfg frame evm delegatedAttestFinish (.returned frame evm (some [wordBytes32Value uid])) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?,evalExpr?,h,attestationsResultValue,lookupField?,lookupIndex?,EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

theorem delegatedAttestTailRun {L : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root heap : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+44 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (hreq : L.get? "delegatedRequest" = some (delegatedAttestRecord ee.calldata root).struct)
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hlo : 224 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) (hcover : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hsize : ee.calldata.size < 2^255+4) (hd : delegatedAttestFieldsValid ee.calldata root)
    (href : requestReferenceValid ee.calldata root (root+UInt256.ofNat 32))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2122⟩ (delegatedAttestSavedStack ee.calldata root R).tail mem aw rdata σ k C) :
    PublicWordRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm delegatedAttestTail := by
  let r := delegatedAttestRecord ee.calldata root
  have hn : allocateNext heap.toNat 256 = heap.toNat+256 := by
    unfold allocateNext
    rw [show allocateRounded 256 = 256 from rfl]
    apply Nat.mod_eq_of_lt
    change heap.toNat+256 < 2^256; omega
  have healloc : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm (.intLit 256) =
      .ok (.int (Int.ofNat 256)) := by simp only [evalExpr?,pure]; rfl
  have hr := easDelegatedAttestTailAllocate v (by omega) (by omega) hh hheap href rd
  rw [delegatedAttestTail,List.append_assoc,List.append_assoc,List.append_assoc]
  by_cases hg : heap.toNat+256 ≤ 2^64-1
  · rw [if_pos hg] at hr
    obtain ⟨a1,k1,C1,r1⟩ := hr
    have hp := allocateBlock_ok (fork := fork) healloc hf (by rw [hn]; exact ⟨hg,by omega⟩)
    rw [hn] at hp
    apply PublicWordRun.prepend (hp := hp)
    let L1 := allocateBlockLocals L (heap.toNat+256)
    let start := UInt256.ofNat (heap.toNat+256)
    have hstart : start.toNat = heap.toNat+256 := ulit_toNat' _ (by change _ < 2^256; omega)
    have hr1 : L1.get? "delegatedRequest" = some r.struct :=
      (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hreq
    have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat (heap.toNat+256))) := store_get_self _ _ _
    have hecopy : evalExprs? config {contract := contract,locals := L1,immutables := immStore v} evm delegatedAttestTailCopyArgs =
        .ok [r.data.tuple,.int (Int.ofNat (heap.toNat+256))] := by
      simp only [delegatedAttestTailCopyArgs,evalExprs?,evalExpr?,hr1,hf1,DelegatedAttestationRecord.struct,
        lookupField?,EvalResult.ofOption,bind,EvalResult.bind,pure]
      rfl
    have hsCopy := copyRequestCall_branches (fork := fork) (retVar := "allocation$allocation") hecopy
    have harray := oneRequestArrayMemory_views mem heap (by omega)
    have hrCopy := easCopyRequest_branches (heap := start) v (by simp only [List.length_cons]; omega)
      (by rw [hstart]; omega) (by rw [hstart]; exact hg) harray.2.2.1
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    have hguard := requestCopyRunValid_iff (heap := start) hd.2.1
    simp only [hstart] at hguard
    by_cases hv : copyRequestValid (heap.toNat+256) r.data.data.size
    · obtain ⟨a2,k2,C2,r2⟩ := hrCopy.1 (hguard.mpr hv)
      have hm := delegatedAttestTailMemory_view mem ee.calldata root heap hlo hg hcover hzero hsize hd.2.1 hv
      have hc := heapResultBlock_ok (result := "allocation") (cursor := "$EAS.freeMemory") (hsCopy.1 hv) hf1 (by decide) (by decide) (by decide)
      apply PublicWordRun.prepend (hp := hc)
      let next := copyRequestNext (heap.toNat+256) r.data.data.size
      let L2 := heapResultLocals L1 "allocation$allocation" "allocation" "$EAS.freeMemory" (.tuple []) next
      let L3 := delegatedAttestDataLocals L2 r.data
      have hr2 : L2.get? "delegatedRequest" = some r.struct :=
        (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hr1
      have hf2 : L2.get? "$EAS.freeMemory" = some (.int (Int.ofNat next)) := store_get_self _ _ _
      have hdata := delegatedAttestDataSource (fork := fork) (L := L2) (imms := immStore v) (evm := evm) (r := r) hr2
      apply PublicWordRun.prepend (hp := hdata)
      have hnext : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by have := hv.2.2.1; change next < 2^256; omega)
      have hr3 : L3.get? "delegatedRequest" = some r.struct := by
        simpa (disch := decide) only [L3,delegatedAttestDataLocals,store_get_ne] using hr2
      have hf3 : L3.get? "$EAS.freeMemory" = some (.int (Int.ofNat next)) := by
        simpa (disch := decide) only [L3,delegatedAttestDataLocals,store_get_ne] using hf2
      have hd3 : L3.get? "data" = some (.array [r.data.tuple]) := store_get_self _ _ _
      obtain ⟨a3,k3,C3,r3⟩ := easDelegatedAttestTailSet (mem := delegatedAttestTailCopiedMemory mem ee.calldata root heap)
        v (by simp only [List.length_cons]; omega)
        (by change heap.toNat+32 < 2^256; omega) (by have := hm.1.1; omega) (by rw [hm.1.2]; decide) hd.2.2.2 r2
      have ha : UInt256.ofNat r.attester.val = calldataWord ee.calldata (root+UInt256.ofNat 160).toNat :=
        addressWord_eq_ofNat_address hd.2.2.2
      rw [← ha] at r3
      have he : evalExprs? config {contract := contract,locals := L3,immutables := immStore v} evm delegatedAttestCallArgs =
          .ok [wordBytes32Value r.schema,.array ([r.data].map AttestationRequestRecord.tuple),.address r.attester,
            .int (Int.ofNat ee.weiValue.toNat),.bool true,.int (Int.ofNat (UInt256.ofNat next).toNat)] := by
        simp only [delegatedAttestCallArgs,evalExprs?,evalExpr?,hr3,hf3,hd3,EvalResult.ofOption,bind,EvalResult.bind,pure,
          envValue,hs.env,hnext,lookupField?,DelegatedAttestationRecord.struct]
        rfl
      have hcall := attestCallRun (locals := L3) (heap := UInt256.ofNat next) (retVar := "__c1$allocation") v .single he
        (by simp only [List.length_cons]; omega) hs (by simpa only [hnext] using hm.2.1)
        (by rw [hnext]; exact hv.2.2.1) hm.2.2.1 hm.2.2.2 (fun _ => rfl)
        (by change ee.calldata.size < 2^256; omega) (by rw [easPatchedValidJumps v]; jump_dest) r3
      rcases hcall with ⟨e1,σ1,m1,out,a4,k4,C4,heap1,uids,used,hs1,_,_,hlen,_,_,hview,_,hcall,r4⟩ | ⟨hcall,hrev⟩ | ⟨hcall,hstatic⟩
      · obtain ⟨uid,rfl⟩ := List.length_eq_one_iff.mp hlen
        have hu := heapResultBlock_ok (result := "__c1") (cursor := "$EAS.freeMemory") hcall hf3 (by decide) (by decide) (by decide)
        apply PublicWordRun.prepend (hp := hu)
        let L4 := heapResultLocals L3 "__c1$allocation" "__c1" "$EAS.freeMemory" (attestationsResultValue [uid] used) heap1
        refine Or.inl ⟨{contract := contract,locals := L4,immutables := immStore v},e1,σ1,uid,?_,hs1,
          easAttestPublicReturn v (by omega) hview r4⟩
        have huids : L4.get? "__c1" = some (attestationsResultValue [uid] used) := heapResultLocals_result _ _ _ _ _ _ (by decide)
        exact delegatedAttestFinishSource huids
      · exact PublicWordRun.revertPrefix (ExecBlock.consRevert hcall : ExecBlock fork config
          {contract := contract,locals := L3,immutables := immStore v} evm delegatedAttestCall .reverted) hrev
      · exact PublicWordRun.staticPrefix (ExecBlock.consStatic hcall : ExecBlock fork config
          {contract := contract,locals := L3,immutables := immStore v} evm delegatedAttestCall .staticViolation) hstatic
    · exact PublicWordRun.revertPrefix (ExecBlock.consRevert (hsCopy.2 hv) : ExecBlock fork config
        {contract := contract,locals := L1,immutables := immStore v} evm delegatedAttestTailCopy .reverted)
        (hrCopy.2 (fun h => hv (hguard.mp h)))
  · rw [if_neg hg] at hr
    exact PublicWordRun.revertPrefix (allocateBlock_revert healloc hf (by rw [hn]; intro h; exact hg h.1)) hr

end Benchmarks.EAS.EAS

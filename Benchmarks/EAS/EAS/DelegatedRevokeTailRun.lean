import Benchmarks.EAS.EAS.DelegatedRevokeTailEVM
import Benchmarks.EAS.EAS.DelegatedRevokeSource
import Benchmarks.EAS.EAS.DelegatedRevokeDecode
import Benchmarks.EAS.EAS.RevokeRun
import Benchmarks.EAS.EAS.PublicVoidRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem delegatedRevokeTailRun {L : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+37 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (hreq : L.get? "delegatedRequest" = some (delegatedRevokeRecord ee.calldata 4).struct)
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hlo : 128 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) (hcover : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hsize : ee.calldata.size < UInt256.size) (h100 : 100 ≤ ee.calldata.size) (hbig : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1136⟩
      (UInt256.ofNat (delegatedRevokeRecord ee.calldata 4).revoker.val::calldataWord ee.calldata 4::UInt256.ofNat 1180::R)
      mem aw rdata σ k C) :
    PublicVoidRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm delegatedRevokeTail := by
  let r := delegatedRevokeRecord ee.calldata 4
  have hn : allocateNext heap.toNat 192 = heap.toNat+192 := fixedAllocation_next .bytes192 hh
  have healloc : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm (.intLit 192) =
      .ok (.int (Int.ofNat 192)) := by simp only [evalExpr?,pure]; rfl
  have hr := easDelegatedRevokeTailEVM v (by omega) hlo hh hheap hsize h100 hbig rd
  rw [delegatedRevokeTail,List.append_assoc]
  by_cases hg : heap.toNat+192 ≤ 2^64-1
  · rw [if_pos hg] at hr
    obtain ⟨a1,k1,C1,r1⟩ := hr
    have hp := allocateBlock_ok (fork := fork) healloc hf (by rw [hn]; exact ⟨hg,by omega⟩)
    rw [hn] at hp
    let L1 := allocateBlockLocals L (heap.toNat+192)
    let L2 := delegatedRevokeDataLocals L1 r.data
    have hr1 : L1.get? "delegatedRequest" = some r.struct :=
      (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hreq
    have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat (heap.toNat+192))) := store_get_self _ _ _
    have hd := delegatedRevokeDataSource (fork := fork) (L := L1) (imms := immStore v) (evm := evm) (r := r) hr1
    apply PublicVoidRun.prepend (hp := hp)
    apply PublicVoidRun.prepend (hp := hd)
    have hr2 : L2.get? "delegatedRequest" = some r.struct := by
      simpa (disch := decide) only [L2,delegatedRevokeDataLocals,store_get_ne] using hr1
    have hf2 : L2.get? "$EAS.freeMemory" = some (.int (Int.ofNat (heap.toNat+192))) := by
      simpa (disch := decide) only [L2,delegatedRevokeDataLocals,store_get_ne] using hf1
    have hd2 : L2.get? "data" = some (.array [r.data.tuple]) := store_get_self _ _ _
    have hnext : (UInt256.ofNat (heap.toNat+192)).toNat = heap.toNat+192 := ulit_toNat' _ (by change _ < 2^256; omega)
    have he : evalExprs? config {contract := contract,locals := L2,immutables := immStore v} evm delegatedRevokeCallArgs =
        .ok [wordBytes32Value r.schema,.array ([r.data].map RevocationRequestRecord.tuple),.address r.revoker,
          .int (Int.ofNat ee.weiValue.toNat),.bool true,.int (Int.ofNat (UInt256.ofNat (heap.toNat+192)).toNat)] := by
      simp only [delegatedRevokeCallArgs,evalExprs?,evalExpr?,hr2,hf2,hd2,EvalResult.ofOption,bind,EvalResult.bind,pure,
        envValue,hs.env,hnext,lookupField?,DelegatedRevocationRecord.struct]
      rfl
    have hm := delegatedRevokeTailMemory_facts mem heap ee.calldata hlo (by change _ < 2^256; omega) hcover hzero
    obtain ⟨used,hcall⟩ := revokeCallRun (L := L2) (heap := UInt256.ofNat (heap.toNat+192))
      (retVar := "__c1$allocation") v .single hstack hs he (by simpa only [hnext] using hm.1)
      (by rw [hnext]; exact hg) hm.2.1 hm.2.2.1 (fun _ => rfl) hsize
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    have hrun : HeapCallOrStatic fork config (deployedRuntime v) ee g s0
        {contract := contract,locals := L2,immutables := immStore v} evm "_revoke" delegatedRevokeCallArgs "__c1$allocation"
        (.int (Int.ofNat used.toNat)) (UInt256.ofNat 1180) (used::R)
        (delegatedRevokeTailMemory mem heap ee.calldata) (heap.toNat+192) := by
      simp only [hnext] at hcall
      rcases hcall with (⟨_,h⟩ | h) | h
      · exact Or.inl h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    rcases hrun with (⟨e1,σ1,m1,out,a2,k2,C2,heap1,hs1,_,_,_,_,hcall,r2⟩ | ⟨hcall,hrev⟩) | ⟨hcall,hstatic⟩
    · refine Or.inl ⟨{contract := contract,locals := heapResultLocals L2 "__c1$allocation" "__c1" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap1,immutables := immStore v},e1,σ1,?_,hs1,?_⟩
      · exact heapResultBlock_ok hcall hf2 (by decide) (by decide) (by decide)
      · exact easBlocks.eas_block_1180 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) r2
    · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hcall,hrev⟩)
    · exact Or.inr (Or.inr ⟨ExecBlock.consStatic hcall,hstatic⟩)
  · rw [if_neg hg] at hr
    exact PublicVoidRun.revertPrefix (allocateBlock_revert healloc hf (by rw [hn]; intro h; exact hg h.1)) hr

end Benchmarks.EAS.EAS

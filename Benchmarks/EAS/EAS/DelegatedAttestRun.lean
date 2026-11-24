import Benchmarks.EAS.EAS.DelegatedAttestTailRun
import Benchmarks.EAS.EAS.DelegatedAttestBounds
import Benchmarks.EAS.EAS.VerifyAttestRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem delegatedAttestRun {L : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {aw root : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+44 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hreq : L.get? "delegatedRequest" = some (delegatedAttestRecord ee.calldata root).struct)
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat (delegatedAttestCopyHeap ee.calldata root+96))))
    (hc : delegatedAttestReady ee.calldata root) (hsize : ee.calldata.size < 2^255+4)
    (href : requestReferenceValid ee.calldata root (root+UInt256.ofNat 32))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13494⟩
      (UInt256.ofNat 224::delegatedAttestSavedStack ee.calldata root R)
      (delegatedAttestInputMemory ee.calldata root) aw rdata σ k C) :
    PublicWordRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm (delegatedAttestVerify ++ delegatedAttestTail) := by
  let r := delegatedAttestRecord ee.calldata root
  let heap := delegatedAttestCopyHeap ee.calldata root+96
  have hh : heap ≤ 2^64-1 := hc.2.2
  have hn : (UInt256.ofNat heap).toNat = heap := ulit_toNat' _ (by change heap < 2^256; omega)
  have hv := delegatedAttestInputMemory_view ee.calldata root hsize hc.1 hc.2.1 hc.2.2
  have he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm delegatedAttestVerifyArgs =
      .ok [r.struct,.int (Int.ofNat (UInt256.ofNat heap).toNat)] := by
    simp only [delegatedAttestVerifyArgs,evalExprs?,evalExpr?,hreq,hf,EvalResult.ofOption,bind,EvalResult.bind,pure,hn]
    rfl
  have hcall := verifyAttestCallRun (L := L) (r := r) (heap := UInt256.ofNat heap)
    (retVar := "__c0$allocation") v he
    (by simp only [delegatedAttestSavedStack,List.length_cons]; omega) hs (by simpa only [hn] using hv.1) hv.2.1
    (by rw [hn]; exact hh) (by rw [easPatchedValidJumps v]; jump_dest) rd
  rcases hcall with (⟨e1,σ1,m1,out,a1,k1,C1,heap1,hs1,hlo,hhi,hprefix,hfree,hcall,r1⟩ | ⟨hcall,hrev⟩) | ⟨hcall,hstatic⟩
  · let L1 := heapResultLocals L "__c0$allocation" "__c0" "$EAS.freeMemory" (.tuple []) heap1
    have hsrc := heapResultBlock_ok (result := "__c0") (cursor := "$EAS.freeMemory") hcall hf (by decide) (by decide) (by decide)
    have hreq1 : L1.get? "delegatedRequest" = some r.struct :=
      (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hreq
    have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap1)) := heapResultLocals_heap _ _ _ _ _ _
    have hn1 : (UInt256.ofNat heap1).toNat = heap1 := ulit_toNat' _ (by change _ < 2^256; omega)
    have hcover : 128 ≤ (delegatedAttestInputMemory ee.calldata root).size := by
      have hcov := hv.1.covered; change 224+128 ≤ _ at hcov; omega
    have hlow : 352 ≤ heap := hv.1.span
    simp only [hn] at hlo hprefix
    have hz : memLoad (UInt256.ofNat 96) m1 = ⟨0⟩ :=
      (memLoad_of_prefix hprefix (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap; omega) hcover).trans hv.2.2
    have ht := delegatedAttestTailRun (L := L1) (heap := UInt256.ofNat heap1) v hstack hs1 hreq1
      (by simpa only [hn1] using hf1) (by rw [hn1]; omega) (by rw [hn1]; exact hhi) hfree
      (by have := hprefix.size; omega) hz hsize hc.1 href r1
    exact ht.prepend hsrc
  · exact PublicWordRun.revertPrefix (ExecBlock.consRevert hcall : ExecBlock fork config
      {contract := contract,locals := L,immutables := immStore v} evm delegatedAttestVerify .reverted) hrev
  · exact PublicWordRun.staticPrefix (ExecBlock.consStatic hcall : ExecBlock fork config
      {contract := contract,locals := L,immutables := immStore v} evm delegatedAttestVerify .staticViolation) hstatic

end Benchmarks.EAS.EAS

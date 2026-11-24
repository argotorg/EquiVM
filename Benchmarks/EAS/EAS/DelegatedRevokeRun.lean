import Benchmarks.EAS.EAS.DelegatedRevokeTailRun
import Benchmarks.EAS.EAS.DelegatedRevokePrepareMemory
import Benchmarks.EAS.EAS.VerifyRevokeRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem delegatedRevokeRun {L : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hreq : L.get? "delegatedRequest" = some (delegatedRevokeRecord ee.calldata 4).struct)
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat 512)))
    (hc : delegatedRevokeClean ee.calldata 4)
    (hsize : ee.calldata.size < UInt256.size) (h228 : 228 ≤ ee.calldata.size) (hbig : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13806⟩
      (UInt256.ofNat 224::UInt256.ofNat 1136::calldataWord ee.calldata 196::calldataWord ee.calldata 4::UInt256.ofNat 1180::R)
      (delegatedRevokeInputMemory ee.calldata) aw rdata σ k C) :
    PublicVoidRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm (delegatedRevokeVerify ++ delegatedRevokeTail) := by
  let r := delegatedRevokeRecord ee.calldata 4
  have hv := delegatedRevokeInputMemory_view ee.calldata hc.1 hc.2
  have ha : UInt256.ofNat r.revoker.val = calldataWord ee.calldata 196 := addressWord_eq_ofNat_address hc.2
  rw [← ha] at rd
  have he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm delegatedRevokeVerifyArgs =
      .ok [r.struct,.int (Int.ofNat (UInt256.ofNat 512).toNat)] := by
    simp only [delegatedRevokeVerifyArgs,evalExprs?,evalExpr?,hreq,hf,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  have hcall := verifyRevokeCallRun (L := L) (r := r) (heap := UInt256.ofNat 512)
    (retVar := "__c0$allocation") v he (by simp only [List.length_cons]; omega) hs hv.1 hv.2
    (by decide) (by rw [easPatchedValidJumps v]; jump_dest) rd
  rcases hcall with (⟨e1,σ1,m1,out,a1,k1,C1,heap1,hs1,hlo,hhi,hprefix,hfree,hcall,r1⟩ | ⟨hcall,hrev⟩) | ⟨hcall,hstatic⟩
  · let L1 := heapResultLocals L "__c0$allocation" "__c0" "$EAS.freeMemory" (.tuple []) heap1
    have hsrc := heapResultBlock_ok (result := "__c0") (cursor := "$EAS.freeMemory") hcall hf (by decide) (by decide) (by decide)
    have hreq1 : L1.get? "delegatedRequest" = some r.struct :=
      (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hreq
    have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap1)) := heapResultLocals_heap _ _ _ _ _ _
    have hn : (UInt256.ofNat heap1).toNat = heap1 := ulit_toNat' _ (by change _ < 2^256; omega)
    have hcover : 128 ≤ (delegatedRevokeInputMemory ee.calldata).size := by
      have hcov := hv.1.covered
      change 224+128 ≤ _ at hcov
      omega
    have hz : memLoad (UInt256.ofNat 96) m1 = ⟨0⟩ :=
      (memLoad_of_prefix hprefix (UInt256.ofNat 96) (by decide) (by decide) hcover).trans
        (delegatedRevokeInputMemory_zero ee.calldata)
    have ht := delegatedRevokeTailRun (L := L1) (heap := UInt256.ofNat heap1) v hstack hs1 hreq1
      (by simpa only [hn] using hf1) (by rw [hn]; change 512 ≤ heap1 at hlo; omega)
      (by rw [hn]; exact hhi) hfree (by have := hprefix.size; omega) hz hsize (by omega) hbig r1
    exact ht.prepend hsrc
  · exact PublicVoidRun.revertPrefix (ExecBlock.consRevert hcall : ExecBlock fork config
      {contract := contract,locals := L,immutables := immStore v} evm delegatedRevokeVerify .reverted) hrev
  · exact PublicVoidRun.staticPrefix (ExecBlock.consStatic hcall : ExecBlock fork config
      {contract := contract,locals := L,immutables := immStore v} evm delegatedRevokeVerify .staticViolation) hstatic

end Benchmarks.EAS.EAS

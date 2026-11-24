import Benchmarks.EAS.EAS.VerifySigner
import Benchmarks.EAS.EAS.HashTypedRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem HeapCallPost.forget {post : Prop} {cfg : Config} {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : EVM.State} {caller : Frame} {evm : EVM.State} {name retVar : Ident}
    {args : List Expr} {value : Value} {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {heap : Nat}
    (h : HeapCallPost fork post cfg code ee g s0 caller evm name args retVar value pc stack mem heap) :
    HeapCallRun fork cfg code ee g s0 caller evm name args retVar value pc stack mem heap := by
  rcases h with ⟨_,h⟩ | h
  · exact h
  · exact Or.inr h

def verifyHashBody : Body := heapResultBlock "_hashTypedDataV4" [.var "structHash",.var "$EAS.freeMemory"]
  "digest$allocation" "digest" "$EAS.freeMemory"
def verifyRecoverArgs : List Expr := [.var "digest",.field (.var "signature") "v",
  .field (.var "signature") "r",.field (.var "signature") "s",.var "$EAS.freeMemory"]
def verifyRecoverBody : Body := heapResultBlock "ECDSA_recover" verifyRecoverArgs
  "__c0$allocation" "__c0" "$EAS.freeMemory"
def verifyDigestBody (field : Ident) : Body := verifyHashBody ++ verifyRecoverBody ++ verifySignerBody field

theorem verifyDigestRun {L : Store} {field : Ident} {req : Value} {a : AccountAddress} {s : SignatureRecord}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash ownerPtr sigPtr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hreq : L.get? "request" = some req) (ha : lookupField? req field = some (.address a))
    (hsig : L.get? "signature" = some s.struct)
    (hhash : L.get? "structHash" = some (wordBytes32Value hash))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hview : SignatureMemoryView mem sigPtr s) (hsigend : sigPtr.toNat+96 ≤ heap.toNat)
    (howner : UInt256.land (memLoad ownerPtr mem) solcAddrMask = UInt256.ofNat a.val)
    (holow : 96 ≤ ownerPtr.toNat) (hocover : ownerPtr.toNat+32 ≤ mem.size) (hoend : ownerPtr.toNat+32 ≤ heap.toNat)
    (hstack : R.length+18 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15646⟩
      (hash::⟨13723⟩::sigPtr::⟨13745⟩::ownerPtr::solcAddrMask::solcAddrMask::⟨13753⟩::ret::R) mem aw rdata σ k C) :
    HeapReturnRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm (verifyDigestBody field) (.tuple []) ret R mem heap.toNat := by
  have ht := hashTypedCallRun (L := L) (args := [.var "structHash",.var "$EAS.freeMemory"])
    (retVar := "digest$allocation") v
    (by simp only [evalExprs?,evalExpr?,hhash,hf,EvalResult.ofOption,EvalResult.bind,bind,pure])
    (by simp only [List.length_cons]; omega) hs hh hlo hheap
    (by rw [easPatchedValidJumps v]; jump_dest) rd
  unfold verifyDigestBody
  rw [List.append_assoc]
  rcases ht with ⟨evm1,σ1,mem1,out1,aw1,k1,C1,heap1,hs1,hge1,hbound1,hprefix1,hfree1,hcall1,r1⟩ | ⟨hcall1,hrev⟩
  · let digest := typedDataWord (domainWord v ee.codeOwner) hash
    let L1 := heapResultLocals L "digest$allocation" "digest" "$EAS.freeMemory" (wordBytes32Value digest) heap1
    have hp1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm verifyHashBody
        (.ok {contract := contract,locals := L1,immutables := immStore v} evm1) :=
      heapResultBlock_ok hcall1 hf (by decide) (by decide) (by decide)
    have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap1)) := heapResultLocals_heap _ _ _ _ _ _
    have hd1 : L1.get? "digest" = some (wordBytes32Value digest) := heapResultLocals_result _ _ _ _ _ _ (by decide)
    have hs1' : L1.get? "signature" = some s.struct :=
      (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hsig
    have he1 : evalExprs? config {contract := contract,locals := L1,immutables := immStore v} evm1 verifyRecoverArgs =
        .ok [wordBytes32Value digest,.int (Int.ofNat s.v.toNat),wordBytes32Value s.r,wordBytes32Value s.s,.int (Int.ofNat heap1)] := by
      have hsEval : evalExpr? config {contract := contract,locals := L1,immutables := immStore v} evm1 (.var "signature") = .ok s.struct := by
        simp only [evalExpr?,hs1',EvalResult.ofOption]
      have hv := evalRecordField hsEval (field := "v") (by rfl)
      have hr := evalRecordField hsEval (field := "r") (by rfl)
      have hs' := evalRecordField hsEval (field := "s") (by rfl)
      simp only [verifyRecoverArgs,evalExprs?,hv,hr,hs',evalExpr?,hd1,hf1,EvalResult.ofOption,EvalResult.bind,bind,pure]
    have hn1 : (UInt256.ofNat heap1).toNat = heap1 := ulit_toNat' _ (by change heap1 < 2^256; omega)
    have hv1 := hview.preserve hprefix1 hsigend (by change heap.toNat < 2^256; omega)
    obtain ⟨b,hr⟩ := recoverSignatureCallRun (heap := UInt256.ofNat heap1) (retVar := "__c0$allocation") v
      (by simpa only [hn1] using he1) hv1 (by simp only [List.length_cons]; omega)
      hs1 hfree1 (by rw [hn1]; omega) (by rw [hn1]; exact hbound1)
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    simp only [hn1] at hr
    rcases hr.forget with ⟨evm2,σ2,mem2,out2,aw2,k2,C2,heap2,hs2,hge2,hbound2,hprefix2,hfree2,hcall2,r2⟩ | ⟨hcall2,hrev⟩
    · let L2 := heapResultLocals L1 "__c0$allocation" "__c0" "$EAS.freeMemory" (.address b) heap2
      have hp2 : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} evm1 verifyRecoverBody
          (.ok {contract := contract,locals := L2,immutables := immStore v} evm2) :=
        heapResultBlock_ok hcall2 hf1 (by decide) (by decide) (by decide)
      have hreq1 : L1.get? "request" = some req :=
        (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hreq
      have hreq2 : L2.get? "request" = some req :=
        (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hreq1
      have hb2 : L2.get? "__c0" = some (.address b) := heapResultLocals_result _ _ _ _ _ _ (by decide)
      have hf2 : L2.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap2)) := heapResultLocals_heap _ _ _ _ _ _
      have hpre := hprefix1.trans (hprefix2.mono hge1)
      have howner2 : UInt256.land (memLoad ownerPtr mem2) solcAddrMask = UInt256.ofNat a.val := by
        rw [memLoad_of_prefix hpre ownerPtr holow hoend hocover]; exact howner
      exact ((verifySignerRun v hreq2 ha hb2 hf2 howner2 (by omega) hs2 hfree2 hbound2 hret r2).prepend
        hp2 hprefix2 hge2).prepend hp1 hprefix1 hge1
    · exact Or.inr ⟨execFuncBody_append hp1 (ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall2)),hrev⟩
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall1),hrev⟩

end Benchmarks.EAS.EAS

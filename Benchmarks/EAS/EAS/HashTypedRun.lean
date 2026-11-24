import Benchmarks.EAS.EAS.HashTypedSource
import Benchmarks.EAS.EAS.DomainCall
import Benchmarks.EAS.EAS.TypedDataCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem hashTypedRun {L : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap structHash ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hhash : L.get? "structHash" = some (wordBytes32Value structHash))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hstack : R.length+10 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15646⟩ (structHash::ret::R) mem aw rdata σ k C) :
    HeapReturnRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm hashTypedFunction.body (wordBytes32Value (typedDataWord (domainWord v ee.codeOwner) structHash))
      ret (typedDataWord (domainWord v ee.codeOwner) structHash::R) mem heap.toNat := by
  have r1 := easBlocks.eas_block_15646 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  have hdomain := domainCallRun (L := L) (heapExpr := .var "$EAS.freeMemory") (retVar := "__c0$allocation") v
    (by simp only [evalExpr?,hf,EvalResult.ofOption]) (by simp only [List.length_cons]; omega)
    hs hh hlo hheap (by rw [easPatchedValidJumps v]; jump_dest) r1
  rw [hashTyped_body]
  rcases hdomain with ⟨evm1,σ1,mem1,out1,aw1,k1,C1,heap1,hs1,hge1,hbound1,hprefix1,hfree1,hcall1,r2⟩ | ⟨hcall1,hrev⟩
  · let L1 := heapResultLocals L "__c0$allocation" "__c0" "$EAS.freeMemory" (wordBytes32Value (domainWord v ee.codeOwner)) heap1
    have hp : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm hashTypedPrefix
        (.ok {contract := contract,locals := L1,immutables := immStore v} evm1) :=
      heapResultBlock_ok hcall1 hf (by decide) (by decide) (by decide)
    have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap1)) := heapResultLocals_heap _ _ _ _ _ _
    have he1 : evalExprs? config {contract := contract,locals := L1,immutables := immStore v} evm1 hashTypedCallArgs =
        .ok [wordBytes32Value (domainWord v ee.codeOwner),wordBytes32Value structHash,.int (Int.ofNat heap1)] := by
      have hd1 : L1.get? "__c0" = some (wordBytes32Value (domainWord v ee.codeOwner)) :=
        heapResultLocals_result _ _ _ _ _ _ (by decide)
      have hh1 : L1.get? "structHash" = some (wordBytes32Value structHash) :=
        (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hhash
      simp only [hashTypedCallArgs,evalExprs?,evalExpr?,hd1,hh1,hf1,EvalResult.ofOption,EvalResult.bind,bind,pure]
    have hn1 : (UInt256.ofNat heap1).toNat = heap1 := ulit_toNat' _ (by change heap1 < 2^256; omega)
    have htyped := typedDataCallRun (retVar := "__c1$allocation") (heap := UInt256.ofNat heap1) v
      (by simpa only [hn1] using he1) (by omega) hs1 hfree1 (by rw [hn1]; omega)
      (by rw [hn1]; exact hbound1) hret r2
    simp only [hn1] at htyped
    rcases htyped with ⟨evm2,σ2,mem2,out2,aw2,k2,C2,heap2,hs2,hge2,hbound2,hprefix2,hfree2,hcall2,r3⟩ | ⟨hcall2,hrev⟩
    · have hsrc := hashTypedTailSource hf1 hcall2
      have hrun : HeapReturnRun fork config (deployedRuntime v) ee g s0
          {contract := contract,locals := L1,immutables := immStore v} evm1 hashTypedTail
          (wordBytes32Value (typedDataWord (domainWord v ee.codeOwner) structHash)) ret
          (typedDataWord (domainWord v ee.codeOwner) structHash::R) mem1 heap1 :=
        Or.inl ⟨_,evm2,σ2,mem2,out2,aw2,k2,C2,heap2,hs2,hge2,hbound2,hprefix2,hfree2,hsrc,r3⟩
      exact hrun.prepend hp hprefix1 hge1
    · have hsrc : ExecFuncBody fork config {contract := contract,locals := L1,immutables := immStore v}
          evm1 hashTypedTail .reverted := ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall2)
      exact Or.inr ⟨execFuncBody_append hp hsrc,hrev⟩
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall1),hrev⟩

theorem hashTypedCallRun {L : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap structHash ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm args =
      .ok [wordBytes32Value structHash,.int (Int.ofNat heap.toNat)])
    (hstack : R.length+10 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15646⟩ (structHash::ret::R) mem aw rdata σ k C) :
    HeapCallRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm "_hashTypedDataV4" args retVar (wordBytes32Value (typedDataWord (domainWord v ee.codeOwner) structHash))
      ret (typedDataWord (domainWord v ee.codeOwner) structHash::R) mem heap.toNat := by
  exact (hashTypedRun (L := hashTypedArgs structHash heap.toNat) v
    (by simp only [hashTypedArgs,store_get_self])
    (by simp (disch := decide) only [hashTypedArgs,store_get_ne,store_get_self])
    hstack hs hh hlo hheap hret rd).call he hashTyped_lookup (hashTyped_bind structHash heap.toNat)

end Benchmarks.EAS.EAS

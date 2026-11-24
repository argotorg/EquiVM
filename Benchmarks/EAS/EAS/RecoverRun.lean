import Benchmarks.EAS.EAS.TryRecoverRun
import Benchmarks.EAS.EAS.RecoverSource
import Benchmarks.EAS.EAS.ECDSAErrorEVM
import Benchmarks.EAS.EAS.HeapPost
import Benchmarks.EAS.EAS.RuntimeBlocks_041

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem recoverRun {L imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash sigV r s saved0 saved1 saved2 ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hhash : L.get? "hash" = some (wordBytes32Value hash))
    (hsigV : L.get? "v" = some (.int (Int.ofNat sigV.toNat)))
    (hr : L.get? "r" = some (wordBytes32Value r)) (hsigS : L.get? "s" = some (wordBytes32Value s))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hstack : R.length+15 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hv : sigV.toNat < 2^8) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16645⟩
      (hash::sigV::r::s::⟨13745⟩::saved0::saved1::saved2::ret::R) mem aw rdata σ k C) :
    ∃ a : AccountAddress, HeapReturnPost fork (a ≠ 0) config (deployedRuntime v) ee g s0
      {contract := contract,locals := L,immutables := imms} evm recoverFunction.body (.address a)
      ret (saved0::saved1::saved2::UInt256.ofNat a.val::R) mem heap.toNat := by
  have he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm recoverCallArgs =
      .ok [wordBytes32Value hash,.int (Int.ofNat sigV.toNat),wordBytes32Value r,wordBytes32Value s,
        .int (Int.ofNat heap.toNat)] := by
    simp only [recoverCallArgs,evalExprs?,evalExpr?,hhash,hsigV,hr,hsigS,hf,EvalResult.ofOption,EvalResult.bind,bind,pure]
  obtain ⟨a,error,herror,hzero,hcall⟩ := tryRecoverCallRun (retVar := "__c0$allocation") v he
    (by simp only [List.length_cons]; omega) hs hh hmem hv hlo hheap
    (by rw [easPatchedValidJumps v]; jump_dest) rd
  refine ⟨a,?_⟩
  rcases hcall with ⟨evm1,σ1,mem1,out,aw1,k1,C1,heap1,hs1,hlo1,hheap1,hprefix,hfree,hcall,r1⟩ | ⟨hcall,hrev⟩
  · have hp := recoverPrefixSource hf hcall
    have htail := recoverTailSource (fork := fork) (imms := imms) (evm := evm1)
      (recoverLocals_recovered L a error heap1) (recoverLocals_error L a error heap1)
      (recoverLocals_heap L a error heap1)
    have r2 := easBlocks.eas_block_13745 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    have hevm := easECDSAError v (by simp only [List.length_cons]; omega)
      (by change error < 2^256; omega) hret r2
    by_cases hz : error = 0
    · rw [if_pos (Or.inl hz)] at htail hevm
      obtain ⟨L2,hsrc⟩ := htail
      obtain ⟨k2,C2,r3⟩ := hevm
      refine Or.inl ⟨hzero hz,Or.inl ⟨{contract := contract,locals := L2,immutables := imms},evm1,σ1,mem1,out,aw1,k2,C2,heap1,hs1,hlo1,hheap1,hprefix,hfree,?_,r3⟩⟩
      rw [recover_body]
      exact execFuncBody_append hp hsrc
    · have hn : ¬ (error = 0 ∨ error = 4) := by omega
      rw [if_neg hn] at htail hevm
      refine Or.inr ⟨?_,hevm⟩
      rw [recover_body]
      exact execFuncBody_append hp htail
  · refine Or.inr ⟨?_,hrev⟩
    rw [recover_body]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall)

theorem recoverCallRun {L imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash sigV r s saved0 saved1 saved2 ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm args =
      .ok [wordBytes32Value hash,.int (Int.ofNat sigV.toNat),wordBytes32Value r,wordBytes32Value s,
        .int (Int.ofNat heap.toNat)])
    (hstack : R.length+15 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hv : sigV.toNat < 2^8) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16645⟩
      (hash::sigV::r::s::⟨13745⟩::saved0::saved1::saved2::ret::R) mem aw rdata σ k C) :
    ∃ a : AccountAddress, HeapCallPost fork (a ≠ 0) config (deployedRuntime v) ee g s0
      {contract := contract,locals := L,immutables := imms} evm "ECDSA_recover" args retVar (.address a)
      ret (saved0::saved1::saved2::UInt256.ofNat a.val::R) mem heap.toNat := by
  obtain ⟨a,h⟩ := recoverRun (L := recoverArgs hash sigV r s heap.toNat) (imms := imms) v
    (by simp (disch := decide) only [recoverArgs,tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [recoverArgs,tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [recoverArgs,tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [recoverArgs,tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [recoverArgs,tryRecoverArgs,store_get_ne,store_get_self])
    hstack hs hh hmem hv hlo hheap hret rd
  exact ⟨a,h.call he recover_lookup (recover_bind hash sigV r s heap.toNat)⟩

end Benchmarks.EAS.EAS

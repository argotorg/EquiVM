import Benchmarks.EAS.EAS.ResolveOneCall
import Benchmarks.EAS.EAS.ResolveManyEntry
import Benchmarks.EAS.EAS.ResolveManySource
import Benchmarks.EAS.EAS.RecordArrayMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManySingleRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema array values available value ptr ret : UInt256} {R : List UInt256}
    {record : Value} {a : AttestationRecord} {target : AccountAddress} {rev last : Bool} (v : EASImmutables)
    (he : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm resolveManySingleArgs =
      .ok [record,a.value,.int (Int.ofNat value.toNat),.bool rev,.int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat ptr.toNat)])
    (hcursor : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat ptr.toNat)))
    (hfield : lookupField? record "resolver" = some (.address target))
    (ht : UInt256.land (memLoad (schema+UInt256.ofNat 32) mem) solcAddrMask = UInt256.ofNat target.val)
    (hstack : R.length+27 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (harray : AttestationArrayMemoryView mem array [a] ptr.toNat)
    (hvalues : WordArrayMemoryView mem values [value] ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManySinglePC rev)
      (resolveManyHeadStack rev schema array values available last.toUInt256 (UInt256.ofNat 1) (ret::R)) mem aw rdata σ k C) :
    HeapReturnPost fork ((resolveOneUsedValue target value).toNat ≤ available.toNat) config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm resolveManySingleBody (.int (Int.ofNat (resolveOneUsedValue target value).toNat))
      ret (resolveOneUsedValue target value::R) mem ptr.toNat := by
  obtain ⟨src,dataPtr,hsrc,hview,hsrcEnd,hdataEnd⟩ := harray.records 0 (by simp)
  have hw := hvalues.get 0 (by simp)
  simp only [Nat.mul_zero,Nat.add_zero,List.getElem_cons_zero] at hsrc hview hdataEnd hw
  obtain ⟨a1,k1,C1,r1⟩ := resolveManySingleEntry v rev (by simp only [List.length_cons]; omega)
    harray.length hvalues.length hsrc hw rd
  have hrun := resolveOneCallRun (retVar := "__c0$allocation") v he hfield ht
    (by simp only [List.length_cons]; omega) hperm hs hview hsrcEnd hdataEnd hheap hh
    (by rw [easPatchedValidJumps]; jump_dest) r1
  rcases hrun with ⟨hb,⟨e,σ',m,out,a2,k2,C2,heap',hs',hlo,hhi,hp,hh',hc,hr⟩ | ⟨hc,hr⟩⟩ | ⟨hc,hr⟩
  · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_4692_packed (immWords := wordsOf (immStore v)) (by omega) hret hr
    let value' := Value.int (Int.ofNat (resolveOneUsedValue target value).toNat)
    let L := unpackHeapLocals (locals.insert "__c0$allocation" (.tuple [value',.int (Int.ofNat heap')]))
      "__c0" "$EAS.freeMemory" value' heap'
    have hunpack := unpackHeapResult (fork := fork) (cfg := config) (evm := e)
      (frame := {contract := contract, locals := locals.insert "__c0$allocation" (.tuple [value',.int (Int.ofNat heap')]), immutables := imms})
      (tmp := "__c0$allocation") (result := "__c0") (cursor := "$EAS.freeMemory")
      (store_get_self _ _ _)
      (by simpa (disch := decide) only [store_get_ne] using hcursor) (by decide) (by decide)
    refine Or.inl ⟨hb,Or.inl ⟨{contract := contract, locals := L, immutables := imms},e,σ',m,out,a3,k3,C3,heap',hs',hlo,hhi,hp,hh',?_,r3⟩⟩
    apply ExecFuncBody.execBlockRet (ExecBlock.consNormal hc ?_)
    apply execBlock_append hunpack
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp (disch := decide) only [evalExprs?,evalExpr?,value',unpackHeapLocals,store_get_self,store_get_ne,
      EvalResult.ofOption,EvalResult.bind,bind,pure]
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hc),hr⟩
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hc),hr⟩

end Benchmarks.EAS.EAS

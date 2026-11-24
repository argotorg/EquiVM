import Benchmarks.EAS.EAS.ResolveOneLocals
import Benchmarks.EAS.EAS.ResolveOneControl
import Benchmarks.EAS.EAS.RefundRun
import Benchmarks.EAS.EAS.HeapReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveOneFinishRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {available value ptr ret : UInt256} {R : List UInt256} {a : AttestationRecord} {target : AccountAddress}
    {rev last : Bool} (v : EASImmutables)
    (hf : ResolveOneLocals locals a target value (UInt256.sub available value) rev last ptr.toNat)
    (hstack : R.length+14 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hheap : ptr.toNat ≤ 2^64-1) (hlo : 96 ≤ ptr.toNat) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15885⟩ (last.toUInt256::value::available::value::ret::R) mem aw rdata σ k C) :
    HeapReturnRun fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm ([resolveOneRefund] ++ resolveOneReturn) (.int (Int.ofNat value.toNat)) ret (value::R) mem ptr.toNat := by
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.var "last") = .ok (.bool last) := by
    simp only [evalExpr?, hf.last, EvalResult.ofOption]
  have hr := resolveOneFinish v last (by omega) hret rd
  cases last with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hr
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    have hsrc := execFuncBody_append (fork := fork)
      (ExecBlock.consNormal (fork := fork) (ExecStmt.iteFalse (fork := fork) (thenB := resolveOneRefundBlock) he ExecBlock.nil) ExecBlock.nil)
      (resolveOneReturnSource (fork := fork) hf.value hf.heap)
    exact Or.inl ⟨_,evm,σ,mem,rdata,aw1,k1,C1,ptr.toNat,hs,le_refl _,hheap,MemoryPrefix.refl _ _,
      by simpa only [u256_ofNat_toNat] using hh,hsrc,rd1⟩
  | true =>
    simp only [if_true] at hr
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    have hrun := refundRun (cfg := config) (imms := imms) (locals := locals) (retVar := "__c3$allocation")
      (args := [.var "availableValue",.var "$EAS.freeMemory"]) v
      (by simp only [List.length_cons]; omega) hperm hs hheap hlo hh
      (by simp only [evalExprs?, evalExpr?, hf.available, hf.heap, EvalResult.ofOption, EvalResult.bind, bind, pure])
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
    rcases hrun with ⟨evm',σ',mem',out,aw2,k2,C2,heap',hs',hmono,hmax,hmem,hheap',hcall,rd2⟩ | ⟨hcall,hr⟩
    · have hf' := hf.refunded heap'
      have hblock := resolveOneRefundBlockSource hf.heap hcall
      have hsrc := execFuncBody_append (ExecBlock.consNormal (ExecStmt.iteTrue (elseB := []) he hblock) ExecBlock.nil)
        (resolveOneReturnSource hf'.value hf'.heap)
      obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_4692_packed (immWords := wordsOf (immStore v)) (by omega) hret rd2
      exact Or.inl ⟨_,evm',σ',mem',out,aw3,k3,C3,heap',hs',hmono,hmax,hmem,hheap',hsrc,rd3⟩
    · exact Or.inr ⟨ExecFuncBody.execBlockRevert
        (ExecBlock.consRevert (ExecStmt.iteTrue he (ExecBlock.consRevert hcall))),hr⟩

end Benchmarks.EAS.EAS

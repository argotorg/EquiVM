import Benchmarks.EAS.EAS.ResolveManyTailSource
import Benchmarks.EAS.EAS.ResolveManyFinishControl
import Benchmarks.EAS.EAS.RefundAny
import Benchmarks.EAS.EAS.HeapReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyFinishRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {available total ptr ret : UInt256} {R : List UInt256} {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress}
    {rev last : Bool} (v : EASImmutables)
    (hf : ResolveManyLocals locals ats words target available total rev last ptr.toNat i)
    (hstack : R.length+14 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hheap : ptr.toNat ≤ 2^64-1) (hlo : 96 ≤ ptr.toNat) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyFinishPC rev) (last.toUInt256::available::total::ret::R) mem aw rdata σ k C) :
    HeapReturnOrStatic fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm ([resolveManyRefund] ++ resolveManyReturn) (.int (Int.ofNat total.toNat)) ret (total::R) mem ptr.toNat := by
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.var "last") = .ok (.bool last) := by
    simp only [evalExpr?, hf.last, EvalResult.ofOption]
  have hr := resolveManyFinish v rev last (by omega) hret rd
  cases last with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hr
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    have hsrc := execFuncBody_append (fork := fork)
      (ExecBlock.consNormal (fork := fork) (ExecStmt.iteFalse (fork := fork) (thenB := resolveManyRefundBlock) he ExecBlock.nil) ExecBlock.nil)
      (resolveManyReturnSource (fork := fork) hf.total hf.heap)
    exact Or.inl (Or.inl ⟨_,evm,σ,mem,rdata,aw1,k1,C1,ptr.toNat,hs,le_refl _,hheap,MemoryPrefix.refl _ _,
      by simpa only [u256_ofNat_toNat] using hh,hsrc,rd1⟩)
  | true =>
    simp only [if_true] at hr
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    have hrun := refundRunAny (cfg := config) (imms := imms) (locals := locals) (retVar := "__c4$allocation")
      (args := [.var "availableValue",.var "$EAS.freeMemory"]) v
      (by simp only [List.length_cons]; omega) hs hheap hlo hh
      (by simp only [evalExprs?, evalExpr?, hf.available, hf.heap, EvalResult.ofOption, EvalResult.bind, bind, pure])
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
    rcases hrun with (⟨evm',σ',mem',out,aw2,k2,C2,heap',hs',hmono,hmax,hmem,hheap',hcall,rd2⟩ | ⟨hcall,hr⟩) | ⟨hcall,hr⟩
    · have hf' := hf.refunded heap'
      have hblock := resolveManyRefundBlockSource hf.heap hcall
      have hsrc := execFuncBody_append (ExecBlock.consNormal (ExecStmt.iteTrue (elseB := []) he hblock) ExecBlock.nil)
        (resolveManyReturnSource hf'.total hf'.heap)
      obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_4692_packed (immWords := wordsOf (immStore v)) (by omega) hret rd2
      exact Or.inl (Or.inl ⟨_,evm',σ',mem',out,aw3,k3,C3,heap',hs',hmono,hmax,hmem,hheap',hsrc,rd3⟩)
    · exact Or.inl (Or.inr ⟨ExecFuncBody.execBlockRevert
        (ExecBlock.consRevert (ExecStmt.iteTrue he (ExecBlock.consRevert hcall))),hr⟩)

    · exact Or.inr ⟨ExecFuncBody.execBlockStatic
        (ExecBlock.consStatic (ExecStmt.iteTrue he (ExecBlock.consStatic hcall))),hr⟩

end Benchmarks.EAS.EAS

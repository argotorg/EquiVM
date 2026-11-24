import Benchmarks.EAS.EAS.Signature
import Benchmarks.EAS.EAS.RuntimeBlocks_042

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def verifySignerBody (field : Ident) : Body := [
  .require (.binary .eq (.var "__c0") (.field (.var "request") field)),
  .return [.tupleLit [],.var "$EAS.freeMemory"]]

theorem evalAddressEq {cfg : Config} {frame : Frame} {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a)) (hy : evalExpr? cfg frame evm y = .ok (.address b)) :
    evalExpr? cfg frame evm (.binary .eq x y) = .ok (.bool (decide (a=b))) := by
  simp only [evalExpr?,hx,hy,EvalResult.bind,bind,evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,Value.address.injEq,decide_eq_true_eq]

theorem verifySignerRun {L imms : Store} {field : Ident} {req : Value} {a b : AccountAddress}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C heap : Nat}
    {ownerPtr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hreq : L.get? "request" = some req) (ha : lookupField? req field = some (.address a))
    (hb : L.get? "__c0" = some (.address b))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (howner : UInt256.land (memLoad ownerPtr mem) solcAddrMask = UInt256.ofNat a.val)
    (hstack : R.length+5 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap) (hheap : heap ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13753⟩
      (ownerPtr::solcAddrMask::solcAddrMask::UInt256.ofNat b.val::ret::R) mem aw rdata σ k C) :
    HeapReturnRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := imms}
      evm (verifySignerBody field) (.tuple []) ret R mem heap := by
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.binary .eq (.var "__c0") (.field (.var "request") field)) = .ok (.bool (decide (b=a))) := evalAddressEq (by simp only [evalExpr?,hb,EvalResult.ofOption])
    (evalRecordField (by simp only [evalExpr?,hreq,EvalResult.ofOption]) ha)
  have hc : UInt256.land (UInt256.ofNat b.val) solcAddrMask = UInt256.ofNat b.val := addressWord_val_clean b
  by_cases heq : b = a
  · have r1 := easBlocks.eas_block_13753_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hc,howner,heq]; exact u256_sub_eq_zero_iff_eq.mpr rfl) rd
    have r2 := easBlocks.eas_block_13763 (immWords := wordsOf (immStore v)) (by omega) hret r1
    refine Or.inl ⟨{contract := contract,locals := L,immutables := imms},evm,σ,mem,rdata,_,_,_,heap,hs,le_refl _,hheap,MemoryPrefix.refl _ _,hh,?_,r2⟩
    apply ExecFuncBody.execBlockRet
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [heq,decide_true] using he
    apply ExecBlock.consReturn
    apply ExecStmt.return
    simp only [evalExprs?,evalExpr?,evalExprList?,hf,EvalResult.ofOption,EvalResult.bind,bind,pure]
  · have hne : UInt256.ofNat b.val ≠ UInt256.ofNat a.val := by
      intro h
      apply heq
      apply Fin.ext
      have hn := congrArg UInt256.toNat h
      have hb' : (UInt256.ofNat b.val).toNat = b.val := addressWord_toNat_val b
      have ha' : (UInt256.ofNat a.val).toNat = a.val := addressWord_toNat_val a
      simpa only [hb',ha'] using hn
    have r1 := easBlocks.eas_block_13753_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hc,howner]; exact u256_sub_ne_zero_of_ne hne)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_13764 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_13753_taken_stack,List.length_cons]; omega) r1
    refine Or.inr ⟨?_,hr⟩
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert
    apply ExecStmt.requireFalse
    simpa only [heq,decide_false] using he

end Benchmarks.EAS.EAS

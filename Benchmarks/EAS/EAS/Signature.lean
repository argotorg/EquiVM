import Benchmarks.EAS.EAS.RecoverRun
import Benchmarks.EAS.EAS.RecordFieldExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

structure SignatureRecord where
  v : UInt256
  r : UInt256
  s : UInt256

def SignatureRecord.tuple (s : SignatureRecord) : Value :=
  .tuple [.int (Int.ofNat s.v.toNat),wordBytes32Value s.r,wordBytes32Value s.s]
def SignatureRecord.struct (s : SignatureRecord) : Value :=
  .struct "EIP712Signature" [("v",.int (Int.ofNat s.v.toNat)),("r",wordBytes32Value s.r),("s",wordBytes32Value s.s)]

abbrev decodeSignatureFunction : FunctionDecl := contract.functions[6]!
def decodeSignatureExpr : Expr := .structLit "EIP712Signature"
  [("v",.tupleGet (.var "signature") 0),("r",.tupleGet (.var "signature") 1),("s",.tupleGet (.var "signature") 2)]
theorem decodeSignature_body : decodeSignatureFunction.body = [
    .return [decodeSignatureExpr,.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]] := by native_decide

theorem decodeSignatureExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {s : SignatureRecord}
    (h : frame.locals.get? "signature" = some s.tuple) :
    evalExpr? cfg frame evm decodeSignatureExpr = .ok s.struct := by
  simp only [decodeSignatureExpr,evalExpr?,evalStructFields?,h,EvalResult.ofOption,EvalResult.bind,bind,pure,
    SignatureRecord.tuple,SignatureRecord.struct]
  rfl

theorem decodeSignatureSource {cfg : Config} {frame : Frame} {evm : EVM.State} {s : SignatureRecord} {heap : Nat}
    (hd : frame.locals.get? "signature" = some s.tuple)
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecFuncBody fork cfg frame evm decodeSignatureFunction.body
      (.returned frame evm (some [s.struct,.int (Int.ofNat heap)])) := by
  rw [decodeSignature_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?,decodeSignatureExpr_eval hd,EvalResult.bind,bind,pure]
  simp only [evalExpr?,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

def decodeSignatureArgs (s : SignatureRecord) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "signature" s.tuple
theorem decodeSignature_lookup : lookupCallable? contract "_decodeSignature" = some decodeSignatureFunction.toCallable := rfl
theorem decodeSignature_bind (s : SignatureRecord) (heap : Nat) :
    bindParams? decodeSignatureFunction.params [s.tuple,.int (Int.ofNat heap)] = some (decodeSignatureArgs s heap) := rfl

theorem decodeSignatureCall {cfg : Config} {L imms : Store} {evm : EVM.State}
    {args : List Expr} {retVar : Ident} {s : SignatureRecord} {heap : Nat}
    (he : evalExprs? cfg {contract := contract,locals := L,immutables := imms} evm args =
      .ok [s.tuple,.int (Int.ofNat heap)]) :
    ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "_decodeSignature" args retVar)
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} retVar
        (some [s.struct,.int (Int.ofNat heap)])) evm) := by
  exact internalCallFunctionReturn he decodeSignature_lookup (decodeSignature_bind s heap)
    (decodeSignatureSource (by simp only [decodeSignatureArgs,store_get_self])
      (by simp (disch := decide) only [decodeSignatureArgs,store_get_ne,store_get_self]))

structure SignatureMemoryView (mem : ByteArray) (ptr : UInt256) (s : SignatureRecord) : Prop where
  low : 96 ≤ ptr.toNat
  covered : ptr.toNat+96 ≤ mem.size
  v : UInt256.land (memLoad ptr mem) (UInt256.ofNat 255) = s.v
  r : memLoad (ptr+UInt256.ofNat 32) mem = s.r
  s : memLoad (ptr+UInt256.ofNat 64) mem = s.s

theorem SignatureMemoryView.vBound {mem : ByteArray} {ptr : UInt256} {s : SignatureRecord}
    (h : SignatureMemoryView mem ptr s) : s.v.toNat < 2^8 := by
  rw [← h.v]
  exact u256LandMaskToNatLtOfToNat _ _ (bits := 8) rfl

theorem SignatureMemoryView.preserve {before after : ByteArray} {ptr : UInt256}
    {s : SignatureRecord} {limit : Nat} (h : SignatureMemoryView before ptr s)
    (hp : MemoryPrefix before after limit) (he : ptr.toNat+96 ≤ limit) (hb : limit < UInt256.size) :
    SignatureMemoryView after ptr s := by
  have ho (n : Nat) (hn : n ≤ 64) : (ptr+UInt256.ofNat n).toNat = ptr.toNat+n :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hc := h.covered
  have hl := h.low
  have hp0 := memLoad_of_prefix hp ptr h.low (by omega) (by omega)
  refine ⟨h.low,le_trans h.covered hp.size,?_,?_,?_⟩
  · rw [hp0]; exact h.v
  · exact (memLoad_of_prefix hp _ (by rw [ho 32 (by decide)]; omega)
      (by rw [ho 32 (by decide)]; omega) (by rw [ho 32 (by decide)]; omega)).trans h.r
  · exact (memLoad_of_prefix hp _ (by rw [ho 64 (by decide)]; omega)
      (by rw [ho 64 (by decide)]; omega) (by rw [ho 64 (by decide)]; omega)).trans h.s

set_option maxRecDepth 10000 in
theorem recoverSignatureCallRun {L imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash sigPtr saved0 saved1 saved2 ret : UInt256} {s : SignatureRecord} {R : List UInt256} (v : EASImmutables)
    (he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm args =
      .ok [wordBytes32Value hash,.int (Int.ofNat s.v.toNat),wordBytes32Value s.r,wordBytes32Value s.s,
        .int (Int.ofNat heap.toNat)])
    (hview : SignatureMemoryView mem sigPtr s)
    (hstack : R.length+15 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13723⟩
      (hash::sigPtr::⟨13745⟩::saved0::saved1::saved2::ret::R) mem aw rdata σ k C) :
    ∃ a : AccountAddress, HeapCallPost fork (a ≠ 0) config (deployedRuntime v) ee g s0
      {contract := contract,locals := L,immutables := imms} evm "ECDSA_recover" args retVar (.address a)
      ret (saved0::saved1::saved2::UInt256.ofNat a.val::R) mem heap.toNat := by
  have r1 := easBlocks.eas_block_13723 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_13723_stack,hview.v,hview.r,hview.s] at r1
  exact recoverCallRun v he hstack hs hh (by have := hview.covered; omega) hview.vBound hlo hheap hret r1

end Benchmarks.EAS.EAS

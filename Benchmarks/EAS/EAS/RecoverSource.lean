import Benchmarks.EAS.EAS.TryRecoverCallSource
import Benchmarks.EAS.EAS.ECDSAErrorSource
import Benchmarks.EAS.EAS.HeapResultBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

abbrev recoverFunction : FunctionDecl := contract.functions[28]!
def recoverCallArgs : List Expr := [.var "hash",.var "v",.var "r",.var "s",.var "$EAS.freeMemory"]
def recoverPrefix : Body :=
  heapResultBlock "ECDSA_tryRecover" recoverCallArgs "__c0$allocation" "__c0" "$EAS.freeMemory" ++ [
    .letDecl "recovered" (some (.elem .address)) (.tupleGet (.var "__c0") 0),
    .letDecl "error" (some (.elem (.int (.uint ⟨8,by decide⟩)))) (.tupleGet (.var "__c0") 1)]
def recoverTail : Body :=
  heapResultBlock "ECDSA__throwError" [.var "error",.var "$EAS.freeMemory"]
    "__c1$allocation" "__c1" "$EAS.freeMemory" ++ [
    .return [.var "recovered",.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]]
theorem recover_body : recoverFunction.body = recoverPrefix ++ recoverTail := by native_decide

def recoverLocals (L : Store) (a : AccountAddress) (error heap : Nat) : Store :=
  heapResultLocals L "__c0$allocation" "__c0" "$EAS.freeMemory" (.tuple [.address a,.int (Int.ofNat error)]) heap
    |>.insert "recovered" (.address a) |>.insert "error" (.int (Int.ofNat error))

theorem recoverPrefixSource {L imms : Store} {evm evm' : EVM.State} {a : AccountAddress}
    {error heap : Nat} {oldHeap : Value}
    (hh : L.get? "$EAS.freeMemory" = some oldHeap)
    (hc : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "ECDSA_tryRecover" recoverCallArgs "__c0$allocation")
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} "__c0$allocation"
        (some [.tuple [.address a,.int (Int.ofNat error)],.int (Int.ofNat heap)])) evm')) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm recoverPrefix
      (.ok {contract := contract,locals := recoverLocals L a error heap,immutables := imms} evm') := by
  apply execBlock_append (heapResultBlock_ok hc hh (by decide) (by decide) (by decide))
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .address a) ?_) ?_
  · simp (disch := decide) only [evalExpr?,heapResultLocals,unpackHeapLocals,store_get_ne,store_get_self,
      EvalResult.ofOption,EvalResult.bind,bind,pure]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int (Int.ofNat error)) ?_) ExecBlock.nil
  simp (disch := decide) only [evalExpr?,heapResultLocals,unpackHeapLocals,store_get_ne,store_get_self,
    EvalResult.ofOption,EvalResult.bind,bind,pure]
  rfl

theorem recoverLocals_heap (L : Store) (a : AccountAddress) (error heap : Nat) :
    (recoverLocals L a error heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp (disch := decide) only [recoverLocals,store_get_ne,heapResultLocals_heap]
theorem recoverLocals_recovered (L : Store) (a : AccountAddress) (error heap : Nat) :
    (recoverLocals L a error heap).get? "recovered" = some (.address a) := by
  simp (disch := decide) only [recoverLocals,store_get_ne,store_get_self]
theorem recoverLocals_error (L : Store) (a : AccountAddress) (error heap : Nat) :
    (recoverLocals L a error heap).get? "error" = some (.int (Int.ofNat error)) := store_get_self _ _ _

theorem recoverTailSource {L imms : Store} {evm : EVM.State} {a : AccountAddress} {error heap : Nat}
    (ha : L.get? "recovered" = some (.address a))
    (he : L.get? "error" = some (.int (Int.ofNat error)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if error = 0 ∨ error = 4 then ∃ L',
      ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm recoverTail
        (.returned {contract := contract,locals := L',immutables := imms} evm
          (some [.address a,.int (Int.ofNat heap)]))
    else ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm recoverTail .reverted := by
  have hc := ecdsaErrorCall (fork := fork) (cfg := config) (L := L) (imms := imms) (evm := evm)
    (args := [.var "error",.var "$EAS.freeMemory"]) (retVar := "__c1$allocation") (n := error) (heap := heap)
    (by simp only [evalExprs?,evalExpr?,he,hh,EvalResult.ofOption,EvalResult.bind,bind,pure])
  split_ifs with hn
  · rw [if_pos hn] at hc
    let L' := heapResultLocals L "__c1$allocation" "__c1" "$EAS.freeMemory" (.tuple []) heap
    refine ⟨L',ExecFuncBody.execBlockRet ?_⟩
    apply execBlock_append (heapResultBlock_ok hc hh (by decide) (by decide) (by decide))
    apply ExecBlock.consReturn
    apply ExecStmt.return
    have ha' : L'.get? "recovered" = some (.address a) := by
      rw [heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
      exact ha
    have hh' : L'.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := heapResultLocals_heap _ _ _ _ _ _
    dsimp only [L'] at ha' hh'
    simp only [evalExprs?,evalExpr?,ha',hh',EvalResult.ofOption,EvalResult.bind,bind,pure]
  · rw [if_neg hn] at hc
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert hc)

def recoverArgs (hash sigV r s : UInt256) (heap : Nat) : Store := tryRecoverArgs hash sigV r s heap
theorem recover_lookup : lookupCallable? contract "ECDSA_recover" = some recoverFunction.toCallable := rfl
theorem recover_bind (hash sigV r s : UInt256) (heap : Nat) :
    bindParams? recoverFunction.params [wordBytes32Value hash,.int (Int.ofNat sigV.toNat),wordBytes32Value r,
      wordBytes32Value s,.int (Int.ofNat heap)] = some (recoverArgs hash sigV r s heap) := rfl

end Benchmarks.EAS.EAS

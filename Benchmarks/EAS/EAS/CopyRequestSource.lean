import Benchmarks.EAS.EAS.BytesAllocateSource
import Benchmarks.EAS.EAS.AttestationRequest

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev copyRequestFunction : FunctionDecl := contract.functions[1]!
def copyRequestRead : Body := [.letDecl "payload" (some .bytes) (.tupleGet (.var "data") 4)]
def copyRequestBytes : Body := bytesAllocateBlock (.arrayLength .localVar {base := "payload"})
def copyRequestReturn : Body := [.return [.tupleLit [],.var "$EAS.freeMemory"]]
def copyRequestNext (heap len : Nat) : Nat := allocateNext (allocateNext heap 192) (bytesAllocation len)
def copyRequestValid (heap len : Nat) : Prop :=
  (allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192) ∧ len ≤ 2^64-1 ∧
    copyRequestNext heap len ≤ 2^64-1 ∧ allocateNext heap 192 ≤ copyRequestNext heap len
instance (heap len : Nat) : Decidable (copyRequestValid heap len) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def copyRequestLocals (L : Store) (r : AttestationRequestRecord) (heap : Nat) : Store :=
  allocateBlockLocals ((allocateBlockLocals L (allocateNext heap 192)).insert "payload" (.bytes r.data))
    (copyRequestNext heap r.data.size)

theorem copyRequest_body : copyRequestFunction.body =
    allocateBlock (.intLit 192) ++ copyRequestRead ++ copyRequestBytes ++ copyRequestReturn := by native_decide

theorem copyRequestRead_source {L imms : Store} {evm : EVM.State} {r : AttestationRequestRecord}
    (hd : L.get? "data" = some r.tuple) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm copyRequestRead
      (.ok {contract := contract,locals := L.insert "payload" (.bytes r.data),immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  simp only [evalExpr?,hd,AttestationRequestRecord.tuple,EvalResult.ofOption,EvalResult.bind,bind,pure]
  rfl

theorem copyRequestSource {L imms : Store} {evm : EVM.State} {r : AttestationRequestRecord} {heap : Nat}
    (hd : L.get? "data" = some r.tuple) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if copyRequestValid heap r.data.size then
      ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm copyRequestFunction.body
        (.returned {contract := contract,locals := copyRequestLocals L r heap,immutables := imms} evm
          (some [.tuple [],.int (Int.ofNat (copyRequestNext heap r.data.size))]))
    else ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm copyRequestFunction.body .reverted := by
  rw [copyRequest_body]
  have hsize : evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.intLit 192) = .ok (.int (Int.ofNat 192)) := by
    simp only [evalExpr?,pure]; rfl
  by_cases hg : allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192
  · have halloc := allocateBlock_ok (fork := fork) hsize hh hg
    have hd1 := (allocateBlockLocals_get (heap := allocateNext heap 192)
      (by decide : ("allocation$allocation" == "data") = false) (by decide) (by decide)).trans hd
    have hp := execBlock_append halloc (copyRequestRead_source (imms := imms) (evm := evm) hd1)
    have hf : ((allocateBlockLocals L (allocateNext heap 192)).insert "payload" (.bytes r.data)).get? "$EAS.freeMemory" =
        some (.int (Int.ofNat (allocateNext heap 192))) := by
      simp (disch := decide) only [store_get_ne,allocateBlockLocals,unpackHeapLocals,store_get_self]
    have hl : evalExpr? config {contract := contract, locals := (allocateBlockLocals L (allocateNext heap 192)).insert "payload" (.bytes r.data),immutables := imms} evm
        (.arrayLength .localVar {base := "payload"}) = .ok (.int (Int.ofNat r.data.size)) := by
      simp only [evalExpr?,store_get_self,readLocalPath?,EvalResult.bind,bind,pure]
    have hb := bytesAllocateSource (fork := fork) hl hf
    rw [show allocateNext (allocateNext heap 192) (bytesAllocation r.data.size) = copyRequestNext heap r.data.size from rfl] at hb
    by_cases hg' : r.data.size ≤ 2^64-1
    · rw [if_pos hg'] at hb
      by_cases hn : copyRequestNext heap r.data.size ≤ 2^64-1 ∧ allocateNext heap 192 ≤ copyRequestNext heap r.data.size
      · rw [if_pos hn] at hb
        rw [if_pos ⟨hg,hg',hn⟩]
        apply ExecFuncBody.execBlockRet
        apply execBlock_append (execBlock_append hp hb)
        apply ExecBlock.consReturn
        apply ExecStmt.return
        have hfree : (copyRequestLocals L r heap).get? "$EAS.freeMemory" =
            some (.int (Int.ofNat (copyRequestNext heap r.data.size))) := store_get_self _ _ _
        change evalExprs? config {contract := contract,locals := copyRequestLocals L r heap,immutables := imms} evm
          [.tupleLit [],.var "$EAS.freeMemory"] = _
        simp only [evalExprs?,evalExpr?,evalExprList?,hfree,EvalResult.ofOption,EvalResult.bind,bind,pure]
      · rw [if_neg hn] at hb
        rw [if_neg (by intro h; exact hn h.2.2)]
        apply ExecFuncBody.execBlockRevert
        exact execBlock_append_term (execBlock_append hp hb) (by intros;exact nofun)
    · rw [if_neg hg'] at hb
      rw [if_neg (by intro h; exact hg' h.2.1)]
      apply ExecFuncBody.execBlockRevert
      exact execBlock_append_term (execBlock_append hp hb) (by intros;exact nofun)
  · rw [if_neg (by intro h; exact hg h.1)]
    apply ExecFuncBody.execBlockRevert
    simpa only [List.append_assoc] using execBlock_append_term
      (s2 := copyRequestRead ++ copyRequestBytes ++ copyRequestReturn) (allocateBlock_revert hsize hh hg) (by intros;exact nofun)

def copyRequestArgs (r : AttestationRequestRecord) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "data" r.tuple

theorem copyRequest_lookup : lookupCallable? contract "_copyAttestationData" = some copyRequestFunction.toCallable := rfl

theorem copyRequest_bind (r : AttestationRequestRecord) (heap : Nat) :
    bindParams? copyRequestFunction.params [r.tuple,.int (Int.ofNat heap)] = some (copyRequestArgs r heap) := rfl

theorem copyRequestCall {locals imms : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {r : AttestationRequestRecord} {heap : Nat}
    (he : evalExprs? config {contract := contract,locals := locals,immutables := imms} evm args = .ok [r.tuple,.int (Int.ofNat heap)]) :
    if copyRequestValid heap r.data.size then
      ExecStmt fork config {contract := contract,locals := locals,immutables := imms} evm (.internalCall "_copyAttestationData" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := locals,immutables := imms} retVar
          (some [.tuple [],.int (Int.ofNat (copyRequestNext heap r.data.size))])) evm)
    else ExecStmt fork config {contract := contract,locals := locals,immutables := imms} evm (.internalCall "_copyAttestationData" args retVar) .reverted := by
  have h := copyRequestSource (fork := fork) (imms := imms) (evm := evm)
    (show (copyRequestArgs r heap).get? "data" = some r.tuple from store_get_self _ _ _)
    (show (copyRequestArgs r heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) from by
      simp (disch := decide) only [copyRequestArgs,store_get_ne,store_get_self])
  split at h
  · rename_i hv
    rw [if_pos hv]
    exact internalCallFunctionReturn he copyRequest_lookup (copyRequest_bind r heap) h
  · rename_i hv
    rw [if_neg hv]
    exact internalCallFunctionRevert he copyRequest_lookup (copyRequest_bind r heap) h

end Benchmarks.EAS.EAS

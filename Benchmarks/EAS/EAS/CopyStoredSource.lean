import Benchmarks.EAS.EAS.StoredBytes
import Benchmarks.EAS.EAS.BytesAllocation

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev copyStoredFunction : FunctionDecl := contract.functions[3]!

def attestationABI : ABIType := .tuple [
  .elem (.bytes abiBytes32Width), .elem (.bytes abiBytes32Width),
  .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
  .elem (.bytes abiBytes32Width), .elem .address, .elem .address, .elem .bool, .bytes]

def copyStoredRead : Body := [
  .letDecl "attestation" (some attestationABI) (.storage attestationRef),
  .letDecl "payload" (some .bytes) (.field (.var "attestation") "data")]

abbrev copyStoredSize : Expr := bytesAllocationExpr (.arrayLength .localVar {base := "payload"})

def copyStoredReturn : Body := [.return [.var "attestation", .var "$EAS.freeMemory"],
  .return [.tupleLit [], .var "$EAS.freeMemory"]]

theorem copyStored_body : copyStoredFunction.body = allocateBlock (.intLit 320) ++
    (copyStoredRead ++ (allocateBlock copyStoredSize ++ copyStoredReturn)) := by native_decide

def copyStoredReadLocals (locals : Store) (evm : EVM.State) (word : UInt256) : Store :=
  (locals.insert "attestation" (attestationValue evm word (.bytes (attestationPayload evm word))))
    |>.insert "payload" (.bytes (attestationPayload evm word))

theorem copyStoredRead_ok {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_db" = none) (hkey : locals.get? "uid" = some (wordBytes32Value word))
    (hv : storedBytesValid (attestationHeader evm word)) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm copyStoredRead
      (.ok {contract := contract, locals := copyStoredReadLocals locals evm word, immutables := imms} evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := attestationValue evm word (.bytes (attestationPayload evm word))) ?_) ?_
  · rw [attestation_read hnone hkey, if_pos hv]
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes (attestationPayload evm word)) ?_) ExecBlock.nil
  simp only [evalExpr?, store_get_self, EvalResult.ofOption, EvalResult.bind, bind]
  change EvalResult.ofOption .typeError (lookupField? (attestationValue evm word (.bytes (attestationPayload evm word))) "data") = _
  rw [attestationValue_data]
  rfl

theorem copyStoredRead_revert {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_db" = none) (hkey : locals.get? "uid" = some (wordBytes32Value word))
    (hv : ¬ storedBytesValid (attestationHeader evm word)) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm copyStoredRead .reverted := by
  apply ExecBlock.consRevert
  apply ExecStmt.letDeclRevert
  rw [attestation_read hnone hkey, if_neg hv]

theorem copyStoredSize_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {payload : ByteArray}
    (hp : frame.locals.get? "payload" = some (.bytes payload)) :
    evalExpr? cfg frame evm copyStoredSize = .ok (.int (Int.ofNat (bytesAllocation payload.size))) := by
  apply bytesAllocationExpr_eval
  simp only [evalExpr?, hp, readLocalPath?, EvalResult.bind, bind, pure]

def copyStoredMiddleLocals (locals : Store) (evm : EVM.State) (word : UInt256) (heap : Nat) : Store :=
  copyStoredReadLocals (allocateBlockLocals locals (allocateNext heap 320)) evm word

theorem copyStoredMiddleLocals_heap {locals : Store} {evm : EVM.State} {word : UInt256} {heap : Nat} :
    (copyStoredMiddleLocals locals evm word heap).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat (allocateNext heap 320))) := by
  simp only [copyStoredMiddleLocals, copyStoredReadLocals,
    store_get_ne _ _ (by decide : ("payload" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("attestation" == "$EAS.freeMemory") = false), allocateBlockLocals, unpackHeapLocals, store_get_self]

theorem copyStored_prefix {evm : EVM.State} {locals imms : Store} {word : UInt256} {heap : Nat}
    (hnone : locals.get? "_db" = none) (hkey : locals.get? "uid" = some (wordBytes32Value word))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320)
    (hv : storedBytesValid (attestationHeader evm word)) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm
      (allocateBlock (.intLit 320) ++ copyStoredRead)
      (.ok {contract := contract, locals := copyStoredMiddleLocals locals evm word heap, immutables := imms} evm) := by
  apply execBlock_append (allocateBlock_ok (n := 320) (by simp only [evalExpr?, pure]; rfl) hh hg)
  apply copyStoredRead_ok
  · rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
    exact hnone
  · rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
    exact hkey
  · exact hv

def copyStoredNext (heap : Nat) (payload : ByteArray) : Nat :=
  allocateNext (allocateNext heap 320) (bytesAllocation payload.size)

def copyStoredFinalLocals (locals : Store) (evm : EVM.State) (word : UInt256) (heap : Nat) : Store :=
  allocateBlockLocals (copyStoredMiddleLocals locals evm word heap) (copyStoredNext heap (attestationPayload evm word))

theorem copyStoredSource_ok {evm : EVM.State} {locals imms : Store} {word : UInt256} {heap : Nat}
    (hnone : locals.get? "_db" = none) (hkey : locals.get? "uid" = some (wordBytes32Value word))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320)
    (hv : storedBytesValid (attestationHeader evm word))
    (hb : copyStoredNext heap (attestationPayload evm word) ≤ 2^64-1 ∧
      allocateNext heap 320 ≤ copyStoredNext heap (attestationPayload evm word)) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm copyStoredFunction.body
      (.returned {contract := contract, locals := copyStoredFinalLocals locals evm word heap, immutables := imms} evm
        (some [attestationValue evm word (.bytes (attestationPayload evm word)),
          .int (Int.ofNat (copyStoredNext heap (attestationPayload evm word)))])) := by
  rw [copyStored_body, ← List.append_assoc]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (copyStored_prefix hnone hkey hh hg hv)
  have hp : (copyStoredMiddleLocals locals evm word heap).get? "payload" = some (.bytes (attestationPayload evm word)) := store_get_self _ _ _
  have hh' := copyStoredMiddleLocals_heap (locals := locals) (evm := evm) (word := word) (heap := heap)
  apply execBlock_append (allocateBlock_ok (copyStoredSize_eval hp) hh' hb)
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hatt : (copyStoredFinalLocals locals evm word heap).get? "attestation" =
      some (attestationValue evm word (.bytes (attestationPayload evm word))) := by
    rw [copyStoredFinalLocals, allocateBlockLocals_get (by decide) (by decide) (by decide)]
    simp only [copyStoredMiddleLocals, copyStoredReadLocals,
      store_get_ne _ _ (by decide : ("payload" == "attestation") = false), store_get_self]
  have hf : (copyStoredFinalLocals locals evm word heap).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat (copyStoredNext heap (attestationPayload evm word)))) := store_get_self _ _ _
  change evalExprs? config {contract := contract, locals := copyStoredFinalLocals locals evm word heap, immutables := imms} evm
    [.var "attestation", .var "$EAS.freeMemory"] = _
  simp only [evalExprs?, evalExpr?, hatt, hf, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem copyStoredSource_revert_allocate {evm : EVM.State} {locals imms : Store} {heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : ¬ (allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320)) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm copyStoredFunction.body .reverted := by
  rw [copyStored_body]
  apply ExecFuncBody.execBlockRevert
  exact execBlock_append_term (allocateBlock_revert (n := 320) (by simp only [evalExpr?, pure]; rfl) hh hg) (by intros; simp)

theorem copyStoredSource_revert_header {evm : EVM.State} {locals imms : Store} {word : UInt256} {heap : Nat}
    (hnone : locals.get? "_db" = none) (hkey : locals.get? "uid" = some (wordBytes32Value word))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320)
    (hv : ¬ storedBytesValid (attestationHeader evm word)) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm copyStoredFunction.body .reverted := by
  rw [copyStored_body]
  apply ExecFuncBody.execBlockRevert
  apply execBlock_append (allocateBlock_ok (n := 320) (by simp only [evalExpr?, pure]; rfl) hh hg)
  refine execBlock_append_term ?_ (by intros; simp)
  exact copyStoredRead_revert
    ((allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hnone)
    ((allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hkey) hv

theorem copyStoredSource_revert_payload {evm : EVM.State} {locals imms : Store} {word : UInt256} {heap : Nat}
    (hnone : locals.get? "_db" = none) (hkey : locals.get? "uid" = some (wordBytes32Value word))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320)
    (hv : storedBytesValid (attestationHeader evm word))
    (hb : ¬ (copyStoredNext heap (attestationPayload evm word) ≤ 2^64-1 ∧
      allocateNext heap 320 ≤ copyStoredNext heap (attestationPayload evm word))) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm copyStoredFunction.body .reverted := by
  rw [copyStored_body, ← List.append_assoc]
  apply ExecFuncBody.execBlockRevert
  apply execBlock_append (copyStored_prefix hnone hkey hh hg hv)
  have hp : (copyStoredMiddleLocals locals evm word heap).get? "payload" = some (.bytes (attestationPayload evm word)) := store_get_self _ _ _
  have hh' := copyStoredMiddleLocals_heap (locals := locals) (evm := evm) (word := word) (heap := heap)
  exact execBlock_append_term (allocateBlock_revert (copyStoredSize_eval hp) hh' hb) (by intros; simp)

def copyStoredValid (evm : EVM.State) (word : UInt256) (heap : Nat) : Prop :=
  (allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320) ∧
  storedBytesValid (attestationHeader evm word) ∧
  (copyStoredNext heap (attestationPayload evm word) ≤ 2^64-1 ∧
    allocateNext heap 320 ≤ copyStoredNext heap (attestationPayload evm word))

instance (evm : EVM.State) (word : UInt256) (heap : Nat) : Decidable (copyStoredValid evm word heap) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem copyStoredSource_revert {evm : EVM.State} {locals imms : Store} {word : UInt256} {heap : Nat}
    (hnone : locals.get? "_db" = none) (hkey : locals.get? "uid" = some (wordBytes32Value word))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hv : ¬ copyStoredValid evm word heap) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm copyStoredFunction.body .reverted := by
  by_cases hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320
  · by_cases hh' : storedBytesValid (attestationHeader evm word)
    · exact copyStoredSource_revert_payload hnone hkey hh hg hh' (fun hb => hv ⟨hg, hh', hb⟩)
    · exact copyStoredSource_revert_header hnone hkey hh hg hh'
  · exact copyStoredSource_revert_allocate hh hg

def copyStoredArgs (word : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "uid" (wordBytes32Value word)

theorem copyStoredArgs_facts (word : UInt256) (heap : Nat) :
    (copyStoredArgs word heap).get? "_db" = none ∧
    (copyStoredArgs word heap).get? "uid" = some (wordBytes32Value word) ∧
    (copyStoredArgs word heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp only [copyStoredArgs, store_get_self,
    store_get_ne _ _ (by decide : ("uid" == "_db") = false),
    store_get_ne _ _ (by decide : ("uid" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "_db") = false), store_get_empty, and_self]

theorem copyStored_lookup : lookupCallable? contract "_copyStoredAttestation" = some copyStoredFunction.toCallable := by rfl

theorem copyStored_bind (word : UInt256) (heap : Nat) :
    bindParams? copyStoredFunction.params [wordBytes32Value word, .int (Int.ofNat heap)] =
      some (copyStoredArgs word heap) := by rfl

theorem copyStoredCall_ok {evm : EVM.State} {locals imms : Store} {word : UInt256} {heap : Nat}
    {args : List Expr} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [wordBytes32Value word, .int (Int.ofNat heap)])
    (hv : copyStoredValid evm word heap) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_copyStoredAttestation" args retVar)
      (.ok {
        contract := contract
        immutables := imms
        locals := locals.insert retVar
          (.tuple [attestationValue evm word (.bytes (attestationPayload evm word)),
          .int (Int.ofNat (copyStoredNext heap (attestationPayload evm word)))])} evm) := by
  have hf := copyStoredArgs_facts word heap
  exact internalCallFunctionReturn hargs copyStored_lookup (copyStored_bind word heap)
    (copyStoredSource_ok hf.1 hf.2.1 hf.2.2 hv.1 hv.2.1 hv.2.2)

theorem copyStoredCall_revert {evm : EVM.State} {locals imms : Store} {word : UInt256} {heap : Nat}
    {args : List Expr} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [wordBytes32Value word, .int (Int.ofNat heap)])
    (hv : ¬ copyStoredValid evm word heap) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_copyStoredAttestation" args retVar) .reverted := by
  have hf := copyStoredArgs_facts word heap
  exact internalCallFunctionRevert hargs copyStored_lookup (copyStored_bind word heap)
    (copyStoredSource_revert hf.1 hf.2.1 hf.2.2 hv)

end Benchmarks.EAS.EAS

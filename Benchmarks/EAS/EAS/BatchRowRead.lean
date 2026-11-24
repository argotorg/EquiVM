import Benchmarks.EAS.EAS.MultiAttestSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def batchRowLast (requestsName : Ident) : Expr := .binary .eq (.var "i")
  (.cast (.binary .sub (.arrayLength .localVar {base := requestsName}) (.intLit 1)) (.elem (.int abiUInt256Int)))
def batchRowReadLocals (L : Store) (rowName : Ident) (last : Bool) (row : Value) : Store :=
  (L.insert "last" (.bool false)).insert "last" (.bool last) |>.insert rowName row
def batchRowRead (ty : ABIType) (requestsName rowName : Ident) : Body := [
  .letDecl "last" (some (.elem .bool)) (.boolLit false),
  .assign .localVar {base := "last"} (batchRowLast requestsName),
  .letDecl rowName (some ty) (.index (.var requestsName) (.var "i"))]

-- GENERALIZES multiRequestReadSource: retain the array and row variable names as parameters.
theorem batchRowReadSource {L imms : Store} {evm : EVM.State} {requests : List Value}
    {i : Nat} (ty : ABIType) (requestsName rowName : Ident) (hneq : requestsName ≠ "last")
    (hrequests : L.get? requestsName = some (.array requests))
    (hindex : L.get? "i" = some (.int (Int.ofNat i))) (hi : i < requests.length)
    (hlen : requests.length < UInt256.size) (hnorm : normalizeRawBoolWord? requests[i] = .ok requests[i]) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm (batchRowRead ty requestsName rowName)
      (.ok {contract := contract,locals := batchRowReadLocals L rowName (decide (i=requests.length-1)) requests[i],immutables := imms} evm) := by
  let L1 := L.insert "last" (.bool false)
  have hn : (UInt256.ofNat requests.length).toNat = requests.length := ulit_toNat' _ hlen
  have hs : (UInt256.sub (UInt256.ofNat requests.length) (UInt256.ofNat 1)).toNat = requests.length-1 := by
    rw [usub_toNat (by rw [hn]; change 1 ≤ requests.length; omega),hn]
    rfl
  have hi1 : L1.get? "i" = some (.int (Int.ofNat i)) := by simpa (disch := first | decide | exact beq_eq_false_iff_ne.mpr hneq | exact beq_eq_false_iff_ne.mpr (Ne.symm hneq)) only [L1,store_get_ne] using hindex
  have hd1 : L1.get? requestsName = some (.array requests) := by simpa (disch := first | decide | exact beq_eq_false_iff_ne.mpr hneq | exact beq_eq_false_iff_ne.mpr (Ne.symm hneq)) only [L1,store_get_ne] using hrequests
  have he := evalCastUint256Sub (cfg := config) (frame := {contract := contract,locals := L1,immutables := imms}) (evm := evm)
    (a := (.arrayLength .localVar {base := requestsName})) (b := .intLit 1) (x := UInt256.ofNat requests.length) (y := UInt256.ofNat 1)
    (by rw [hn]; exact evalLocalArrayLength hd1) (by simp only [evalExpr?,pure]; rfl)
    (by rw [hn]; change 1 ≤ requests.length; omega)
  have hlast : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm (batchRowLast requestsName) =
      .ok (.bool (decide (i=requests.length-1))) := by
    have hv : (Value.int (Int.ofNat i) == Value.int (Int.ofNat (requests.length-1))) = decide (i=requests.length-1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,Value.int.injEq,Int.ofNat_eq_natCast,Nat.cast_inj,decide_eq_true_eq]
    rw [batchRowLast,evalExpr?,evalLocalValue hi1,he] <;> try decide
    simp only [bind,EvalResult.bind,hs,evalBinaryOp_eq_int_ok,hv]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bool false) (by simp only [evalExpr?,pure]))
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) hlast (assignLocalValue (store_get_self L "last" (.bool false))))
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  apply evalArrayIndex
    (evalLocalValue (by simpa (disch := first | decide | exact beq_eq_false_iff_ne.mpr hneq | exact beq_eq_false_iff_ne.mpr (Ne.symm hneq)) only [store_get_ne] using hd1))
    (evalLocalValue (by simpa (disch := first | decide | exact beq_eq_false_iff_ne.mpr hneq | exact beq_eq_false_iff_ne.mpr (Ne.symm hneq)) only [store_get_ne] using hi1)) hi rfl hnorm


end Benchmarks.EAS.EAS

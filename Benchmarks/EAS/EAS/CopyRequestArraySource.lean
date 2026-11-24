import Benchmarks.EAS.EAS.CopyRequestCall
import Benchmarks.EAS.EAS.ArrayAllocateSource
import Benchmarks.EAS.EAS.ResolveManySource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev copyRequestArrayFunction : FunctionDecl := contract.functions[2]!
def copyRequestArrayLength : Expr := .arrayLength .localVar {base := "data"}
def copyRequestArrayGuard : Expr := .binary .lt (.var "i") copyRequestArrayLength
def copyRequestArrayPrefix : Body := arrayAllocateExprBlock copyRequestArrayLength 32 ++ [resolveManyIndexInit]
def copyRequestArrayCallArgs : List Expr := [.index (.var "data") (.var "i"),.var "$EAS.freeMemory"]
def copyRequestArrayIteration : Body := [
  .internalCall "_copyAttestationData" copyRequestArrayCallArgs "allocation$allocation",
  .letDecl "allocation" none (.tupleGet (.var "allocation$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "allocation$allocation") 1),resolveManyIncrement]
def copyRequestArraySuffix : Body := [.while copyRequestArrayGuard copyRequestArrayIteration] ++ copyRequestReturn

theorem copyRequestArray_body : copyRequestArrayFunction.body = copyRequestArrayPrefix ++ copyRequestArraySuffix := by native_decide

structure CopyRequestArrayLocals (L : Store) (rs : List AttestationRequestRecord) (heap i : Nat) : Prop where
  data : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple))
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  index : L.get? "i" = some (.int (Int.ofNat i))

theorem CopyRequestArrayLocals.next {L : Store} {rs : List AttestationRequestRecord} {heap i next : Nat}
    (h : CopyRequestArrayLocals L rs heap i) :
    CopyRequestArrayLocals ((allocateBlockLocals L next).insert "i" (.int (Int.ofNat (i+1)))) rs next (i+1) := by
  constructor
  · simpa (disch := decide) only [allocateBlockLocals,unpackHeapLocals,store_get_ne] using h.data
  · simp (disch := decide) only [allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
  · exact store_get_self _ _ _

theorem copyRequestArrayGuardSource {L imms : Store} {evm : EVM.State} {rs : List AttestationRequestRecord} {heap i : Nat}
    (h : CopyRequestArrayLocals L rs heap i) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm copyRequestArrayGuard =
      .ok (.bool (decide (i < rs.length))) := by
  have hl := evalLocalArrayLength (cfg := config) (evm := evm) (stele := {contract := contract,locals := L,immutables := imms}) h.data
  simp only [List.length_map] at hl
  simp only [copyRequestArrayGuard,evalExpr?,h.index,hl,EvalResult.ofOption,EvalResult.bind,bind,
    copyRequestArrayLength,evalExpr?,h.data,readLocalPath?,pure,List.length_map,evalBinaryOp_lt_int_ok,
    Int.ofNat_eq_natCast,Nat.cast_lt]

theorem copyRequestArrayCallArgsSource {L imms : Store} {evm : EVM.State} {rs : List AttestationRequestRecord} {heap i : Nat}
    (h : CopyRequestArrayLocals L rs heap i) (hi : i < rs.length) :
    evalExprs? config {contract := contract,locals := L,immutables := imms} evm copyRequestArrayCallArgs =
      .ok [rs[i].tuple,.int (Int.ofNat heap)] := by
  have he := evalArrayIndex (evalLocalValue (cfg := config) (evm := evm) (stele := {contract := contract,locals := L,immutables := imms}) h.data)
    (evalLocalValue h.index) (by simpa only [List.length_map] using hi) (List.getElem_map ..)
    (show normalizeRawBoolWord? rs[i].tuple = .ok rs[i].tuple from rfl)
  simp only [copyRequestArrayCallArgs,evalExprs?,he,evalExpr?,h.heap,EvalResult.ofOption,EvalResult.bind,bind,pure]

theorem copyRequestArrayIterationSource {L imms : Store} {evm : EVM.State} {rs : List AttestationRequestRecord} {heap i : Nat}
    (h : CopyRequestArrayLocals L rs heap i) (hi : i < rs.length) (hlen : rs.length < UInt256.size) :
    (copyRequestValid heap rs[i].data.size →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm copyRequestArrayIteration
        (.ok {contract := contract,locals := (allocateBlockLocals L (copyRequestNext heap rs[i].data.size)).insert "i" (.int (Int.ofNat (i+1))),immutables := imms} evm)) ∧
    (¬ copyRequestValid heap rs[i].data.size →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm copyRequestArrayIteration .reverted) := by
  have hc := copyRequestCall_branches (fork := fork) (retVar := "allocation$allocation") (copyRequestArrayCallArgsSource (imms := imms) (evm := evm) h hi)
  constructor
  · intro hv
    apply ExecBlock.consNormal (hc.1 hv)
    change ExecBlock fork config {contract := contract,locals := L.insert "allocation$allocation" (.tuple [.tuple [],.int (Int.ofNat (copyRequestNext heap rs[i].data.size))]),immutables := imms} evm
      ([.letDecl "allocation" none (.tupleGet (.var "allocation$allocation") 0),
        .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "allocation$allocation") 1)] ++ [resolveManyIncrement]) _
    apply execBlock_append (unpackHeapResult (store_get_self _ _ _)
      (by simpa (disch := decide) only [store_get_ne] using h.heap) (by decide) (by decide))
    apply ExecBlock.consNormal (resolveManyIncrementSource ?_ (by omega)) ExecBlock.nil
    simpa (disch := decide) only [unpackHeapLocals,store_get_ne] using h.index
  · intro hv
    exact ExecBlock.consRevert (hc.2 hv)

theorem copyRequestArrayPrefixSource {L imms : Store} {evm : EVM.State} {rs : List AttestationRequestRecord} {heap : Nat}
    (hd : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    let next := allocateNext heap (32+32*rs.length)
    (rs.length ≤ 2^64-1 ∧ (next ≤ 2^64-1 ∧ heap ≤ next) →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm copyRequestArrayPrefix
        (.ok {contract := contract,locals := (allocateBlockLocals L next).insert "i" (.int 0),immutables := imms} evm) ∧
      CopyRequestArrayLocals ((allocateBlockLocals L next).insert "i" (.int 0)) rs next 0) ∧
    (¬ (rs.length ≤ 2^64-1 ∧ (next ≤ 2^64-1 ∧ heap ≤ next)) →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm copyRequestArrayPrefix .reverted) := by
  dsimp only
  have hl := evalLocalArrayLength (cfg := config) (evm := evm) (stele := {contract := contract,locals := L,immutables := imms}) hd
  simp only [List.length_map] at hl
  have ha := arrayAllocateExprSource (fork := fork) (length := copyRequestArrayLength) hl hh 32
  constructor
  · intro hv
    rw [if_pos hv.1,if_pos hv.2] at ha
    constructor
    · exact execBlock_append ha (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil)
    · constructor
      · simpa (disch := decide) only [allocateBlockLocals,unpackHeapLocals,store_get_ne] using hd
      · simp (disch := decide) only [allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
      · exact store_get_self _ _ _
  · intro hv
    by_cases hn : rs.length ≤ 2^64-1
    · rw [if_pos hn,if_neg (fun h => hv ⟨hn,h⟩)] at ha
      exact execBlock_append_term ha (by intros; exact nofun)
    · rw [if_neg hn] at ha
      exact execBlock_append_term ha (by intros; exact nofun)

def copyRequestArrayArgs (rs : List AttestationRequestRecord) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "data" (.array (rs.map AttestationRequestRecord.tuple))
theorem copyRequestArray_lookup : lookupCallable? contract "_copyAttestationArray" = some copyRequestArrayFunction.toCallable := rfl
theorem copyRequestArray_bind (rs : List AttestationRequestRecord) (heap : Nat) :
    bindParams? copyRequestArrayFunction.params [.array (rs.map AttestationRequestRecord.tuple),.int (Int.ofNat heap)] =
      some (copyRequestArrayArgs rs heap) := rfl

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.NewRecordRunSource
import Benchmarks.EAS.EAS.RequestGuards
import Benchmarks.EAS.EAS.RecordStoreRun
import Benchmarks.EAS.EAS.RefUIDRun
import Benchmarks.EAS.EAS.RecordTailRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

abbrev attestFunction : FunctionDecl := contract.functions[14]!
def attestIteration : Body := match attestFunction.body[26]! with
  | .while _ body => body
  | _ => []
def attestReadRequest : Body := heapResultBlock "_decodeAttestationData"
  [.index (.var "data") (.var "i"),.var "$EAS.freeMemory"] "request$allocation" "request" "$EAS.freeMemory"
def attestRequestLocals (L : Store) (r : AttestationRequestRecord) (heap : Nat) : Store :=
  heapResultLocals L "request$allocation" "request" "$EAS.freeMemory" r.struct heap

theorem attestIteration_eq : attestIteration =
    attestReadRequest ++ readTimeBlock "__c1$allocation" "__c1" ++ attestRequestGuards ++ newRecordBody ++
    [.while (.boolLit true) uidIteration] ++ recordStoreBody ++ [refUIDStmt] ++ recordTailBody := by native_decide

theorem attestReadRequest_source {L imms : Store} {evm : EVM.State} {rs : List AttestationRequestRecord} {i heap : Nat}
    (hd : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple)))
    (hi : L.get? "i" = some (.int (Int.ofNat i))) (hb : i < rs.length)
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestReadRequest
      (.ok {contract := contract,locals := attestRequestLocals L rs[i] heap,immutables := imms} evm) := by
  apply heapResultBlock_ok (decodeAttestationDataCall (r := rs[i]) (heap := heap) ?_) hh (by decide) (by decide) (by decide)
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.index (.var "data") (.var "i")) = .ok rs[i].tuple := by
    have hw : lookupNth? rs i = some rs[i] := by rw [lookupNth_getElem,List.getElem?_eq_getElem hb]
    simp only [evalExpr?,hd,hi,EvalResult.ofOption,EvalResult.bind,bind,pure,evalIndex?,Int.ofNat_eq_natCast,
      Int.natCast_nonneg,List.length_map,Nat.cast_lt,hb,and_self,if_true,Int.toNat_natCast,lookupNth_map,hw,
      Option.map_some,AttestationRequestRecord.tuple,normalizeRawBoolWord?]
  simp only [evalExprs?,he,evalExpr?,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

end Benchmarks.EAS.EAS

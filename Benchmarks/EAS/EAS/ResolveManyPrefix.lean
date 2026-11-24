import Benchmarks.EAS.EAS.ResolveManyLocals
import Benchmarks.EAS.EAS.RecordFieldExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyLengthSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {ats : List AttestationRecord}
    (ha : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value))) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm [resolveManyLength]
      (.ok {contract := contract, locals := locals.insert "length" (.int (Int.ofNat ats.length)), immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  simp only [evalExpr?,readLocalPath?,ha,List.length_map,EvalResult.ofOption,EvalResult.bind,bind,pure,Int.ofNat_eq_natCast]

theorem resolveManySingleGuardSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {len : Nat}
    (hl : locals.get? "length" = some (.int (Int.ofNat len))) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
      (.binary .eq (.var "length") (.intLit 1)) = .ok (.bool (decide (len=1))) := by
  simp only [evalExpr?,hl,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,Value.int.injEq,decide_eq_true_eq,Int.ofNat_eq_natCast]
  omega

theorem resolveManySingleArgsSource {locals imms : Store} {evm : EVM.State} {record : Value} {a : AttestationRecord}
    {value available : UInt256} {rev last : Bool} {heap : Nat}
    (hs : locals.get? "schemaRecord" = some record)
    (ha : locals.get? "attestations" = some (.array [a.value]))
    (hv : locals.get? "values" = some (.array [.int (Int.ofNat value.toNat)]))
    (hr : locals.get? "isRevocation" = some (.bool rev))
    (hav : locals.get? "availableValue" = some (.int (Int.ofNat available.toNat)))
    (hl : locals.get? "last" = some (.bool last))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    evalExprs? config {contract := contract, locals := locals, immutables := imms} evm resolveManySingleArgs =
      .ok [record,a.value,.int (Int.ofNat value.toNat),.bool rev,.int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat heap)] := by
  have hia : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.index (.var "attestations") (.intLit 0)) = .ok a.value := by
    exact evalArrayIndex (i := 0) (xs := [a.value]) (arr := .var "attestations") (idx := .intLit 0) (by simp only [evalExpr?,ha,EvalResult.ofOption])
      (by simp only [evalExpr?]; rfl) (by simp) rfl rfl
  have hiv : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.index (.var "values") (.intLit 0)) = .ok (.int (Int.ofNat value.toNat)) := by
    exact evalArrayIndex (i := 0) (xs := [.int (Int.ofNat value.toNat)]) (arr := .var "values") (idx := .intLit 0) (by simp only [evalExpr?,hv,EvalResult.ofOption])
      (by simp only [evalExpr?]; rfl) (by simp) rfl rfl
  simp only [resolveManySingleArgs,evalExprs?,hia,hiv,evalExpr?,hs,hr,hav,hl,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

def resolveManyLengthLocals (record : Value) (ats : List AttestationRecord) (words : List UInt256) (rev : Bool)
    (available : UInt256) (last : Bool) (heap : Nat) : Store :=
  (resolveManyArgs record ats words rev available last heap).insert "length" (.int (Int.ofNat ats.length))
def resolveManyHeadLocals (record : Value) (ats : List AttestationRecord) (words : List UInt256) (target : AccountAddress)
    (rev : Bool) (available : UInt256) (last : Bool) (heap : Nat) : Store :=
  (resolveManyLengthLocals record ats words rev available last heap).insert "resolver" (.address target)
def resolveManyLoopLocals (record : Value) (ats : List AttestationRecord) (words : List UInt256) (target : AccountAddress)
    (rev : Bool) (available : UInt256) (last : Bool) (heap : Nat) : Store :=
  (resolveManyHeadLocals record ats words target rev available last heap).insert "totalUsedValue" (.int 0) |>.insert "i" (.int 0)

theorem resolveManyLoopLocals_facts (record : Value) (ats : List AttestationRecord) (words : List UInt256) (target : AccountAddress)
    (rev : Bool) (available : UInt256) (last : Bool) (heap : Nat) (hlen : ats.length = words.length) :
    ResolveManyLocals (resolveManyLoopLocals record ats words target rev available last heap)
      ats words target available ⟨0⟩ rev last heap 0 := by
  constructor <;> simp (disch := decide) only [resolveManyLoopLocals,resolveManyHeadLocals,resolveManyLengthLocals,resolveManyArgs,
    store_get_self,store_get_ne,hlen] <;> rfl

theorem resolveManyHeadSource {imms : Store} {evm : EVM.State}
    (record : Value) (ats : List AttestationRecord) (words : List UInt256) (target : AccountAddress)
    (rev : Bool) (available : UInt256) (last : Bool) (heap : Nat)
    (hfield : lookupField? record "resolver" = some (.address target)) (hn : ats.length ≠ 1) :
    ExecBlock fork config {contract := contract, locals := resolveManyArgs record ats words rev available last heap, immutables := imms}
      evm [resolveManyLength,resolveManySingle,resolveManyResolverInit]
      (.ok {contract := contract, locals := resolveManyHeadLocals record ats words target rev available last heap, immutables := imms} evm) := by
  have hl := resolveManyLengthSource (fork := fork) (ats := ats) (cfg := config) (imms := imms) (evm := evm)
    (locals := resolveManyArgs record ats words rev available last heap)
    (by simp (disch := decide) only [resolveManyArgs,store_get_ne,store_get_self])
  apply execBlock_append hl
  have hg := resolveManySingleGuardSource (cfg := config) (imms := imms) (evm := evm) (len := ats.length)
    (locals := resolveManyLengthLocals record ats words rev available last heap) (store_get_self _ _ _)
  apply ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [decide_eq_false hn] using hg) ExecBlock.nil)
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  exact evalRecordField (by simp (disch := decide) only [evalExpr?,resolveManyArgs,store_get_self,store_get_ne,EvalResult.ofOption]) hfield

end Benchmarks.EAS.EAS

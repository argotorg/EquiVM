import Benchmarks.EAS.EAS.SchemaABI

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem decodedSchemaRecord_length {out : ByteArray} {base : Nat} (hv : schemaBodyValid out base) :
    (decodedSchemaRecord out base).schema.size = schemaTextLength out base := by
  have hp := hv.2.2.2.2.2.2
  simp only [decodedSchemaRecord, ByteArray.size_extract]
  omega

def getSchemaDecodeLocals (locals : Store) (record : SchemaRecord) : Store :=
  (locals.insert "record" record.tuple).insert "text" (.bytes record.schema)

theorem getSchemaDecodeSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {out : ByteArray} {record : SchemaRecord}
    (ho : locals.get? "result" = some (.bytes out))
    (hd : cfg.externalABI.decodeValue? schemaRecordABI out = some record.tuple)
    (hl : record.schema.size ≤ 2^64-1) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm getSchemaDecode
      (.ok {contract := contract, locals := getSchemaDecodeLocals locals record, immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := record.tuple) (by
    simp only [evalExpr?, ho, EvalResult.ofOption, EvalResult.bind, bind, hd, pure]))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes record.schema) (by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption, EvalResult.bind, bind, SchemaRecord.tuple, tupleGetValue?, pure]
    rfl))
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  have ht : (Int.ofNat record.schema.size ≤ (18446744073709551615 : Int)) := by
    change record.schema.size ≤ 18446744073709551615 at hl
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [evalExpr?, readLocalPath?, store_get_self, EvalResult.bind, bind, evalBinaryOp?, pure,
    Int.ofNat_eq_natCast]
  have ht' : (record.schema.size : Int) ≤ 2^64-1 := ht
  rw [decide_eq_true ht']

theorem getSchemaDecodeRevert {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {out : ByteArray}
    (ho : locals.get? "result" = some (.bytes out))
    (hd : cfg.externalABI.decodeValue? schemaRecordABI out = none) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm getSchemaDecode .reverted := by
  apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  simp only [evalExpr?, ho, EvalResult.ofOption, EvalResult.bind, bind, hd]

theorem getSchemaReturnSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {record : SchemaRecord} {heap : Nat}
    (hr : locals.get? "record" = some record.tuple)
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm getSchemaReturn
      (.returned {contract := contract, locals := locals, immutables := imms} evm (some [record.value,.int (Int.ofNat heap)])) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, evalStructFields?, SchemaRecord.value, SchemaRecord.tuple, hr, hh,
    EvalResult.ofOption, EvalResult.bind, bind, tupleGetValue?, pure]
  rfl

def schemaCopyHeap (heap : Nat) (out : ByteArray) : Nat := allocateNext heap out.size
def schemaDecodeHeap (heap : Nat) (out : ByteArray) : Nat := allocateNext (schemaCopyHeap heap out) 128
def schemaFinalHeap (heap : Nat) (out : ByteArray) : Nat :=
  allocateNext (schemaDecodeHeap heap out) (bytesAllocation (schemaTextLength out (schemaReturnOffset out)))
def schemaCallValid (heap : Nat) (success : Bool) (out : ByteArray) : Prop :=
  success=true ∧
  (schemaCopyHeap heap out ≤ 2^64-1 ∧ heap ≤ schemaCopyHeap heap out) ∧
  (schemaDecodeHeap heap out ≤ 2^64-1 ∧ schemaCopyHeap heap out ≤ schemaDecodeHeap heap out) ∧
  schemaReturnValid out ∧
  (schemaFinalHeap heap out ≤ 2^64-1 ∧ schemaDecodeHeap heap out ≤ schemaFinalHeap heap out)
instance (heap : Nat) (success : Bool) (out : ByteArray) : Decidable (schemaCallValid heap success out) := by
  unfold schemaCallValid; infer_instance

def getSchemaAllocatedLocals (locals : Store) (heap : Nat) (out : ByteArray) : Store :=
  allocateBlockLocals (allocateBlockLocals locals (schemaCopyHeap heap out)) (schemaDecodeHeap heap out)
def getSchemaFinalLocals (locals : Store) (heap : Nat) (out : ByteArray) : Store :=
  allocateBlockLocals
    (getSchemaDecodeLocals (getSchemaAllocatedLocals locals heap out) (decodedSchemaRecord out (schemaReturnOffset out)))
    (schemaFinalHeap heap out)

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.ResolveManySource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure ResolveManyLocals (locals : Store) (ats : List AttestationRecord) (words : List UInt256)
    (target : AccountAddress) (available total : UInt256) (rev last : Bool) (heap i : Nat) : Prop where
  resolver : locals.get? "resolver" = some (.address target)
  attestations : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value))
  values : locals.get? "values" = some (.array (words.map fun w => .int (Int.ofNat w.toNat)))
  length : locals.get? "length" = some (.int (Int.ofNat words.length))
  index : locals.get? "i" = some (.int (Int.ofNat i))
  available : locals.get? "availableValue" = some (.int (Int.ofNat available.toNat))
  total : locals.get? "totalUsedValue" = some (.int (Int.ofNat total.toNat))
  revocation : locals.get? "isRevocation" = some (.bool rev)
  last : locals.get? "last" = some (.bool last)
  heap : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))

theorem ResolveManyLocals.withValue {locals : Store} {ats : List AttestationRecord} {words : List UInt256}
    {target : AccountAddress} {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) (value : UInt256) :
    ResolveManyLocals (locals.insert "value" (.int (Int.ofNat value.toNat))) ats words target available total rev last heap i := by
  rcases h with ⟨hr,ha,hv,hl,hi,hav,ht,hrv,hlast,hh⟩
  constructor <;> simp (disch := decide) only [store_get_ne] <;> assumption

theorem ResolveManyLocals.payment {locals : Store} {ats : List AttestationRecord} {words : List UInt256}
    {target : AccountAddress} {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) (out : ByteArray) :
    ResolveManyLocals (payableProbeLocals locals out heap) ats words target available total rev last (allocateNext heap 32) i := by
  rcases h with ⟨hr,ha,hv,hl,hi,hav,ht,hrv,hlast,hh⟩
  constructor <;> simp (disch := decide) only [payableProbeLocals,allocateBlockLocals,unpackHeapLocals,
    store_get_self,store_get_ne] <;> assumption

theorem ResolveManyLocals.subtract {locals : Store} {ats : List AttestationRecord} {words : List UInt256}
    {target : AccountAddress} {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) (value : UInt256) :
    ResolveManyLocals (locals.insert "availableValue" (.int (Int.ofNat (UInt256.sub available value).toNat)))
      ats words target (UInt256.sub available value) total rev last heap i := by
  rcases h with ⟨hr,ha,hv,hl,hi,hav,ht,hrv,hlast,hh⟩
  constructor <;> simp (disch := decide) only [store_get_self,store_get_ne] <;> assumption

theorem ResolveManyLocals.add {locals : Store} {ats : List AttestationRecord} {words : List UInt256}
    {target : AccountAddress} {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) (value : UInt256) :
    ResolveManyLocals (locals.insert "totalUsedValue" (.int (Int.ofNat (total+value).toNat)))
      ats words target available (total+value) rev last heap i := by
  rcases h with ⟨hr,ha,hv,hl,hi,hav,ht,hrv,hlast,hh⟩
  constructor <;> simp (disch := decide) only [store_get_self,store_get_ne] <;> assumption

theorem ResolveManyLocals.advance {locals : Store} {ats : List AttestationRecord} {words : List UInt256}
    {target : AccountAddress} {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) :
    ResolveManyLocals (locals.insert "i" (.int (Int.ofNat (i+1)))) ats words target available total rev last heap (i+1) := by
  rcases h with ⟨hr,ha,hv,hl,hi,hav,ht,hrv,hlast,hh⟩
  constructor <;> simp (disch := decide) only [store_get_self,store_get_ne] <;> assumption

theorem resolveManyGuardSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress}
    {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm timeArrayGuard =
      .ok (.bool (decide (i < words.length))) :=
  resolveManyZeroGuardSource ⟨h.values,h.length,h.index,h.heap⟩

theorem resolveManyAccumulateSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {total value : UInt256} {i : Nat}
    (ht : locals.get? "totalUsedValue" = some (.int (Int.ofNat total.toNat)))
    (hv : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) (hb : i+1 < UInt256.size) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm [resolveManyTotalUpdate,resolveManyIncrement]
      (.ok {contract := contract, locals := (locals.insert "totalUsedValue" (.int (Int.ofNat (total+value).toNat))).insert "i" (.int (Int.ofNat (i+1))), immutables := imms} evm) := by
  have he := evalCastUint256Add (cfg := cfg) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) (a := .var "totalUsedValue") (b := .var "value") (x := total.toNat) (y := value.toNat)
    (by simp only [evalExpr?,ht,EvalResult.ofOption]) (by simp only [evalExpr?,hv,EvalResult.ofOption])
  rw [← uadd_toNat] at he
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he (assignLocalBase_ok ht))
  exact ExecBlock.consNormal (resolveManyIncrementSource
    (by simpa (disch := decide) only [store_get_ne] using hi) hb) ExecBlock.nil

end Benchmarks.EAS.EAS

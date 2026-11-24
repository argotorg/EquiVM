import Benchmarks.EAS.EAS.AttestationAlias
import Benchmarks.EAS.EAS.RequireList
import Benchmarks.EAS.EAS.UIDLoopSource
import Benchmarks.EAS.EAS.WordExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def revokeUIDGuard : Expr := .binary .ne (.storage (attestationAliasRef "uid"))
  (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩))
def revokeSchemaGuard : Expr := .binary .eq (.storage (attestationAliasRef "schema")) (.var "schema")
def revokeAttesterGuard : Expr := .binary .eq (.storage (attestationAliasRef "attester")) (.var "revoker")
def revokeRevocableGuard : Expr := .storage (attestationAliasRef "revocable")
def revokeTimeGuard : Expr := .binary .eq (.storage (attestationAliasRef "revocationTime")) (.intLit 0)
def revokeGuards : Body := [.require revokeUIDGuard,.require revokeSchemaGuard,.require revokeAttesterGuard,
  .require revokeRevocableGuard,.require revokeTimeGuard]

def revokeGuardsValid (a : AttestationRecord) (schema : UInt256) (revoker : AccountAddress) : Prop :=
  a.uid ≠ ⟨0⟩ ∧ a.schema = schema ∧ a.attester = revoker ∧ a.revocable = true ∧ a.revocationTime = ⟨0⟩
instance (a : AttestationRecord) (schema : UInt256) (revoker : AccountAddress) : Decidable (revokeGuardsValid a schema revoker) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem revokeGuards_source {L imms : Store} {evm : EVM.State} {word schema : UInt256} {revoker : AccountAddress}
    (ha : L.get? "attestation" = some (.storageRef (attestationER word) attestationType))
    (hs : L.get? "schema" = some (wordBytes32Value schema))
    (hr : L.get? "revoker" = some (.address revoker)) :
    if revokeGuardsValid (storedAttestationRecord evm word) schema revoker then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm revokeGuards
        (.ok {contract := contract,locals := L,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm revokeGuards .reverted := by
  let a := storedAttestationRecord evm word
  have hread (f : ScalarFieldWrite) := attestationAlias_scalar (evm := evm) (imms := imms) (f := f) ha
  have hu : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.storage (attestationAliasRef "uid")) = .ok (wordBytes32Value a.uid) :=
    hread (f := attestationWordWrite "uid" (dbSlot word) a.uid) (by simp only [attestationScalarWrites,List.mem_cons]; tauto)
  have hschema : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.storage (attestationAliasRef "schema")) = .ok (wordBytes32Value a.schema) :=
    hread (f := attestationWordWrite "schema" (dbSlot word+⟨1⟩) a.schema) (by simp only [attestationScalarWrites,List.mem_cons]; tauto)
  have hw : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.storage (attestationAliasRef "attester")) = .ok (.address a.attester) :=
    hread (f := attestationAddressWrite "attester" (dbSlot word+⟨5⟩) a.attester) (by simp only [attestationScalarWrites,List.mem_cons]; tauto)
  have hb : evalExpr? config {contract := contract,locals := L,immutables := imms} evm revokeRevocableGuard = .ok (.bool a.revocable) :=
    hread (f := ⟨"revocable",attestationBoolLoc (dbSlot word+⟨5⟩),.bool a.revocable,a.revocable.toUInt256,rfl,rfl⟩)
      (by simp only [attestationScalarWrites,List.mem_cons]; tauto)
  have ht : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.storage (attestationAliasRef "revocationTime")) = .ok (.int (Int.ofNat a.revocationTime.toNat)) :=
    hread (f := revokeTimeField word a.revocationTime) (by simp only [revokeTimeField,attestationScalarWrites,List.mem_cons]; tauto)
  have heUID : evalExpr? config {contract := contract,locals := L,immutables := imms} evm revokeUIDGuard =
      .ok (.bool (decide (a.uid ≠ ⟨0⟩))) := by
    simp only [revokeUIDGuard,evalExpr?,hu,pure,EvalResult.bind,bind]
    exact evalBytes32Ne a.uid ⟨0⟩
  have heSchema : evalExpr? config {contract := contract,locals := L,immutables := imms} evm revokeSchemaGuard =
      .ok (.bool (decide (a.schema = schema))) := by
    simp only [revokeSchemaGuard,evalExpr?,hschema,hs,EvalResult.ofOption,EvalResult.bind,bind]
    exact evalBytes32Eq a.schema schema
  have heAttester : evalExpr? config {contract := contract,locals := L,immutables := imms} evm revokeAttesterGuard =
      .ok (.bool (decide (a.attester = revoker))) := by
    simp only [revokeAttesterGuard,evalExpr?,hw,hr,EvalResult.ofOption,EvalResult.bind,bind,evalBinaryOp?]
    congr 2
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Value.address.injEq,decide_eq_true_eq]
  have heTime := evalWordEqZero ht
  have h := execRequires (fork := fork) (cfg := config) (frame := {contract := contract,locals := L,immutables := imms}) (evm := evm)
    [(revokeUIDGuard,decide (a.uid ≠ ⟨0⟩)),(revokeSchemaGuard,decide (a.schema = schema)),
      (revokeAttesterGuard,decide (a.attester = revoker)),(revokeRevocableGuard,a.revocable),
      (revokeTimeGuard,decide (a.revocationTime = ⟨0⟩))]
    (by
      intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact heUID
      · exact heSchema
      · exact heAttester
      · exact hb
      · exact heTime)
  simpa only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,
    List.map_cons,List.map_nil,revokeGuardsValid,revokeGuards,a] using h

end Benchmarks.EAS.EAS
